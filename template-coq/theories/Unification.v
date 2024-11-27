(* Distributed under the terms of the MIT license. *)

(** This file defines a unification algorithm inspired by Unicoq :
    "A Unification Algorithm for COQ Featuring Universe Polymorphism and Overloading"
    https://github.com/unicoq

    It is intended for practical use and is not verified 
    (we even disable the guard checker). *)

From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import BasicAst uGraph config.
From MetaCoq.Template Require Import Ast AstUtils Typing Checker Evars Pretty.
Import MCMonadNotation.

Unset Guard Checking.

(** A convenient notation for function application, which saves many parentheses. *)
Notation "f $ x" := (f x) 
  (at level 10, x at level 100, right associativity, only parsing).

(** Right-to-left function composition. *)
Notation "f <<< g" := (fun x => f (g x)) (at level 40, left associativity).

(** Left-to-right function composition. *)
Notation "f >>> g" := (fun x => g (f x)) (at level 40, left associativity).

(** * Controlling unification. *)

(** In the equation [t1 =?= t2] : 
    - [Left] refers to [t1].
    - [Right] refers to [t2].
    - [Both] refers to [t1] and [t2]. *)
Inductive side := Left | Right | Both.

Module Side.

Definition t := side.

(** Swap sides. [Both] is mapped to [Both]. *)
Definition swap (s : t) : t :=
  match s with 
  | Left => Right 
  | Right => Left 
  | Both => Both
  end.

(** [Side.leq s s'] checks if [s] is "smaller" then [s']. 
    Any side is smaller than [Both]. *)
Definition leq (s s' : t) : bool :=
  match s, s' with 
  | _, Both => true 
  | Left, Left => true 
  | Right, Right => true 
  | _, _ => false
  end.
  
End Side.

(** The algorithm uses directions in addition to sides. 
    In the equation [t1 =?= t2] :
    - [Original] is the direction [t1] -> [t2].
    - [Swapped] is the direction [t2] -> [t1]. *)
Inductive direction := Original | Swapped.

(** Unification flags control the behaviour of the unification algorithm. *)
(* TODO : documententation. *)
Module UnifFlags.
Record t := mk
  { beta_reduce_type : bool
  ; unify_types : bool 
  ; aggressive : bool
  ; super_aggressive : bool 
  ; try_solving_eqn : bool 
  ; (** On which side(s) is it allowed to reduce ? *)
    reduce_side : Side.t
  ; (** On which side(s) is it allowed to instantiate evars ? *)
    inst_side : Side.t 
  ; (** Which evars are allowed to be instantiated ? 
        If [None] than all evars are instantiable. *)
    inst_evars : option ESet.t }.

(** Reasonable default flags. *)
Definition default := mk true true true false true Both Both None.
End UnifFlags.

(** * Unification errors. *)

(* TODO : document this. *)
Inductive unif_error := 
  | NotSameHead : unif_error
  | NotSameArgSize : unif_error
  | OccurCheck : evar -> term -> unif_error
  | UnivInconsistency : unif_error
  | CannotReduce : unif_error
  | InternalError : doc unit -> unif_error.

(** Unification returns a [unif_result]. *)
Inductive unif_result A : Type := 
  (** [Success x] : unification succeeded with result [x] (typically the updated evar map). *)
  | Success : A -> unif_result A
  (** [UnifError err] : unification failed with error [err]. *)
  | UnifError : unif_error -> unif_result A.
Arguments Success {A}%_type_scope a.
Arguments UnifError {A}%_type_scope error.

(** * Logging. *)

(** We define logging functions specially tailored to unification. *)
Module Log.

(** A [Log.node] contains all the log data pertaining to a single unification problem. *)
Record node t := mknode
  { (** The initial evar map. *)
    evm : EvarMap.t 
  ; (** The local context. *)
    ctx : context
  ; (** The type of conversion problem. *)
    pb : conv_pb 
  ; (** The first term we are unifying. *)
    t1 : term 
  ; (** The second term we are unifying. *)
    t2 : term 
  ; (** A list of subproblems or messages, ordered from last to first. *)
    elements : t
  ; (** The result of unification. *)
    res : unif_result EvarMap.t }.

Arguments evm {t}.
Arguments ctx {t}.
Arguments pb {t}.
Arguments t1 {t}.
Arguments t2 {t}.
Arguments elements {t}.
Arguments res {t}.

(** A log contains a list of unification problems and messages. *)
Inductive t := Log : list (node t + doc unit) -> t.

(** Helper function to unwrap a log. *)
Definition unLog (log : t) : list (node t + doc unit) :=
  match log with Log elems => elems end.

(** The empty log. *)
Definition empty : t := Log [].

(** Append logs. *)
Definition append (l l' : t) : t := Log (unLog l ++ unLog l').

Section Printing.
Context `{PrettyFlags.t} (env : global_env) (verbose : bool).

Fixpoint print_elem (elem : node t + doc unit) {struct elem} : doc unit :=
  match elem with 
  | inl n => str "> " ^^ print_node n tt
  | inr d => str "- " ^^ group $ align $ d
  end
  
with print_node (n : node t) (u : unit) {struct u} : doc unit :=
  (* TODO : print the evar map and context if verbose. *)
  (* Print the unification equation. *)
  let names := List.map (string_of_name <<< binder_name <<< decl_name) n.(ctx) in
  let t1 := print_term (env, Monomorphic_ctx) names n.(t1) in
  let t2 := print_term (env, Monomorphic_ctx) names n.(t2) in
  let op := match n.(pb) with Conv => str "=?=" | Cumul => str "<?=" end in
  let equation := group $ align $ t1 ^/^ op ^/^ t2 in
  (* Print the children elements. *)
  let elements := List.map print_elem $ unLog n.(elements) in
  (* Print the result. *)
  let res :=
    match n.(res) with 
    | Success _ => str "[success]"
    | UnifError _ => str "[error]"
    end 
  in
  (* Assemble everything. *)
  group $ align $ separate hardline (equation :: elements ++ [res]).

(** Pretty-print a log. The [verbose] flag controls whether we should print
    the evar maps and local contexts. *)
Definition print (log : t) : doc unit :=
  group $ align $ separate_map hardline print_elem $ unLog log.

End Printing.

End Log.

(** * Unification monad. *)

(** Unification works in a monad [M], which can :
    - read some unification parameters.
    - fail with a [unif_error].
    - log data to a [Log.t]. *)
Definition M A := UnifFlags.t -> Log.t * unif_result A. 

(** Monadic return. *)
Definition retM {A} (a : A) : M A := fun _ => (Log.empty, Success a).

(** Monadic fail. *)
Definition failM {A} (err : unif_error) : M A :=
  fun _ => (Log.empty, UnifError err).

(** Monadic bind. *)
Definition bindM {A} {B} (ma : M A) (mf : A -> M B) : M B :=
  fun flags =>
    match ma flags with 
    | (l, Success a) => let (l', res) := mf a flags in (Log.append l l', res)
    | (l, UnifError err) => (l, UnifError err)
    end.
Notation "'let*' x := c1 'in' c2" := (bindM c1 (fun x => c2))
  (at level 100, x pattern, c1 at next level, right associativity).

(** Monad instance for [M]. To avoid typeclass errors, I prefer using [retM] and [let*] 
    instead of [ret] and [mlet]. *)
Instance monad_M : Monad M :=
{ ret _ := retM ; bind _ _ := bindM }.

(** Monadic alternative. *)
Definition orM {A} (mx my : M A) : M A :=
  fun flags =>
    match mx flags with 
    | (l, Success x) => (l, Success x)
    | (l, UnifError _) => let (l', y) := my flags in (Log.append l l', y)
    end.
Notation "x <|> y" := (orM x y) (at level 85, right associativity).
   
(** [whenM cond x] executes [x] if [cond] is true, and otherwise does nothing. *)
Definition whenM (cond : bool) (x : M unit) : M unit :=
  if cond then x else retM tt.

(** [liftM x err] lifts a value from the [option] monad to [M].
    [None] is mapped to [UnifError err]. *)
Definition liftM {A} (x : option A) (err : unif_error) : M A :=
  match x with 
  | Some x => retM x
  | None => failM err
  end.

(** Log a (primitive) string. *)
Definition log_str (s : string) : M unit :=
  fun _ => (Log.Log [inr $ str s], Success tt).

(** Log a document. *)
Definition log_doc (d : doc unit) : M unit :=
  fun _ => (Log.Log [inr d], Success tt).

(** Log a unification (sub)problem. It collects the logs of [problem],
    packages them in a [Log.node], and returns the same [unif_result] as [problem].  *)
Definition log_problem Γ pb t t' evm (problem : M EvarMap.t) : M EvarMap.t :=
  fun flags =>
    let (elements, res) := problem flags in 
    let node := Log.mknode _ evm Γ pb t t' elements res in
    (Log.Log [inl node], res).  

(** Get the unification flags. *)
Definition get_flags : M UnifFlags.t :=
  fun flags => (Log.empty, Success flags).

(** [with_flags flags x] runs the computation [x] with unification flags
    set to [flags]. *)
Definition with_flags {A} (flags : UnifFlags.t) (x : M A) : M A :=
  fun _ => x flags.

(** * Unification algorithm. *)

(** [allowed_inst flags ev side] checks if we are allowed to instantiate evar [ev]. 
    [side] is the side(s) on which the evar occurs. *)
Definition allowed_inst (flags : UnifFlags.t) (ev : evar) (s : Side.t) : bool :=
  (* Check the evar is in the instantiable set. *)
  option_default (ESet.mem ev) (UnifFlags.inst_evars flags) true &&
  (* Check the evar is on the correct side. *)
  Side.leq s (UnifFlags.inst_side flags).

(** [is_evar evm t] checks if [t] is an evar. *)
Definition is_evar evm t : bool :=
  match whd_evars evm t with 
  | tEvar _ _ => true 
  | _ => false 
  end.

Fixpoint ise_list2 {A B} (f : A -> B -> EvarMap.t -> M EvarMap.t) 
  (xs : list A) (ys : list B) (evm : EvarMap.t) : M EvarMap.t :=
  match xs, ys with 
  | [], [] => retM evm 
  | x :: xs, y :: ys =>
    let* evm := f x y evm in ise_list2 f xs ys evm
  | _, _ => failM NotSameHead
  end.

(** [rebuild_case env ci pred bs] rebuilds the terms corresponding to the 
    case predicate and branches of [tCase ci pred _ bs]. 
    This involves adding lambda abstractions and let-ins as needed. *)
Definition rebuild_case Σ ci pred bs : option (term * list term) :=
  match lookup_inductive Σ ci.(ci_ind) with 
  | None => None 
  | Some (mbody, body) =>
    (* Add abstractions to the predicate. *)
    let pred_ctx := case_predicate_context ci.(ci_ind) mbody body pred in
    let pred_term := it_mkLambda_or_LetIn pred_ctx pred.(preturn) in 
    (* Add abstractions to each branch. *)
    let bs_terms := 
      map2 
        (fun b cbody =>
          let b_ctx := case_branch_context ci.(ci_ind) mbody cbody pred b in
          it_mkLambda_or_LetIn b_ctx b.(bbody))
        bs
        body.(ind_ctors)
    in
    (* Return the updated predicate and branches. *)
    Some (pred_term, bs_terms)
  end.

(** [find_unique cond xs] checks if there is exactly one element in [xs] that satisfies
    the condition [cond], and if so returns its index. *)
Definition find_unique {A} (cond : A -> bool) (xs : list A) : option nat :=
  (* Loop over elements of [xs] from first to last. 
     - [i] is the index of the current element.
     - [res] is [None] if we have not yet found an element satisfying [cond],
       otherwise it is [Some idx] where [idx] is the position of the element. *)
  let fix loop res i xs :=
    match xs with 
    | [] => res 
    | x :: xs =>
      if cond x then 
        match res with 
        (* We found a first element satisfying [cond]. *)
        | None => loop (Some i) (S i) xs 
        (* We found two elements satisfying [cond] : return [None]. *)
        | Some _ => None 
        end
      else loop res (S i) xs
    end 
  in 
  loop None 0 xs.
  
(** Specialization of [find_unique] to named variables (tVars). *)
Definition find_unique_var evm (id : ident) (ts : list term) :=
  find_unique 
    (fun t => match whd_evars evm t with tVar id' => id == id' | _ => false end) 
    ts.

(** Specialization of [find_unique] to de Bruijn variables (tRels). *)
Definition find_unique_rel evm (n : nat) (ts : list term) :=
  find_unique 
    (fun t => match whd_evars evm t with tRel n' => n == n' | _ => false end) 
    ts.

(** [evar_occurs evm ev t] checks if evar [ev] occurs in term [t]. *)
Fixpoint evar_occurs (evm : EvarMap.t) (ev : evar) (t : term) : bool :=
  match whd_evars evm t with 
  | tEvar ev' _ => if ev == ev' then true else false 
  | t => fold_term (fun acc subt => acc || evar_occurs evm ev subt) false t
  end.

(** [term_fvars evm t] computes the set of free variables (tVars) in the term [t]. *)
Definition term_fvars (evm : EvarMap.t) (t : term) : IdentSet.t := 
  let fix aux acc t :=
    match whd_evars evm t with 
    | tVar v => IdentSet.add v acc 
    | t => fold_term aux acc t 
    end 
  in 
  aux IdentSet.empty t.

(** [has_free_var evm vars t] checks if [t] has a free variable which is in [vars]. *)
Definition has_free_var (evm : EvarMap.t) (vars : list ident) (t : term) : bool :=
  let fvars := term_fvars evm t in 
  List.existsb (fun v => IdentSet.mem v fvars) vars.

(** [remove_with_deps evm nctx pos] removes the declarations at positions [pos] in named context [nctx].
    Declarations which depend on removed ones are removed as well. *)
Definition remove_with_deps (evm : EvarMap.t) (nctx : named_context) (pos : list nat) : named_context :=
  (* We process declarations in [nctx] from last to first (i.e. outermost to innermost).
     - [i] is the index of the current declaration.
     - [removed] contains the identifiers of the variables which were removed so far. *)
  let fix loop i nctx removed :=
    match nctx with
    | [] => []
    | (id, d) :: nctx =>
      if List.existsb (eqb i) pos
         || has_free_var evm removed d.(decl_type) 
         || option_default (has_free_var evm removed) d.(decl_body) false
      (* Remove [d]. *)
      then loop (pred i) nctx (id :: removed)
      (* Keep [d]. *)
      else (id, d) :: loop (pred i) nctx removed
    end
  in
  rev $ loop (pred #|nctx|) (rev nctx) [].

Module Invert.

(** We need a state-option monad in this section. *)
Local Definition M A := EMap.t (list nat) -> option (EMap.t (list nat) * A).

#[local] Instance : Monad M :=
{ 
  ret _ a s := Some (s, a) ;
  bind _ _ ma mf s := 
    match ma s with 
    | None => None
    | Some (s, a) => mf a s
    end
}.

(** Monadic alternative. *)
Definition msum {A} (mx my : M A) : M A :=
  fun s =>
  match mx s with 
  | None => my s 
  | Some (s, x) => Some (s, x)
  end.
#[local] Notation "x <|> y" := (msum x y) 
  (at level 85, right associativity).
   
Local Definition fail {A} : M A := fun s => None.
  
Definition invert (evm : EvarMap.t) (map : EMap.t (list nat)) (nctx : named_context) 
  (ev0 : evar) (subs : list term) (args : list term) (t : term) : option (EMap.t (list nat) * term) :=
  let subs_args := subs ++ args in
  let var_or_rel depth k :=
    if k <? #|subs| 
    then option_map (tVar <<< fst) $ List.nth_error nctx k
    else Some $ tRel $ #|subs_args| - k - 1 + depth
  in 
  let fix invert_aux (inside_evar : bool) (depth : nat) (t : term) : M term :=
    match whd_evars evm t with
    | tVar id =>
      match var_or_rel depth =<< find_unique_var evm id subs_args with
      | None => fail 
      | Some t => ret t
      end
    | tRel j =>
      if depth <? j then 
        match var_or_rel depth =<< find_unique_rel evm (j - depth) subs_args with 
        | None => fail 
        | Some t => ret t
        end
      else ret $ tRel j
    | tEvar ev args =>
      if ev == ev0 then fail else 
	  (*let evargs' := Evd.expand_existential sigma (ev', evargs') in*)
	  let on_arg arg_idx arg := 
        (* First try to invert the argument. *)
        invert_aux true depth arg <|>
        (* We could not invert this argument : we have to prune it. *)
		(* Pruning can not happen inside an evar's suspended substitution. *)
        if inside_evar then fail else 
        (* Extend the pruning map : we have to prune the declaration 
           at position [arg_idx] of evar [ev]. *)
        (fun map => 
		  let prev_idxs := option_get [] (EMap.find ev map) in
          let map := EMap.add ev (arg_idx :: prev_idxs) map in 
          Some (map, arg))
	  in
      (* Invert each argument. *)
      mlet args <- monad_map_i on_arg args ;;
      ret $ tEvar ev args
	| t =>
      map_term_with_bindersM depth (fun _ depth => ret $ S depth) (invert_aux inside_evar) t
    end
  in
  invert_aux false 0 t map.

End Invert.

Section Algorithm.
Context `{PrettyFlags.t} `{checker_flags} (Σ : global_env) (Δ : named_context).

Implicit Types (Γ : context) (up : UnifFlags.t) (pb : conv_pb).
Existing Instance default_fuel.

(** [type_of evm Δ Γ t] computes the type of term [t] in named context [Δ] and local context [Γ].
    It assumes that [t] is well-typed. *)
Definition type_of (evm : EvarMap.t) (Δ : named_context) (Γ : context) (t : term) : M term :=
  (* TODO : actually use retyping. *)
  (* TODO : integrate evar map handling in [Checker] and get rid of [nf_evars]. *)
  match Checker.infer Σ (EvarMap.evm_universes evm) Δ Γ $ nf_evars evm t with 
  | Checked ty => retM ty 
  | TypeError err => 
    let msg := align $ group $
      str "The term" ^/^ 
      print_term (Σ, Monomorphic_ctx) (context_names Γ) (nf_evars evm t) ^/^
      str "is ill-typed." 
    in
    failM $ InternalError msg
  end.

(** [invert evm map nctx ev subs args t] inverts the equation [?ev[subst] args := t]
    (where [nctx] is the named context of the evar, thus #|nctx| = #|subs|).
    
    More precisely it builds a term t' equal to t, except that every free variable 
    (tVar or tRel) x in t is replaced by :
    - if x appears does not appear _uniquely_ in [subs ++ args], then we fail.
    - if x appears in [subs] at index [i], then x is replaced by [tVar n]
      where [n] is the name of the variable in [nctx] at index [i].
    - If x appears in [args] at index [i] (starting from the end), 
      then x is replaced by [tRel i].
    It fails if [ev] appears inside [t]. 
    
    This function implements a heuristic which helps in some cases : it tries to 
    prune evars appearing in [t] (see also the [prune] function). 
    [map] is the initial pruning map (which assign to every evar a list of argument
    positions to prune), which [invert] extends as needed. *)
Definition invert evm map nctx ev subs args t : M (EMap.t (list nat) * term) :=
  liftM 
    (Invert.invert evm map nctx ev subs args t)
    (InternalError $ align $ group $ 
      str "Failed to invert the term" ^/^
      print_term (Σ, Monomorphic_ctx) [] t).

(** [invert_lambdas evm map nctx ev subst args body] computes the term 
    [fun x1 : A1{subs}^-1 => ... => fun xn : An{subs}^-1 => body], where :
    - [ev] is an evar with named context [nctx].
    - [subs] is a suspended substitution compatible with [nctx] (thus #|subs| = #|nctx|).
    - [args] = [x1 ... xn] are the arguments of the evar.
    - [body] is a term with free de Bruijn indices (tRels) [0 ... n-1].
    - Each [xi] has type [Ai].

    See [invert] for an explanation of [map].
*)
Definition invert_lambdas (evm : EvarMap.t) (Γ : context) (map : EMap.t (list nat)) 
  (nctx : named_context) (ev : evar) (subs args : list term) (body : term) : M (EMap.t (list nat) * term) :=
  (* We process the arguments from last to first. *)
  let fix loop (acc : EMap.t (list nat) * term) args : M (EMap.t (list nat) * term) :=
    match args with 
    | [] => retM acc 
    | arg :: args => 
      let (map, body) := acc in
      let* ty := type_of evm Δ Γ arg in
      let* (map, ty) := invert evm map nctx ev subs (rev args) ty in
      (* TODO : choose a fresh name. *)
      let name := "x" ^ string_of_nat #|args| in
      let binder := {| binder_name := nNamed name ; binder_relevance := Relevant |} in
      loop (map, tLambda binder ty body) args
    end 
  in 
  loop (map, body) $ rev args.
      
(** [prune evm ev pos] prunes the declarations at positions [pos] in the context of the evar [ev].
    More precisely :
    - if [ev] is defined in [evm] it does nothing.
    - if [ev] is undefined in [evm], it assigns [ev := ev'] where [ev'] has the same conclusion
      as [ev] but lives in a context which has been pruned. 
    It returns [None] if prunning failed. *)
Fixpoint prune (evm : EvarMap.t) (ev : nat) (pos : list nat) {struct ev} : M EvarMap.t :=
  if EvarMap.is_defined evm ev then retM evm else
  let* entry := liftM (EvarMap.lookup evm ev) 
    (InternalError $ group $ align $ str "Undefined evar #" ^^ nat10 ev) 
  in
  (* Remove the required positions from the local context of the evar. *)
  let new_ctx := remove_with_deps evm entry.(ev_nctx) pos in 
  (* Make sure the conclusion of the evar does not contain any removed variables.
     This might require pruning other evars which appear in the conclusion. *)
  let concl := entry.(ev_concl) in
  let new_ctx_vars := List.map (tVar <<< fst) new_ctx in
  let* (map, _) := invert evm (EMap.empty (list nat)) new_ctx ev new_ctx_vars [] concl in
  (* Prune other evars as needed. *)
  let* evm := prune_all evm map tt in
  (* Create a fresh evar [ev'] in the new context. *)
  let (evm, ev') := EvarMap.fresh_evar evm entry.(ev_name) new_ctx concl in
  (* Assign [ev := ev']. *)
  retM $ EvarMap.define evm ev' (tEvar ev new_ctx_vars)

(** [prune_all evm map tt] prunes all the evars in [evm] according to [map].
    Unfortunately for technical reasons we have to pass a useless [tt] argument to [prune_all]. *)
with prune_all (evm : EvarMap.t) (map : EMap.t (list nat)) (dummy : unit) {struct dummy} : M EvarMap.t :=
  monad_fold_left (fun evm '(ev, pos) => prune evm ev pos) (EMap.elements map) evm. 

(** [intersect flags evm xs ys] computes the list of positions where the terms in [xs] and [ys] 
    are not equal. By default only disagreements on positions where both are variables 
    (tVar or tRel) are accepted, and we return None otherwse.
    The flag [UnifFlag.aggressive] bypasses this behaviour, making [intersect] always succeed. *)
Definition intersect (flags : UnifFlags.t) evm (xs ys : list term) : option (list nat) :=
  let is_var t := 
    match whd_evars evm t with tVar _ | tRel _ => true | _ => false end 
  in  
  let fix loop i xs ys diff :=
    match xs, ys with 
    | [], [] => Some diff
    | x :: xs, y :: ys =>
      (* TODO : push evar handling in [eq_term]. *)
      if eq_term (EvarMap.evm_universes evm) (nf_evars evm x) (nf_evars evm y) then loop (S i) xs ys diff 
      else if is_var x && is_var y then loop (S i) xs ys (i :: diff)
      else if UnifFlags.aggressive flags then loop (S i) xs ys (i :: diff)
      else None
    | _, _ => None 
    end 
  in 
  loop 0 xs ys [].
          
(** [meta_same evm ev subs1 subs2] implements the Meta-Same rule to unify [ev[subs1] =?= ev[subs2]]. *)
(* TODO : better unif_errors. *)
Definition meta_same evm (ev : evar) (subs1 subs2 : list term) : M EvarMap.t :=
  (* Check if the evar can be instantiated. *)
  let* flags := get_flags in
  if allowed_inst flags ev Both then 
    (* Prune the evar on the positions where [subs1] and [subs2] disagree. *)
    match intersect flags evm subs1 subs2 with
    | Some [] => 
      (* Fast path to avoid pruning if unnecessary. *) 
      retM evm
    | Some pos => prune evm ev pos
    | None => failM $ InternalError $ str "TODO"
    end
  else failM $ InternalError $ str "TODO".

(** Helper function used to implement [meta_inst]. 
    It inverts the equation [ev[subs] args =?= t] and returns :
    - the updated evar map (after pruning).
    - the term [t'] that [ev] will get instantiated with, which lives in the local context of [ev]. *)
Definition meta_inst_solution Γ (ev : evar) (subs args : list term) (t : term) evm  : M (EvarMap.t * term) :=
  (* TODO : remove equal tails. *)
  (* TODO : beta-reduce to remove dependencies. *)
  let* entry := liftM (EvarMap.lookup evm ev) (InternalError $ str "Undefined evar #" ^^ nat10 ev) in
  let* (map, t0) := invert evm (EMap.empty (list nat)) entry.(ev_nctx) ev subs args t in
  let* (map, t1) := invert_lambdas evm Γ map entry.(ev_nctx) ev subs args t0 in
  (* Prune the evar map as required by [map]. *)
  let* evm := prune_all evm map tt in
  (* TODO : refresh universes. *)
  retM (evm, t1).

(** [unfold_def Γ t evm] gets the definition of a local variable or constant. *)
Definition unfold_def Γ t evm : option term :=
  match whd_evars evm t with 
  | tRel n => 
    match decl_body =<< List.nth_error Γ n with 
    | Some body => Some $ lift0 (S n) body
    | _ => None 
    end 
  | tVar id => decl_body =<< lookup_nctx Δ id
  | tConst c uinst =>
    match cst_body =<< lookup_constant Σ c with 
    | Some body => 
      (* TODO : substitute the instance. *)
      Some body
    | None => None 
    end
  | _ => None 
  end.

(** [tapp f args] represents the application of a term [f] to arguments [args].
    The list of arguments can be empty. *)
Definition tapp := term * list term.

(** [whd_tapp evm t] expands evars and removes casts in the head of [t]. *)
Fixpoint whd_tapp evm (t : tapp) {struct t} : tapp :=
  let (f, args) := t in
  match whd_evars evm f with 
  | tApp f' args' => whd_tapp evm (f', args' ++ args)
  | tCast f' _ _ => whd_tapp evm (f', args)
  | f' => (f', args)
  end.

(** * Main unification loop. *)

(** [unify] unifies two terms : it is the main entry point of the algorithm.
    It is a simple wrapper around [unify_tapp]. *)
Fixpoint unify Γ pb (t t' : term) evm {struct pb} : M EvarMap.t :=
  unify_tapp Γ pb (t, []) (t', []) evm

(** [unify_tapp] unifies two [tapp]s [t] and [t']. Note that [t] and [t'] are not 
    required to be in whd_tapp form. *)
with unify_tapp Γ pb (t t' : tapp) evm {struct pb} : M EvarMap.t :=
  log_problem Γ pb (tApp t.1 t.2) (tApp t'.1 t'.2) evm $
  let t := whd_tapp evm t in 
  let t' := whd_tapp evm t' in 
  if is_evar evm t.1 || is_evar evm t'.1 then 
    try_instantiate Γ pb t t' evm
  else 
    try_app_fo Γ pb t t' evm <|>
    try_reduce Γ pb t t' evm

(** [try_instantiate] is called when either [t] or [t'] is an evar (possible applied
    to a suspended subsitution and arguments), and tries to apply rules which instantiate evars. *)
with try_instantiate Γ pb t t' evm {struct pb} : M EvarMap.t :=
  let t := whd_tapp evm t in 
  let t' := whd_tapp evm t' in
  match t.1, t'.1 with 
  | tEvar ev subs, tEvar ev' subs' => 
    if ev == ev' 
    (* Meta-Same *)
    then 
      let* _ := log_str "Meta-Same" in
      let* evm := meta_same evm ev subs subs' in 
      ise_list2 (unify Γ Conv) t.2 t'.2 evm
    (* Meta-Meta *)
    else
      let* _ := log_str "Meta-Meta" in
      (* We try both directions, but first the one with the longest substitution. *)
      let '(dir1, dir2, ev1, ev2, subs1, subs2, args1, args2, t1, t2) := 
        if #|subs| <? #|subs'|
        then (Swapped, Original, ev', ev, subs', subs, t'.2, t.2, t, t')
        else (Original, Swapped, ev, ev', subs, subs', t.2, t'.2, t', t)
      in 
      meta_inst dir1 Γ pb ev1 subs1 args1 t1 evm <|> 
      meta_inst dir2 Γ pb ev2 subs2 args2 t2 evm
  (* Meta-InstL *)
  | tEvar ev subs, _ => 
    let* _ := log_str "Meta-InstL" in
    meta_inst Original Γ pb ev subs t.2 t' evm
  (* Meta-InstR *)
  | _, tEvar ev' subs' => 
    let* _ := log_str "Meta-InstR" in
    meta_inst Swapped Γ pb ev' subs' t'.2 t evm
  | _, _ => failM $ InternalError $ str "try_instantiate : expected an evar"
  end

(** [meta_inst dir Γ pb ev subs t evm] implements the Meta-Inst rule to instantiate [ev[subs] args := t].
    [dir] is [Original] if [ev] is on the left-hand side, and [Swapped] if [ev] is on the right-hand side. *)
(* TODO : better unif_errors. *)
with meta_inst dir Γ pb ev subs args (t : tapp) evm {struct pb} : M EvarMap.t :=
  (* TODO : allow reduction and instantitation in all subproblems. *)
  (*let flags := UnifFlags.mk  Both Both (UnifFlags.inst_evars up) in
  with_flags flags $*)
  let* flags := get_flags in
  (* Beta-reduce [t] if the relevant flag is set. *)
  (* TODO *)
  let t := tApp t.1 t.2 in
  let is_var t := 
    match whd_evars evm t with tVar _ | tRel _ => true | _ => false end 
  in
  (* Check the evar is instantiable and that the substitution and arguments contain 
     only variables (tVars and tRels). *)
  let side := match dir with Original => Left | Swapped => Right end in
  if allowed_inst flags ev side && List.forallb is_var (subs ++ args) then 
    (* Compute the solution [sol]. *)
    let* (evm, sol) := meta_inst_solution Γ ev subs args t evm in
    let* _ := log_doc $ str "solution :" ^+^ 
      print_term (Σ, Monomorphic_ctx) [] sol 
    in
    (* Unify the type of the evar with the type of the solution (if the relevant flag is set). *)
    let* evm :=
      if UnifFlags.unify_types flags
      then 
        let* entry := liftM (EvarMap.lookup evm ev) (InternalError $ str "Undefined evar #" ^^ nat10 ev) in
        let* sol_ty := type_of evm entry.(ev_nctx) [] sol in
        let ev_ty := instantiate_evar entry.(ev_nctx) subs entry.(ev_concl) in
        unify Γ Cumul sol_ty ev_ty evm
      else retM evm
    in 
    (* Check the evar does not occur in the solution. *)
    if evar_occurs evm ev sol then failM $ OccurCheck ev sol else 
    (* Finally define the evar. *)
    retM $ EvarMap.define evm ev sol
  else failM NotSameHead

(** [try_app_fo] tries to structurally unify the two sides of the equation. *)
with try_app_fo Γ pb (t t' : tapp) evm {struct pb} : M EvarMap.t :=
  let* _ := log_str "App-FO" in
  let (f, args) := whd_tapp evm t in 
  let (f', args') := whd_tapp evm t' in
  if #|args| == #|args'| then 
    (* Unify the heads. *)
    let* evm := unify_head Γ pb f f' evm in 
    (* Unify the arguments. *)
    ise_list2 (unify Γ Conv) args args' evm
  else 
    failM NotSameArgSize

with unify_head Γ pb t t' evm {struct pb} : M EvarMap.t :=
  match whd_evars evm t, whd_evars evm t' with 
  (* Type-Same *)
  | tSort s, tSort s' =>
    (* Enforce the new universe constraints. *)
    let evm :=
      match pb with 
      | Conv => EvarMap.set_eq_sort evm s s' 
      | Cumul => EvarMap.set_eq_sort evm s s'
      end
    in 
    (* Check the universe graph is still consistent. *)
    match evm with
    | Some evm => retM evm 
    | None => failM UnivInconsistency
    end
  (* Lam-Same *)
  | tLambda x ty body, tLambda _ ty' body' =>
    let* evm := unify Γ Conv ty ty' evm in 
    unify (Γ ,, vass x ty) pb body body' evm
  (* Prod-Same *)
  | tProd x a b, tProd _ a' b' =>
    let* evm := unify Γ Conv a a' evm in 
    unify (Γ ,, vass x a) pb b b' evm
  (* Let-Same *)
  | tLetIn x def ty body, tLetIn _ def' ty' body' =>
    let* evm := unify Γ Conv def def' evm in
    unify (Γ ,, vdef x def ty) pb body body' evm
  (* Rigid-Same *)
  | tRel n, tRel n' => 
    if n == n' then retM evm else failM NotSameHead
  | tVar v, tVar v' => 
    if v == v' then retM evm else failM NotSameHead
  | tConst c _, tConst c' _ =>
    if c == c' then retM evm else failM NotSameHead
  | tInd ind _, tInd ind' _ =>
    if ind == ind' then retM evm else failM NotSameHead
  | tConstruct ind n _, tConstruct ind' n' _ =>
    if (ind == ind') && (n == n') then retM evm else failM NotSameHead  
  | tProj p t, tProj p' t' =>
    if p == p' then unify Γ Conv t t' evm else failM NotSameHead
  | tFix defs n, tFix defs' n'
  | tCoFix defs n, tCoFix defs' n' =>
    if n == n' then 
      (* First unify the types. *)
      let* evm := ise_list2 (unify Γ Conv) (List.map dtype defs) (List.map dtype defs') evm in
      (* Then unify the bodies in an extended context. *)
      ise_list2 (unify (Γ ,,, fix_context defs) Conv) (List.map dbody defs) (List.map dbody defs') evm
    else failM NotSameHead
  | tCase ci pred x bs, tCase ci' pred' x' bs' =>
    if ci == ci' then 
      let* (pred, bs) := liftM (rebuild_case Σ ci pred bs) (InternalError $ str $ "Failed to rebuild case"%pstring) in
      let* (pred', bs') := liftM (rebuild_case Σ ci' pred' bs') (InternalError $ str $ "Failed to rebuild case"%pstring) in 
      (* Unify the return predicates. *)
      let* evm := unify Γ Conv pred pred' evm in 
      (* Unify the scrutinees. *)
      let* evm := unify Γ Conv x x' evm in
      (* Unify the branches. *)
      ise_list2 (unify Γ Conv) bs bs' evm
    else failM NotSameHead
  (* App-FO *)
  | tApp f ts, tApp f' ts' => 
    let* evm := unify Γ pb f f' evm in 
    ise_list2 (unify Γ Conv) ts ts' evm
  | _, _ => failM NotSameHead
  end
  
(** [try_reduce] tries to reduce/unfold one side of the equation. *)
with try_reduce Γ pb (t t' : tapp) evm {struct pb} : M EvarMap.t :=
  let* flags := get_flags in
  let t := whd_tapp evm t in 
  let t' := whd_tapp evm t' in
  (* Helper function to check if we are _not_ allowed to reduce on the given side. *)
  let cannot_reduce side := negb $ Side.leq side (UnifFlags.reduce_side flags) in
  (* Lam-BetaL *)
  let lam_betaL :=
    if cannot_reduce Left then failM CannotReduce else
    match t with 
    | (tLambda _ _ body, arg :: args) => 
      let* _ := log_str "Lam-BetaL" in
      unify_tapp Γ pb (subst0 [arg] body, args) t' evm
    | _ => failM CannotReduce
    end
  in
  (* Lam-BetaR *)
  let lam_betaR :=
    if cannot_reduce Right then failM CannotReduce else
    match t' with 
    | (tLambda _ _ body', arg' :: args') => 
      let* _ := log_str "Lam-BetaR" in
      unify_tapp Γ pb t (subst0 [arg'] body', args') evm
    | _ => failM CannotReduce
    end
  in 
  (* Let-ZetaL *)
  let let_zetaL :=
    if cannot_reduce Left then failM CannotReduce else 
    match t with 
    | (tLetIn _ def _ body, args) =>
      let* _ := log_str "Let-ZetaL" in
      unify_tapp Γ pb (subst0 [def] body, args) t' evm
    | _ => failM CannotReduce
    end
  in
  (* Let-ZetaR *)
  let let_zetaR :=
    if cannot_reduce Right then failM CannotReduce else 
    match t' with 
    | (tLetIn _ def' _ body', args') =>
      let* _ := log_str "Let-ZetaR" in
      unify_tapp Γ pb t (subst0 [def'] body', args') evm
    | _ => failM CannotReduce
    end
  in
  (* Cons-DeltaL *)
  let cons_deltaL :=
    if cannot_reduce Left then failM CannotReduce else 
    let* def := liftM (unfold_def Γ t.1 evm) CannotReduce in 
    let* _ := log_str "Cons-DeltaL" in 
    unify_tapp Γ pb (def, t.2) t' evm
  in
  (* Cons-DeltaR *)
  let cons_deltaR :=
    if cannot_reduce Right then failM CannotReduce else 
    let* def' := liftM (unfold_def Γ t'.1 evm) CannotReduce in 
    let* _ := log_str "Cons-DeltaR" in 
    unify_tapp Γ pb t (def', t'.2) evm
  in
  (* Lam-EtaL *)
  let lam_etaL :=
    if cannot_reduce Left then failM CannotReduce else  
    match t, t' with
    | _, (tLambda _ _ _, _) => failM CannotReduce 
    | (tLambda x ty body, []), _ =>
      let* _ := log_str "Lam-EtaL" in
      eta_match Original Γ pb (x, ty, body) (mkApps t'.1 t'.2) evm
    | _, _ => failM CannotReduce
    end
  in
  (* Lam-EtaR *)
  let lam_etaR :=
    if cannot_reduce Right then failM CannotReduce else  
    match t, t' with
    | (tLambda _ _ _, _), _ => failM CannotReduce 
    | _, (tLambda x' ty' body', []) =>
      let* _ := log_str "Lam-EtaR" in
      eta_match Swapped Γ pb (x', ty', body') (mkApps t.1 t.2) evm
    | _, _ => failM CannotReduce
    end
  in
  (* First try beta/zeta/iota reduction. *)
  lam_betaL    <|> lam_betaR    <|>
  let_zetaL    <|> let_zetaR    <|>
  (* Then try delta reduction. *)
  cons_deltaL  <|> cons_deltaR  <|>
  (* Finally try eta expansion. *)
  lam_etaL     <|> lam_etaR     <|>
  (* Reducing was not successful. *) 
  failM CannotReduce

(** [check_product Γ t (x, ty) evm] unifies [t <=? forall x : ty, ?body]
    where [?body : Type] is a fresh evar. *)
with check_product Γ (t : term) (x_ty : aname * term) evm {struct t} : M EvarMap.t :=
  let (x, ty) := x_ty in
  (* Create a fresh universe. *)
  let (evm, univ) := EvarMap.fresh_universe evm in
  (* Extend the ambient named context Δ with a declaration for the argument [x : ty] of the product. *)
  let id' := 
    fresh_ident 
      (match x.(binder_name) with nNamed n => n | nAnon => "x" end) 
      (IdentSetProp.of_list $ List.map fst Δ) 
  in 
  let x' := {| binder_name := nNamed id' ; binder_relevance := x.(binder_relevance) |} in
  let ev_nctx := (id', vass x' ty) :: Δ in
  (* Create the body of the product. *)
  let (evm, ev) := EvarMap.fresh_evar evm "body" ev_nctx (tSort $ sType univ) in
  let body := tEvar ev (tRel 0 :: List.map (tVar <<< fst) Δ) in
  (* Unify [t <=? forall x : ty, ?body]. *)
  unify Γ Cumul t (tProd x ty body) evm

(** [eta_match dir Γ pb x ty body t' evm] implements the eta-expansion rule
    to unify [(fun x : ty => body) =?= t']. *)
with eta_match dir Γ pb (x_ty_body : aname * term * term) (t' : term) evm {struct pb} : M EvarMap.t :=
  let '(x, ty, body) := x_ty_body in
  (* Check [t'] is a product with domain [ty]. *)
  let* ty' := type_of evm Δ Γ t' in
  let* evm := check_product Γ ty' (x, ty) evm in 
  (* Lift [t'] and apply it to [tRel 0]. *)
  let t'' := mkApp (lift0 1 t') (tRel 0) in
  (* Unify [body =?= t'']. *)
  match dir with 
  | Original => unify (Γ ,, vass x ty) pb body t'' evm
  | Swapped => unify (Γ ,, vass x ty) pb t'' body evm
  end.

End Algorithm.

(****************************)
(** Testing *)

From MetaCoq.Template Require Import All.

Definition env := fst ($quote_rec (nat, app, In)).

Definition vass' (n : ident) (ty : term) : context_decl :=
  vass {| binder_name := nNamed n ; binder_relevance := Relevant |} ty.

Definition test := 
  (* named context. *)
  let y1 := "y1" in 
  let y2 := "y2" in 
  let Δy :=
    [ (y1, vass' y1 ($quote nat))
    ; (y2, vass' y2 ($quote nat)) ]
  in 
  (* evar map. *)
  let evm := EvarMap.empty in 
  let (evm, z0) := EvarMap.fresh_evar evm "z" [] ($quote (nat -> nat -> nat)) in
  (* terms to unify. *)
  let t1_body :=
    mkApps ($quote In)
      [ $quote nat
      ; mkApps (tEvar z0 []) [tVar y1 ; tVar y2]
      ; tRel 0 ]
  in 
  let t1 := tLam "arg" ($quote (list nat)) t1_body in
  let t2 := mkApps ($quote In) [ $quote nat ; tVar y1 ] in
  (* Unify the terms. *)
  let (log, res) := @unify PrettyFlags.default default_checker_flags env Δy [] Conv t1 t2 evm UnifFlags.default in
  let log_str := pp_string 120 $ @Log.print PrettyFlags.default env log in
  let res_str :=
    match res with 
    | Success evm => pp_string 120 $ @EvarMap.print PrettyFlags.default (env, Monomorphic_ctx) evm
    | UnifError _ => "error"%pstring
    end 
  in
  (res_str, log_str).

Eval vm_compute in test.
