(* Distributed under the terms of the MIT license. *)

From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import BasicAst uGraph config.
From MetaCoq.Template Require Import Ast AstUtils Typing Checker Evars Pretty.
Import MCMonadNotation.

Unset Guard Checking.

(** This file defines a unification algorithm inspired by Unicoq :
    "A Unification Algorithm for COQ Featuring Universe Polymorphism and Overloading"
    https://github.com/unicoq
    
    It is intended for practical use and is not verified 
    (we even disable the guard checker). *)

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

(** The algorithm logs some information : a [log_level] controls how much
    information is logged. *)
Inductive log_level := 
  (** Don't log any information. *)
  | LogSilent
  (** Log information only for successful rules. *)
  | LogDefault
  (** Log information for all rules, including unsuccessful ones.
      This easily can generate huge logs. *)
  | LogVerbose.

(** Unification flags control the behaviour of the unification algorithm. *)
Module UnifFlags.
Record t := mk
  { (** How much information should we log ? *)
    log_lvl : log_level 
  ; (** When instantiating an evar with a term [t], should we weak-head beta reduce [t] ?
        This helps to remove false dependencies, e.g. when [t] is [(fun _ => 0) x]. *)
    inst_beta_reduce : bool
  ; (** When unifying an evar with a term [t], should we unify the type of the evar
        with the type of [t] ? *)
    inst_unify_types : bool 
  ; (** When unifying [?x[subs1] =?= ?x[subs2]] (rule Meta-Same), should we allow
        [subs1] and [subs2] to disagree on positions which are not variables (tVar or tRel) ? *)
    meta_same_aggressive : bool
  ; (** On which side(s) is it allowed to reduce ? *)
    reduce_side : Side.t
  ; (** On which side(s) is it allowed to instantiate evars ? *)
    inst_side : Side.t 
  ; (** Which evars are allowed to be instantiated ? 
        If [None] than all evars are instantiable. *)
    inst_evars : option ESet.t }.

(** Reasonable default flags. *)
Definition default := mk LogDefault true true false Both Both None.

(** Modify the [reduce_side] in some flags. *)
Definition set_reduce_side (s : Side.t) (flags : t) : t :=
  {| log_lvl              := flags.(log_lvl) 
  ;  inst_beta_reduce     := flags.(inst_beta_reduce) 
  ;  inst_unify_types     := flags.(inst_unify_types) 
  ;  meta_same_aggressive := flags.(meta_same_aggressive)
  ;  reduce_side          := s 
  ;  inst_side            := flags.(inst_side)
  ;  inst_evars           := flags.(inst_evars)|}.
  
(** Modify the [inst_side] in some flags. *)
Definition set_inst_side (s : Side.t) (flags : t) : t :=
  {| log_lvl              := flags.(log_lvl)
  ;  inst_beta_reduce     := flags.(inst_beta_reduce) 
  ;  inst_unify_types     := flags.(inst_unify_types) 
  ;  meta_same_aggressive := flags.(meta_same_aggressive)
  ;  reduce_side          := flags.(reduce_side) 
  ;  inst_side            := s
  ;  inst_evars           := flags.(inst_evars) |}.  

End UnifFlags.

(** Unification returns a [unif_result]. *)
Inductive unif_result A : Type := 
  (** [UnifSuccess x] : unification succeeded with result [x] (typically the updated evar map). *)
  | UnifSuccess : A -> unif_result A
  (** [UnifError] : unification failed. Look at the log for additional details. *)
  | UnifError : unif_result A.
Arguments UnifSuccess {A}%_type_scope a.
Arguments UnifError {A}%_type_scope.

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
  | inr d => group $ align $ d
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
    | UnifSuccess _ => str "[success]"
    | UnifError => str "[error]"
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
Definition retM {A} (a : A) : M A := fun _ => (Log.empty, UnifSuccess a).

(** [failM err] writes [err] to the log and returns [UnifError] *)
Definition failM {A} (err : doc unit) : M A := 
  fun flags => 
    match UnifFlags.log_lvl flags with
    | LogSilent => (Log.empty, UnifError)
    | _ => (Log.Log [inr err], UnifError)
    end.

(** Monadic bind. *)
Definition bindM {A} {B} (ma : M A) (mf : A -> M B) : M B :=
  fun flags =>
    match ma flags with 
    | (l, UnifSuccess a) => let (l', res) := mf a flags in (Log.append l l', res)
    | (l, UnifError) => (l, UnifError)
    end.
Notation "'let*' x := c1 'in' c2" := (bindM c1 (fun x => c2))
  (at level 100, x pattern, c1 at next level, right associativity).

(** Monad instance for [M]. To avoid typeclass errors, I prefer using [retM] and [let*] 
    instead of [ret] and [mlet]. *)
Instance monad_M : Monad M :=
{ ret _ := retM ; bind _ _ := bindM }.

(** Monadic alternative. The [log_lvl] flag controls if we keep the logs of 
    failed attempts. *)
Definition orM {A} (mx my : M A) : M A :=
  fun flags =>
    match mx flags with 
    | (l, UnifSuccess x) => (l, UnifSuccess x)
    | (l, UnifError) => 
      let (l', y) := my flags in 
      match UnifFlags.log_lvl flags with 
      | LogVerbose => (Log.append l l', y)
      | _ => (l', y)
      end
    end.
Notation "x <|> y" := (orM x y) (at level 85, right associativity).
   
(** [whenM cond x] executes [x] if [cond] is true, and otherwise does nothing. *)
Definition whenM (cond : bool) (x : M unit) : M unit :=
  if cond then x else retM tt.

(** Log a (primitive) string. *)
Definition log_str (s : string) : M unit :=
  fun flags =>
    match UnifFlags.log_lvl flags with 
    | LogSilent => (Log.empty, UnifSuccess tt)
    | _ => (Log.Log [inr $ str s], UnifSuccess tt)
    end.

(** Log a document. *)
Definition log_doc (d : doc unit) : M unit :=
  fun flags => 
    match UnifFlags.log_lvl flags with 
    | LogSilent => (Log.empty, UnifSuccess tt)
    | _ => (Log.Log [inr d], UnifSuccess tt)
    end.
  
(** Log a unification (sub)problem. It collects the logs of [problem],
    packages them in a [Log.node], and returns the same [unif_result] as [problem].  *)
Definition log_problem Γ pb t t' evm (problem : M EvarMap.t) : M EvarMap.t :=
  fun flags =>
    let (elements, res) := problem flags in 
    match UnifFlags.log_lvl flags with 
    | LogSilent => (Log.empty, res)
    | _ =>
      let node := Log.mknode _ evm Γ pb t t' elements res in
      (Log.Log [inl node], res)
    end.  

(** [liftM x err] lifts a value from the [option] monad to [M].
    In case of failure it writes [err] to the log. *)
Definition liftM {A} (x : option A) (msg : doc unit) : M A :=
  match x with 
  | Some x => retM x
  | None => failM msg
  end.

(** Get the unification flags. *)
Definition get_unif_flags : M UnifFlags.t :=
  fun flags => (Log.empty, UnifSuccess flags).

(** [with_unif_flags flags x] runs the computation [x] with unification flags
    set to [flags]. *)
Definition with_unif_flags {A} (flags : UnifFlags.t) (x : M A) : M A :=
  fun _ => x flags.

(** [has_free_rel evm n t] checks if [tRel n] occurs in [t], expanding evars on the way. *)
Fixpoint has_free_rel (evm : EvarMap.t) (n : nat) (t : term) : bool :=
  match whd_evars evm t with 
  | tRel n' => n == n' 
  | t => fold_term_with_binders n (fun _ => S) 
           (fun n b t => b || has_free_rel evm n t) false t
  end.

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

(** [ise_list2 f xs ys evm] applies [f] to each element of [xs] and [ys],
    updating the evar map [evm] along the way. *)
Definition ise_list2 {A B} (f : A -> B -> EvarMap.t -> M EvarMap.t) 
  (xs : list A) (ys : list B) (evm : EvarMap.t) : M EvarMap.t :=
  let fix loop xs ys evm :=
    match xs, ys with 
    | [], [] => retM evm 
    | x :: xs, y :: ys =>
      let* evm := f x y evm in loop xs ys evm
    | _, _ => failM $ str "ise_list2 : incompatible argument sizes"
    end
  in 
  (* Applying [f] might be costly : we first check if the lengths match. *)
  if #|xs| == #|ys| then loop xs ys evm 
  else failM $ str "ise_list2 : incompatible argument sizes".

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

(** * Unification algorithm. *)

Section Algorithm.
Context `{PrettyFlags.t} (Σ : global_env) (Δ : named_context).
Existing Instance default_checker_flags.

(** * Term applications. *)

(** Similar to a stack reduction machine, the unification algorithm keeps
    the arguments of applications separate from the head :[(f, args)] represents 
    the application [mkApps f args]. Note that we do not always maintain the invariant 
    that [args] is non-empty or that [f] is not an application : we use [whd_tapp]
    whenever we require these conditions locally. *)
Definition tapp := term * list term.

(** [whd_tapp evm t] expands evars and removes casts in the head of [t]. *)
Fixpoint whd_tapp (evm : EvarMap.t) (t : tapp) {struct t} : tapp :=
  let (f, args) := t in
  match whd_evars evm f with 
  | tApp f' args' => whd_tapp evm (f', args' ++ args)
  | tCast f' _ _ => whd_tapp evm (f', args)
  | f' => (f', args)
  end.

(** [whd_beta_tapp evm (t, args)] weak-head beta reduces the term [mkApps f args]. *)
Definition whd_beta_tapp (evm : EvarMap.t) (t : tapp) : tapp :=
  let fix loop t {struct t} :=
    match whd_tapp evm t with 
    | (tApp f args1, args2) => loop (f, args1 ++ args2)
    | (tLambda _ _ body, arg :: args) => loop (subst0 [arg] body, args) 
    | t => t
    end
  in
  loop t.

(** [unif_fun t] is the type of functions which can unify things of type [t]
    (typically [term] or [tapp]). *)
Definition unif_fun t := context -> conv_pb -> t -> t -> EvarMap.t -> M EvarMap.t.

(** [type_of evm Δ Γ t] computes the type of term [t] in named context [Δ] and local context [Γ].
    It assumes that [t] is well-typed. *)
Definition type_of (evm : EvarMap.t) (Δ : named_context) (Γ : context) (t : term) : M term :=
  match retype evm Σ Δ Γ t with 
  | Checked ty => retM ty 
  | TypeError err => 
    failM $
      str "The term" ^/^ 
      print_term (Σ, Monomorphic_ctx) (context_names Γ) t ^/^
      str "is ill-typed." 
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
    (str "Failed to invert the term" ^/^
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
  let* entry := liftM (EvarMap.lookup evm ev) (str "Undefined evar #" ^^ nat10 ev) 
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
      if eq_term_evars evm Conv x y then loop (S i) xs ys diff 
      else if is_var x && is_var y then loop (S i) xs ys (i :: diff)
      else if UnifFlags.meta_same_aggressive flags then loop (S i) xs ys (i :: diff)
      else None
    | _, _ => None 
    end 
  in 
  loop 0 xs ys [].

(** [unfold_def Γ t evm] unfolds the definition of a local variable (tRel or tVar) or constant. *)
Definition unfold_def Γ t evm : option term :=
  match whd_evars evm t with 
  | tRel n => 
    match decl_body =<< List.nth_error Γ n with 
    | Some body => Some $ lift0 (S n) body
    | None => None 
    end 
  | tVar id => decl_body =<< lookup_nctx Δ id
  | tConst c uinst =>
    match cst_body =<< lookup_constant Σ c with 
    | Some body => Some $ subst_instance uinst body
    | None => None 
    end
  | _ => None 
  end.

(** [check_product Γ t (x, ty) evm] unifies [t <=? forall x : ty, ?body]
    where [?body : Type] is a fresh evar. *)
Definition check_product (unify : unif_fun term) Γ (t : term) (x_ty : aname * term) evm : M EvarMap.t :=
  let (x, ty) := x_ty in
  (* Create a fresh universe level for the type of the body. *)
  let (evm, lvl) := EvarMap.fresh_level evm in
  (* Extend the ambient named context Δ with a declaration for the argument [x : ty] of the product. *)
  let id' := 
    fresh_ident 
      (match x.(binder_name) with nNamed n => n | nAnon => "x" end) 
      (IdentSetProp.of_list $ List.map fst Δ) 
  in 
  let x' := {| binder_name := nNamed id' ; binder_relevance := x.(binder_relevance) |} in
  let ev_nctx := (id', vass x' ty) :: Δ in
  (* Create the body of the product. *)
  let (evm, ev) := EvarMap.fresh_evar evm "body" ev_nctx (tSort $ sType $ Universe.make' lvl) in
  let body := tEvar ev (tRel 0 :: List.map (tVar <<< fst) Δ) in
  (* Unify [t <=? forall x : ty, ?body]. *)
  unify Γ Cumul t (tProd x ty body) evm.
  
(** [eta_match dir Γ pb x ty body t' evm] implements the eta-expansion rule
    to unify [(fun x : ty => body) =?= t']. *)
Definition eta_match (unify : unif_fun term) dir Γ pb (x_ty_body : aname * term * term) (t' : term) evm : M EvarMap.t :=
  let '(x, ty, body) := x_ty_body in
  (* Check [t'] is a product with domain [ty]. *)
  let* ty' := type_of evm Δ Γ t' in
  let* evm := check_product unify Γ ty' (x, ty) evm in 
  (* Lift [t'] and apply it to [tRel 0]. *)
  let t'' := mkApp (lift0 1 t') (tRel 0) in
  (* Unify [body =?= t'']. *)
  match dir with 
  | Original => unify (Γ ,, vass x ty) pb body t'' evm
  | Swapped => unify (Γ ,, vass x ty) pb t'' body evm
  end.

(** * Convertibility heuristic. *)

Section TryConv.

(** Helper function to determine if a term is evar-free. *)
Fixpoint is_evarfree (t : term) : bool :=
  match t with 
  | tEvar _ _ => false 
  | _ => fold_term (fun b t => b && is_evarfree t) true t
  end.

(** [try_conv Γ pb t t'] implements the Reduce-Same rule, which tries to unify evar-free terms
    [t] and [t'] by checking conversion (currently is uses the algorithm defined in Checker.v). *)
Definition try_conv Γ pb (t t' : tapp) evm : M (EvarMap.t) :=
  let t := mkApps t.1 t.2 in
  let t' := mkApps t'.1 t'.2 in
  if is_evarfree t && is_evarfree t' then 
    if check_conv RedFlags.all evm Σ Δ Γ pb t t' 
    then let* _ := log_str "Reduce-Same" in retM evm
    else failM $ str "Reduce-Same : not convertible"
  else failM $ str "Reduce-Same : terms contain evars".

End TryConv.

(** * First-order approximation. *)

Section TryAppFO.
Context (unify : unif_fun term).

(** Structurally unify the heads of two terms. *)
Definition unify_head Γ pb (t t' : term) evm : M EvarMap.t :=
  (* Helper function to unify universe instances.
     Instances are always unified using equality (not cumulativity). *)
  let unify_uinst u u' evm :=
    ise_list2 
      (fun l l' evm => 
        liftM (EvarMap.set_eq_level evm l l') 
              (str "Unify-UInst : universe inconsistency"))
      u u' evm 
  in
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
    liftM evm $ str "Type-Same : universe inconsistency"
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
  (* Rel-Same *)
  | tRel n, tRel n' => 
    if n == n' then retM evm 
    else failM $ str "Rel-Same : not same head"
  (* Var-Same *)
  | tVar v, tVar v' => 
    if v == v' then retM evm 
    else failM $ str "Var-Same : not same head"
  (* Const-Same *)
  | tConst c u, tConst c' u' =>
    if c == c' then unify_uinst u u' evm
    else failM $ str "Const-Same : not same head"
  (* Ind-Same *)
  | tInd ind u, tInd ind' u' =>
    if ind == ind' then unify_uinst u u' evm
    else failM $ str "Ind-Same : not same head"
  (* Construct-Same *)
  | tConstruct ind n u, tConstruct ind' n' u' =>
    if (ind == ind') && (n == n') then unify_uinst u u' evm 
    else failM $ str "Construct-Same : not same head"  
  (* Proj-Same *)
  | tProj p t, tProj p' t' =>
    if p == p' then unify Γ Conv t t' evm 
    else failM $ str "Prof-Same : not same head"
  (* (Co)Fix-Same *)
  | tFix defs n, tFix defs' n'
  | tCoFix defs n, tCoFix defs' n' =>
    if n == n' then 
      (* First unify the types. *)
      let* evm := ise_list2 (unify Γ Conv) (List.map dtype defs) (List.map dtype defs') evm in
      (* Then unify the bodies in an extended context. *)
      ise_list2 (unify (Γ ,,, fix_context defs) Conv) (List.map dbody defs) (List.map dbody defs') evm
    else failM $ str "(Co)Fix-Same : not same head"
  (* Case-Same *)
  | tCase ci pred x bs, tCase ci' pred' x' bs' =>
    if ci == ci' then 
      (* Instead of unifying the arguments of each branch one by one and then the bodies,
         we reconstruct the lambda abstractions corresponding the the branches and predicate
         and unify those directly. *)
      let* (pred_t, bs_t) := liftM (rebuild_case Σ ci pred bs) (str $ "Failed to rebuild case"%pstring) in
      let* (pred_t', bs_t') := liftM (rebuild_case Σ ci' pred' bs') (str $ "Failed to rebuild case"%pstring) in 
      (* Unify the return predicates. *)
      let* evm := unify Γ Conv pred_t pred_t' evm in 
      (* Unify the universe instances. *)
      let* evm := unify_uinst pred.(puinst) pred'.(puinst) evm in
      (* Unify the scrutinees. *)
      let* evm := unify Γ Conv x x' evm in
      (* Unify the branches. *)
      ise_list2 (unify Γ Conv) bs_t bs_t' evm
    else failM $ str "Case-Same : not same head"
  (* Int-Same *)
  | tInt x, tInt x' =>
    if x == x' then retM evm 
    else failM $ str "Int-Same : not same head"
  (* Float-Same *)
  | tFloat x, tFloat x' =>
    if x == x' then retM evm 
    else failM $ str "Float-Same : not same head"
  (* String-Same *)
  | tString s, tString s' =>
    match PrimString.compare s s' with 
    | Eq => retM evm 
    | _ => failM $ str "String-Same : not same head"
    end
  | _, _ => failM $ str "Head-Same : not applicable"
  end.

(** [try_app_fo] applies the first-order heuristic to structurally unify 
    the two sides of an equation. *)
Definition try_app_fo Γ pb (t t' : tapp) evm : M EvarMap.t :=
  let (f, args) := whd_tapp evm t in 
  let (f', args') := whd_tapp evm t' in
  if #|args| == #|args'| then 
    let* _ := log_str "App-FO" in
    (* Unify the heads. *)
    let* evm := unify_head Γ pb f f' evm in 
    (* Unify the arguments. *)
    ise_list2 (unify Γ Conv) args args' evm
  else 
    failM $ str "App-FO : not same arg size".

End TryAppFO.

(** * Evar instantiation. *)

Section TryInstantiate.
Context (unify : unif_fun term) (unify_tapp : unif_fun tapp).

(** [meta_same ev subs1 subs2 evm] implements the Meta-Same rule to unify [ev[subs1] =?= ev[subs2]]. *)
Definition meta_same (ev : evar) (subs1 subs2 : list term) evm : M EvarMap.t :=
  let* _ := log_str "Meta-Same" in
  (* Check if the evar can be instantiated. *)
  let* flags := get_unif_flags in
  if allowed_inst flags ev Both then 
    (* Prune the evar on the positions where [subs1] and [subs2] disagree. *)
    match intersect flags evm subs1 subs2 with
    (* Meta-Same-Same *)
    | Some [] => retM evm
    (* Meta-Same *)
    | Some pos => prune evm ev pos
    | None => failM $ str "Meta-Same : failed intersecting."
    end
  else failM $ str "Meta-Same : not applicable".

(** [remove_equal_tails (f, args) (f', args')] removes the equal variables 
    (tRel or tVar) of args and args', starting from the right most argument, 
    and until a different variable is found. It needs to check that no
    solution is lost, meaning that the variable being removed is not
    duplicated in any of the spines or bodies. *)
Definition remove_equal_tails (evm : EvarMap.t) (t t' : tapp) : list term * list term :=
  (* We process arguments from last to first. *)  
  let fix loop xs ys :=
    match xs, ys with 
    | tRel n :: xs, tRel n' :: ys => 
      if (n == n') && List.forallb (negb <<< has_free_rel evm n) (t.1 :: t'.1 :: xs ++ ys)  
      then loop xs ys else (rev xs, rev ys)
    | tVar id :: xs, tVar id' :: ys =>
      if (id == id') && List.forallb (negb <<< has_free_var evm [id]) (t.1 :: t'.1 :: xs ++ ys)
      then loop xs ys else (rev xs, rev ys)
    | _, _ => (rev xs, rev ys)
    end 
  in 
  loop (rev t.2) (rev t'.2).  

(** Helper function used to implement [meta_inst]. 
    It inverts the equation [ev[subs] args =?= t] and returns :
    - the updated evar map (after pruning).
    - the term [t'] that [ev] will get instantiated with, which lives in the local context of [ev]. *)
Definition meta_inst_solution Γ (ev : evar) (subs args : list term) (t : tapp) evm : M (EvarMap.t * term) :=
  (* Remove equal tails in the two lists of arguments.
     This helps avoid unnecessarily eta-expanded solutions. *)
  let (args, t_args) := remove_equal_tails evm (tEvar ev subs, args) t in
  let t := (t.1, t_args) in
  (* If the relevant flag is set, weak-head beta reduce [t] to remove dependencies. *)
  let* flags := get_unif_flags in
  let t := if UnifFlags.inst_beta_reduce flags then whd_beta_tapp evm t else t in
  (* Invert [t]. *)
  let* entry := liftM (EvarMap.lookup evm ev) (str "Undefined evar #" ^^ nat10 ev) in
  let t := mkApps t.1 t.2 in
  let* (map, t) := invert evm (EMap.empty (list nat)) entry.(ev_nctx) ev subs args t in
  let* (map, t) := invert_lambdas evm Γ map entry.(ev_nctx) ev subs args t in
  (* Prune the evar map as required by [map]. *)
  let* evm := prune_all evm map tt in
  (* TODO : refresh universes. *)
  retM (evm, t).

(** [meta_inst dir Γ ev subs args t evm] implements the Meta-Inst rule to instantiate [ev[subs] args := t].
    [dir] is [Original] if [ev] is on the left-hand side, and [Swapped] if [ev] is on the right-hand side. *)
Definition meta_inst dir Γ ev subs args (t : tapp) evm : M EvarMap.t :=
  let is_var t := 
    match whd_evars evm t with tVar _ | tRel _ => true | _ => false end 
  in
  (* Check the evar is instantiable and that the substitution and arguments contain 
     only variables (tVars and tRels). *)
  let side := match dir with Original => Left | Swapped => Right end in
  let* flags := get_unif_flags in
  if allowed_inst flags ev side && List.forallb is_var (subs ++ args) then 
    let* _ := log_doc $ str "Meta-Inst-" ^^ match dir with Original => str "L" | Swapped => str "R" end in
    (* Allow reduction and instantiation on both sides in subproblems. *)
    let flags := 
      UnifFlags.set_reduce_side Both $
      UnifFlags.set_inst_side Both flags
    in
    with_unif_flags flags $  
    (* Compute the solution [sol]. *)
    let* (evm, sol) := meta_inst_solution Γ ev subs args t evm in
    let* _ := log_doc $ str "solution :" ^+^ 
      print_term (Σ, Monomorphic_ctx) [] sol 
    in
    (* Unify the type of the evar with the type of the solution (if the relevant flag is set). *)
    let* evm :=
      if UnifFlags.inst_unify_types flags
      then 
        let* entry := liftM (EvarMap.lookup evm ev) (str "Undefined evar #" ^^ nat10 ev) in
        let* sol_ty := type_of evm entry.(ev_nctx) [] sol in
        let ev_ty := instantiate_evar entry.(ev_nctx) subs entry.(ev_concl) in
        unify Γ Cumul sol_ty ev_ty evm
      else retM evm
    in 
    (* Check the evar does not occur in the solution. *)
    if evar_occurs evm ev sol then failM $ str "Meta-Inst : occur check failed" else
    (* Finally define the evar. *)
    retM $ EvarMap.define evm ev sol
  else failM $ str "Meta-Inst : not applicable".

(** [meta_fo dir Γ pb ev subs args t evm] implements a first-order heuristic to 
    unify [ev[subs] args] and [t]. This heuristic is similar to the rule App-FO
    but slightly more general : it applies even if [t] has more arguments than [ev]. 
    For instance it will split the problem [ev[subs] x1 x2 =?= f y1 y2 y3 y4] into
    the subproblems [ev[subs] =?= f y1 y2], [x1 =?= y3] and [x2 =?= y4].  *)
Definition meta_fo dir Γ pb ev subs args (t : tapp) evm : M EvarMap.t :=
  (* Check if we are allowed to use this heuristic. *)
  let* flags := get_unif_flags in
  let ev_side := match dir with Original => Left | Swapped => Right end in
  if allowed_inst flags ev ev_side && 
     (* If the evar has no arguments, Meta-Inst will trigger. *)
     (0 <? #|args|) && 
     (* We allow [t] and [ev] to have the same number of arguments to be more general than App-FO. *)
     (#|args| <=? #|t.2|) 
  then
    let* _ := log_doc $ str "Meta-FO-" ^^ match dir with Original => str "L" | Swapped => str "R" end in
    (* Unify the heads and the arguments. As usual we check the arguments for 
       convertibility [Conv] even when checking the applications for cumulativity [Cumul]. *)
    let (t_args1, t_args2) := chop (#|t.2| - #|args|) t.2 in 
    match dir with 
    | Original =>
      let* evm := unify_tapp Γ pb (tEvar ev subs, []) (t.1, t_args1) evm in
      ise_list2 (unify Γ Conv) args t_args2 evm
    | Swapped =>
      let* evm := unify_tapp Γ pb (t.1, t_args1) (tEvar ev subs, []) evm in
      ise_list2 (unify Γ Conv) t_args2 args evm
    end
  else failM $ str "Meta-FO : not applicable".

(** [try_instantiate Γ pb t t' evm] is called when either [t] or [t'] is an evar (possible applied
    to a suspended subsitution and arguments), and tries to apply rules which instantiate evars. *)
Definition try_instantiate Γ pb (t t' : tapp) evm : M EvarMap.t :=
  let t := whd_tapp evm t in 
  let t' := whd_tapp evm t' in
  match t.1, t'.1 with 
  | tEvar ev subs, tEvar ev' subs' => 
    if ev == ev' then
    (* Meta-Same *)
      let* evm := meta_same ev subs subs' evm in 
      ise_list2 (unify Γ Conv) t.2 t'.2 evm
    (* Meta-Meta *)
    else
      (* We try both directions, but first the one with the longest substitution. *)
      let '(dir1, dir2, ev1, ev2, subs1, subs2, args1, args2, t1, t2) := 
        if #|subs| <? #|subs'|
        then (Swapped, Original, ev', ev, subs', subs, t'.2, t.2, t, t')
        else (Original, Swapped, ev, ev', subs, subs', t.2, t'.2, t', t)
      in 
      meta_inst dir1 Γ    ev1 subs1 args1 t1 evm <|> 
      meta_inst dir2 Γ    ev2 subs2 args2 t2 evm <|>
      meta_fo   dir1 Γ pb ev1 subs1 args1 t1 evm <|>
      meta_fo   dir2 Γ pb ev2 subs2 args2 t2 evm
  (* Meta-InstL *)
  | tEvar ev subs, _ => 
    meta_inst Original Γ    ev subs t.2 t' evm <|>
    meta_fo   Original Γ pb ev subs t.2 t' evm
  (* Meta-InstR *)
  | _, tEvar ev' subs' => 
    meta_inst Swapped Γ    ev' subs' t'.2 t evm <|>
    meta_fo   Swapped Γ pb ev' subs' t'.2 t evm
  | _, _ => failM $ str "try_instantiate : expected an evar"
  end.

End TryInstantiate.

(** * Reduction heuristics. *)

Section TryReduce.
Context (unify : unif_fun term) (unify_tapp : unif_fun tapp).

(** [is_stuck evm Γ t] determines if [t] is stuck, in the sense that reducing it
    is useless. This is used to implement controlled backtracking. *)
Definition is_stuck (evm : EvarMap.t) (Γ : context) (t : tapp) : bool :=
  let t := whd_tapp evm t in
  (* Unfold [t] if applicable. *)
  let t := 
    match unfold_def Γ t.1 evm with 
    | Some def => (def, t.2)
    | None => t
    end
  in
  (* Weak-head reduce [t] using a specialized reduction strategy.
     See [whd_theta_stack] for more details. *)
  let t := whd_theta_stack evm Σ Δ Γ t.1 t.2 in
  (* Check the head constructor. 
     NOTE : I include tVar here as it seems to make sense, 
     whereas the official unicoq implementation does not (probably a mistake ?). *)
  match t.1 with 
  | tCase _ _ _ _ | tFix _ _ | tCoFix _ _ | tVar _ | tRel _ | tLambda _ _ _ => true 
  | _ => false 
  end.
  
(** [try_reduce] tries to solve an equation by reducing or unfolding some terms.
    It uses quite sophisticated heuristics to decide when to reduce : read
    the Unicoq paper for more details. *)
Definition try_reduce Γ pb (t t' : tapp) evm : M EvarMap.t :=
  let* flags := get_unif_flags in
  let t := whd_tapp evm t in 
  let t' := whd_tapp evm t' in
  (* Helper function to check if we are allowed to reduce on the given side. *)
  let can_reduce side := Side.leq side (UnifFlags.reduce_side flags) in
  (* Lam-Beta-L *)
  let lam_betaL :=
    match can_reduce Left, t with 
    | true, (tLambda _ _ body, arg :: args) => 
      let* _ := log_str "Lam-Beta-L" in
      unify_tapp Γ pb (subst0 [arg] body, args) t' evm
    | _, _ => failM $ str "Lam-Beta-L : not applicable"
    end
  in
  (* Lam-Beta-R *)
  let lam_betaR :=
    match can_reduce Right, t' with 
    | true, (tLambda _ _ body', arg' :: args') => 
      let* _ := log_str "Lam-Beta-R" in
      unify_tapp Γ pb t (subst0 [arg'] body', args') evm
    | _, _ => failM $ str "Lam-Beta-R : not applicable"
    end
  in 
  (* Let-Zeta-L *)
  let let_zetaL :=
    match can_reduce Left, t with 
    | true, (tLetIn _ def _ body, args) =>
      let* _ := log_str "Let-Zeta-L" in
      unify_tapp Γ pb (subst0 [def] body, args) t' evm
    | _, _ => failM $ str "Let-Zeta-L : not applicable"
    end
  in
  (* Let-Zeta-R *)
  let let_zetaR :=
    match can_reduce Right, t' with 
    | true, (tLetIn _ def' _ body', args') =>
      let* _ := log_str "Let-Zeta-R" in
      unify_tapp Γ pb t (subst0 [def'] body', args') evm
    | _, _ => failM $ str "Let-Zeta-R : not applicable"
    end
  in
  (* Red-Iota-L *)
  let red_iotaL :=
    match can_reduce Left, t.1 with 
    | true, tCase _ _ _ _ | true, tFix _ _ | true, tCoFix _ _ =>
      (* Reduce and check we made progress. *)
      let t_new := whd_theta_stack evm Σ Δ Γ t.1 t.2 in
      if eq_term_evars evm Conv (mkApps t.1 t.2) (mkApps t_new.1 t_new.2) then 
        failM $ str "Red-Iota-L : no progress"
      else
        let* _ := log_str "Red-Iota-L" in 
        unify_tapp Γ pb t_new t' evm
    | _, _ => failM $ str "Red-Iota-L : not applicable"
    end
  in
  (* Red-Iota-R *)
  let red_iotaR :=
    match can_reduce Right, t'.1 with 
    | true, tCase _ _ _ _ | true, tFix _ _ | true, tCoFix _ _ =>
      (* Reduce and check we made progress. *)
      let t_new' := whd_theta_stack evm Σ Δ Γ t'.1 t'.2 in
      if eq_term_evars evm Conv (mkApps t'.1 t'.2) (mkApps t_new'.1 t_new'.2) then 
        failM $ str "Red-Iota-R : no progress"
      else 
        let* _ := log_str "Red-Iota-R" in 
        unify_tapp Γ pb t t_new' evm
    | _, _ => failM $ str "Red-Iota-R : not applicable"
    end
  in
  (* Cons-Delta-L *)
  let cons_deltaL :=
    match can_reduce Left, unfold_def Γ t.1 evm with 
    | true, Some def =>
      let* _ := log_str "Cons-Delta-L" in 
      let t_new := whd_theta_stack evm Σ Δ Γ def t.2 in
      unify_tapp Γ pb t_new t' evm
    | _, _ => failM $ str "Cons-Delta-L : not applicable"
    end
  in
  (* Cons-Delta-R *)
  let cons_deltaR :=
    match can_reduce Right, unfold_def Γ t'.1 evm with 
    | true, Some def' =>
      let* _ := log_str "Cons-Delta-R" in 
      let t_new' := whd_theta_stack evm Σ Δ Γ def' t'.2 in
      unify_tapp Γ pb t t_new' evm
    | _, _ => failM $ str "Cons-Delta-R : not applicable"
    end
  in
  (* Lam-Eta-L *)
  let lam_etaL :=
    match can_reduce Left, t, t' with
    | _, _, (tLambda _ _ _, _) => failM $ str "Lam-Eta-L : not applicable" 
    | true, (tLambda x ty body, []), _ =>
      let* _ := log_str "Lam-Eta-L" in
      eta_match unify Original Γ pb (x, ty, body) (mkApps t'.1 t'.2) evm
    | _, _, _ => failM $ str "Lam-Eta-L : not applicable"
    end
  in
  (* Lam-EtaR *)
  let lam_etaR :=
    match can_reduce Right, t, t' with
    | _, (tLambda _ _ _, _), _ => failM $ str "Lam-Eta-R : not applicable" 
    | true, _, (tLambda x' ty' body', []) =>
      let* _ := log_str "Lam-Eta-R" in
      eta_match unify Swapped Γ pb (x', ty', body') (mkApps t.1 t.2) evm
    | _, _, _ => failM $ str "Lam-Eta-R : not applicable"
    end
  in
  (* First try beta/zeta/iota reduction. *)
  lam_betaL    <|> lam_betaR    <|>
  let_zetaL    <|> let_zetaR    <|>
  red_iotaL    <|> red_iotaR    <|>
  (* Then try eta expansion. *)
  lam_etaL     <|> lam_etaR     <|>
  (* Finally try delta reduction. *)
  cons_deltaL  <|> cons_deltaR  <|>
  (* Reducing was not successful. *) 
  failM $ str "try_reduce : not applicable".

End TryReduce.

(** * Main unification loop. *)

(** [unify] unifies two terms : it is the main entry point of the algorithm.
    It is a simple wrapper around [unify_tapp]. *)
Fixpoint unify Γ pb (t t' : term) evm {struct pb} : M EvarMap.t :=
  unify_tapp Γ pb (t, []) (t', []) evm

(** [unify_tapp] unifies two [tapp]s [t] and [t']. Note that [t] and [t'] are not 
    required to be in whd_tapp-normal form. *)
with unify_tapp Γ pb (t t' : tapp) evm {struct pb} : M EvarMap.t :=
  log_problem Γ pb (tApp t.1 t.2) (tApp t'.1 t'.2) evm $
  let t := whd_tapp evm t in 
  let t' := whd_tapp evm t' in 
  if is_evar evm t.1 || is_evar evm t'.1 then 
    try_instantiate unify unify_tapp Γ pb t t' evm
  else 
    try_conv Γ pb t t' evm <|>
    try_app_fo unify Γ pb t t' evm <|>
    try_reduce unify unify_tapp Γ pb t t' evm.
  
End Algorithm.

(*************************************************************************************)
(** * Testing *)

(*From MetaCoq.Template Require Import All.

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
  let (log, res) := @unify PrettyFlags.default env Δy [] Conv t1 t2 evm UnifFlags.default in
  let log_str := pp_string 120 $ @Log.print PrettyFlags.default env log in
  let res_str :=
    match res with 
    | UnifSuccess evm => pp_string 120 $ @EvarMap.print PrettyFlags.default (env, Monomorphic_ctx) evm
    | UnifError => "error"%pstring
    end 
  in
  (res_str, log_str).

Eval vm_compute in test.*)

(* TODO : 
- investigate generation of universe constraints (maybe ask Matthieu for help)
- add controlled backtracking ("stuck" heuristic)
- reduce primitive projections.
*)