From Coq Require Import PrimString Uint63.
From MetaCoq.Template Require Import Ast.
From MetaCoq.Utils Require Import utils.
From PPrint Require Import All.

Open Scope pstring.

(** * Pretty-printing configuration. *)

Module Config.

(** The pretty-printing functions can show a variable amount of information,
    depending on the printing configuration. *)
Record t := mk
  { (** Should we print universes ? *)
    cf_universes : bool 
  ; (** Should we print evar instances ? *)
    cf_evar_instances : bool 
  ; (** Should we print relevance information ? *)
    cf_relevance : bool 
  ; (** Should we print match predicates ? *)
    cf_match_preds : bool
  ; (** Should we print all parentheses ? *) 
    cf_parentheses : bool 
  ; (** Should we print full kernel names ? *)
    cf_full_names : bool }.

(** Don't print any low-level details. *)
Definition none : t := mk false false false false false false.
  
(** Print all low-level details. *)
Definition all : t := mk true true true true true true.

(** Helper function to add universe printing to a configuration. *)
Definition with_universes (cf : t) : t :=
  {| cf_universes := true 
  ;  cf_evar_instances := cf.(cf_evar_instances)
  ;  cf_relevance := cf.(cf_relevance)
  ;  cf_match_preds := cf.(cf_match_preds) 
  ;  cf_parentheses := cf.(cf_parentheses)
  ;  cf_full_names := cf.(cf_full_names) |}.
  
End Config.

(** * Utils *)

(** A convenient notation for function application, which saves many parentheses. *)
Notation "f $ x" := (f x) (at level 10, x at level 100, right associativity, only parsing).

(** Some notations to avoid confusing string types. *)
Notation pstring := PrimString.string.
Notation bstring := bytestring.string.

(** Convert a bytestring to a primitive string. *)
Definition pstring_of_sbtring (bstr : bstring) : pstring :=
  let fix loop pstr bstr :=
    match bstr with 
    | String.EmptyString => pstr
    | String.String byte bstr => 
      let char := PrimString.make 1 $ Uint63.of_nat (Byte.to_nat byte) in
      loop (PrimString.cat pstr char) bstr
    end
  in
  loop "" bstr.

(** Convert a primitive string to a byte string. *)
Definition bstring_of_pstring (pstr : pstring) : bstring :=
  string_of_list char63_to_string (PrimStringAxioms.to_list pstr).

(** [bstr s] builds an atomic document containing the bytestring [s]. *)
Definition bstr {A} (s : bstring) : doc A :=
  str $ pstring_of_sbtring s.

(** Name handling. *)

(** While pretty-printing terms we store the names of the binders traversed so far
    in a _name context_ [id_0; id_1; ...; id_n], which is simply a list of [ident]. 
    The identifier [id_i] is the name associated to the de Bruijn index [i]. *)

Section NameHandling.
Context (env : global_env_ext).

(** [is_fresh ctx id] checks if [id] does not occur in context [ctx]. *)
Definition is_fresh (ctx : list ident) (id : ident) :=
  List.forallb (fun id' => negb (eqb id id')) ctx.

(** [name_for_type t] chooses a generic name for a variable of type [t]. *)
Fixpoint name_for_type (t : term) : bstring :=
  match t with
  | tRel _ | tVar _ | tEvar _ _ => "H"%bs
  | tSort _ => "X"%bs
  | tProd _ _ _ => "f"%bs
  | tLambda _ _ _ => "f"%bs
  | tLetIn _ _ _ t' => name_for_type t'
  | tApp f _ => name_for_type f
  | tConst _ _ => "x"%bs
  | tInd ind u =>
    match lookup_inductive env ind with
    | Some (_, body) => String.substring 0 1 (body.(ind_name))
    | None => "X"%bs
    end
  | _ => "U"%bs
  end.

(** [base_name n ty] creates a generic name from :
    - [n] if it is not anonymous.
    - [ty] otherwise. *)
Definition base_name (n : name) (t : option term) : ident :=
  match n with
  | nNamed n => n
  | nAnon =>
    match t with
    | Some t => name_for_type t
    | None => "_"%bs
    end
  end.

(** [fresh_name ctx basename] generates a fresh name in context [ctx],
    starting from [basename]. *)
Definition fresh_name (ctx : list ident) (basename : ident) : ident :=
  (* Try without any suffix. *)
  if is_fresh ctx basename then basename
  (* Try suffixes, starting at 0 and couting up. *)
  else 
    let fix loop i fuel :=
      let name := (basename ++ string_of_nat i)%bs in
      match fuel with 
      | 0 => (* This should not happen. *) name
      | S fuel => if is_fresh ctx name then name else loop (S i) fuel
      end
    in 
    (* This fuel value should be big enough. *)
    loop 0 (List.length ctx).

(** Get the [context] associated to a fixpoint. *)
Definition fix_context (m : mfixpoint term) : context :=
  List.rev (mapi (fun i def => vass def.(dname) (lift0 i def.(dtype))) m).

(** [push_context decls ctx] adds fresh names for the declarations [decls]
    to the name context [ctx]. *)
Definition push_context (decls : context) (ctx : list ident) : list ident :=
  let fix loop decls ctx :=
    match decls with
    | [] => ctx
    | d :: decls => 
      let basename := base_name (binder_name d.(decl_name)) (Some d.(decl_type)) in
      loop decls (fresh_name ctx basename :: ctx)
    end 
  in
  loop (MCList.rev decls) ctx.

Definition string_of_constructor (ind : inductive) (ctor_idx : nat) : bstring :=
  (string_of_inductive ind ++ "," ++ string_of_nat ctor_idx)%bs.

End NameHandling.

(** Pretty-printing. *)

Section Printing.
Context (config : Config.t).

Section Env.
Context (env : global_env_ext).

(** [paren_if top d] adds parentheses around document [d] if [top] is equal to [false].
    It takes into account the configuration option to force parentheses. *)
Definition paren_if {A} (top : bool) (d : doc A) : doc A :=
  if Config.cf_parentheses config || negb top then paren d else d.
  
Definition print_name (n : name) : doc unit :=
  match n with 
  | nAnon => str "_"
  | nNamed n => bstr n
  end. 

About Instance.t.

(** Print a kernel name. This is not so simple : 
    - the configuration options might require us to print the full name.
    - we treat single-letter labels specially, e.g. [MetaCoq.Common.Universes.Instance.t]
      is printed as [Instance.t] instead of just [t]. *)
Definition print_kername (kname : kername) : doc unit :=
  (* Helper function get the identifiers in a module path. *)
  let fix modpath_ids path acc :=
    match path with 
    | MPfile dirpath => List.rev dirpath ++ acc
    | MPbound dirpath id _ => 
      (* TODO : is this correct ? *)
      List.rev (id :: dirpath)
    | MPdot path id => modpath_ids path (id :: acc)
    end
  in
  let (modpath, label) := kname in
  let path := modpath_ids modpath [] in 
  if Config.cf_full_names config then 
    (* If the config option is set, print the full module path. *)
    flow_map (str ".") bstr $ path ++ [label]
  else if String.length label <=? 1 then 
    (* If the label is very short, print the last part of the modpath + the label. *)
    match List.last (List.map Some path) None with 
    | Some prefix => flow_map (str ".") bstr $ [prefix ; label]
    | None => bstr label 
    end
  else 
    (* Otherwise print only the identifier *)
    bstr label.

Definition print_level (l : Level.t) : doc unit :=
  match l with 
  | Level.lzero => str "Set"
  | Level.level s => bstr s
  | Level.lvar n => 
    (* For level variables, we try to get the name of the level in the local universe context. *)
    match snd env with 
    | Monomorphic_ctx => str "lvar" ^^ nat10 n
    | Polymorphic_ctx (univ_names, _) => 
      match List.nth_error univ_names n with 
      | Some uname => print_name uname 
      | None => str "lvar" ^^ nat10 n
      end
    end
  end.

Definition print_level_expr (le : LevelExprSet.elt) : doc unit :=
  match le with 
  | (l, 0) => print_level l
  | (l, n) => print_level l ^^ str "+" ^^ nat10 n
  end.
  
Definition print_sort (s : sort) :=
  match s with
  | sProp => str "Prop"
  | sSProp => str "SProp"
  | sType l =>
    if Config.cf_universes config
    then
      let lvls := flow_map (str "," ^^ break 0) print_level_expr $ LevelExprSet.elements l in 
      bracket "Type@{" lvls "}"
    else str "Type"
  end.

Definition print_univ_instance (uinst : Instance.t) : doc unit :=
  if Config.cf_universes config && negb (uinst == []) then 
    let lvls := flow_map (break 0) print_level uinst in 
    bracket "@{" lvls "}"
  else 
    empty.

(** Print the names bound by a universe declaration, but _not_ the constraints. *)
Definition print_univ_decl (decl : universes_decl) : doc unit :=
  match decl with 
  | Monomorphic_ctx => empty 
  | Polymorphic_ctx (unames, _) =>
      bracket "@{" (flow_map (str "," ^^ break 0) print_name unames) "}"  
  end.
  
(** Helper function to print a single definition in a fixpoint block. *)
Definition print_def {A} (on_ty : A -> doc unit) (on_body : A -> doc unit) (def : def A) :=
  let n_doc := 
    separate space 
      [ print_name (binder_name $ def.(dname)) 
      ; str "{ struct" ^+^ nat10 def.(rarg) ^+^ str "}" 
      ; str ":" ] 
  in
  let ty_doc := on_ty def.(dtype) ^+^ str ":=" in
  let body_doc := on_body def.(dbody) in 
  (* We don't [align] here on purpose. *)
  group $ group (n_doc ^//^ ty_doc) ^//^ body_doc.
         
  

(** Helper function to print a single term of the form [tFix mfix n] or [tCoFix mfix n].
    The parameter [is_fix] controls whether to print a fixpoint or a co-fixpoint. *)
Definition print_fixpoint (on_term : list ident -> term -> doc unit) (ctx : list ident) 
  (defs : mfixpoint term) (n : nat) (is_fix : bool) : doc unit  :=
  let prefix := if is_fix then str "let fix" else str "let cofix" in
  let sep := break 0 ^^ str "with" ^^ space in
  let on_def := 
    print_def (on_term ctx) (on_term $ push_context env (fix_context defs) ctx)
  in
  let func_name := 
    option_default 
      (fun def => print_name def.(dname).(binder_name)) 
      (List.nth_error defs n) (nat10 n) 
  in
  if Nat.ltb 1 (List.length defs)
  then align $ group $ prefix ^+^ separate_map sep on_def defs ^/^ str "for" ^+^ func_name
  else align $ group $ prefix ^+^ separate_map sep on_def defs.

(** Helper function to print a single branch (without the leading "|"). *)
Definition print_branch (on_term : list ident -> term -> doc unit) (ctx : list ident) 
  (branch : branch term) (ctor : constructor_body) : doc unit :=
  let branch_ctx := push_context env ctor.(cstr_args) ctx in
  let var_names := List.rev (firstn (List.length ctor.(cstr_args)) branch_ctx) in
  let binder := flow_map (break 2) bstr (ctor.(cstr_name) :: var_names) in
  group $ align $ binder ^+^ str "⇒" ^//^ on_term branch_ctx branch.(bbody).

Fixpoint print_term (top : bool) (ctx : list ident) (t : term) {struct t} : doc unit :=
  match t with
  | tRel n =>
    match List.nth_error ctx n with
    | Some id => bstr id
    | None => str "UnboundRel(" ^^ nat10 n ^^ str ")"
    end
  | tVar n => str "Var(" ^^ bstr n ^^ str ")"
  | tEvar ev args => 
    if Config.cf_evar_instances config then 
      let args_doc := flow_map (str ";" ^^ break 0) (print_term true ctx) args in
      str "Evar(" ^^ nat10 ev ^^ bracket "[" args_doc "]" ^^ str ")"
    else 
      str "Evar(" ^^ nat10 ev ^^ str ")"
  | tSort s => print_sort s
  | tCast c _ t => 
    let contents := print_term true ctx c ^//^ (str ":"  ^+^ print_term true ctx t) in
    paren_if top $ align $ group contents
  | tProd n ty body =>
    let n := fresh_name ctx $ base_name env n.(binder_name) (Some ty) in
    let contents :=
      (* Decide whether this is a dependent or non-dependent product. *)
      if noccur_between 0 1 body
      then [print_term false ctx ty ^+^ str "→" ; print_term true (n :: ctx) body]
      else [str "∀" ^+^ bstr n ^+^ str ":" ; 
            print_term false ctx ty ^^ str "," ; 
            print_term true (n :: ctx) body]
    in 
    paren_if top $ align $ flow (break 2) contents
  | tLambda n ty body =>
    let n := fresh_name ctx $ base_name env n.(binder_name) (Some ty) in
    let contents :=
      [str "fun" ^+^ bstr n ^+^ str ":" ; 
       print_term true ctx ty ^+^ str "⇒" ; 
       print_term true (n :: ctx) body]
    in 
    paren_if top $ align $ flow (break 2) contents
  | tLetIn n def ty body =>
    let n := fresh_name ctx $ base_name env n.(binder_name) (Some ty) in
    let n_doc := str "let" ^+^ bstr n ^+^ str ":" in
    let ty_doc := print_term true ctx ty ^+^ str ":=" in
    let def_doc := print_term true ctx def in
    let body_doc := print_term true (n :: ctx) body in
    (* Getting the formatting correct is a bit tricky. *)
    let line := group $ group (n_doc ^//^ ty_doc) ^//^ def_doc ^/^ str "in" in 
    align $ group $ line ^/^ body_doc
  | tApp f args =>
    paren_if top $ align $ flow_map (break 2) (print_term false ctx) (f :: args) 
  | tConst kname uinst => print_kername kname ^^ print_univ_instance uinst
  | tInd ind uinst =>
    let name := 
      match lookup_inductive env ind with
      | Some (_, body) => bstr body.(ind_name)
      | None => bracket "UnboundInd(" (bstr $ string_of_inductive ind) ")"
      end
    in 
    name ^^ print_univ_instance uinst
  | tConstruct ind idx uinst =>
    let name :=
      match lookup_constructor env ind idx with
      | Some (_, body) => bstr body.(cstr_name)
      | None =>
        str "UnboundCtor(" ^^ (bstr $ string_of_constructor ind idx) ^^ str ")"
      end
    in
    name ^^ print_univ_instance uinst
  | tCase ci pred x branches =>
    match lookup_inductive env ci.(ci_ind) with
    | Some (_, body) =>
        (* Print each branch separately. *)
        let branch_docs := map2 (print_branch (print_term true) ctx) branches body.(ind_ctors) in
        (* Part 1 is [match x with]. *)
        let part1 := 
          group $ str "match" ^+^ print_term true ctx x ^/^ str "with"
        in
        (* Part 2 is [C1 => ... | C2 => ... | C3 => ... end]*)
        let part2 := 
          group $ concat 
            [ break 0 ^^ ifflat empty (str "|" ^^ space)
            ; separate (break 0 ^^ str "|" ^^ space) branch_docs
            ; break 0 ^^ str "end" ]
        in
        paren_if top $ align $ part1 ^^ part2
    | None => str "CASE_ERROR"
    end
  | tFix mfix n => paren_if top $ print_fixpoint (print_term true) ctx mfix n true 
  | tCoFix mfix n => paren_if top $ print_fixpoint (print_term true) ctx mfix n false
  | tProj p t =>
    match lookup_projection env p with
    | Some (_, _, _, pbody) => 
      group $ align $ concat 
        [ print_term false ctx t
        ; ifflat empty (hardline ^^ blank 2) 
        ; str ".(" ^^ bstr pbody.(proj_name) ^^ str ")" ]
    | None =>
      let contents := 
        [ bstr (string_of_inductive p.(proj_ind)) 
        ; nat10 p.(proj_npars)
        ; nat10 p.(proj_arg) 
        ; print_term true ctx t ]
      in
      bracket "UnboundProj(" (flow (str "," ^^ break 0) contents) ")"
    end 
  | tInt i => str "Int(" ^^ bstr (string_of_prim_int i) ^^ str ")"
  | tFloat f => str "Float(" ^^ bstr (string_of_float f) ^^ str ")"
  | tString s => str "String(" ^^ str s ^^ str ")"
  | tArray u arr def ty => 
    let arr_doc := bracket "[" (flow_map (space ^^ str ";" ^^ break 0) (print_term true ctx) arr) "]" in 
    let contents := [print_level u ; arr_doc ; print_term true ctx def ; print_term true ctx ty] in
    bracket "Array(" (flow (str "," ^^ break 0) contents) ")"
  end.

(*Definition test : TemplateMonad unit :=
  mlet (env, t) <- tmQuoteRec 
    (fix add (n m : nat) {struct n} : nat :=
    match n with
    | 0 => m
    | S p => S (add p m)
    end) ;;
  let output := pp_string 80 $ print_term Config.basic (empty_ext env) true [] t in
  tmPrint =<< tmEval cbv output.
MetaCoq Run test.*)

(** [print_context_decl ctx decl] pretty-prints the context declaration [decl] in named context [ctx]. *)
Definition print_context_decl (ctx : list ident) (decl : context_decl) : doc unit :=
  let contents := 
    match decl.(decl_body) with
    | None => 
      [ print_name decl.(decl_name).(binder_name) 
      ; str ":" ^+^ print_term true ctx decl.(decl_type)]
    | Some body => 
        [ print_name decl.(decl_name).(binder_name) 
        ; str ":" ^+^ print_term true ctx decl.(decl_type)
        ; str ":=" ^+^ print_term true ctx body ]
    end
  in 
  group $ paren $ flow (break 2) contents.

(** [print_context ctx decls] prints the declarations in [decls], 
    and returns the updated named context and pretty-printed declarations (ordered from innermost to outermost). *)
Definition print_context (ctx : list ident) (decls : context) : list ident * list (doc unit) := 
  (* We process the declarations from outermost to innermost,
     while extending the named context as we go. *)
  let fix loop (ctx : list ident) (acc : list (doc unit)) (decls : list context_decl) :=
    match decls with 
    | [] => (ctx, acc)
    | d :: decls =>
      (* Generate a fresh name for the first declaration. *)
      let d_name := fresh_name ctx $ 
        base_name env d.(decl_name).(binder_name) (Some d.(decl_type)) 
      in
      (* Pretty-print the first declaration. *)
      let d_doc := print_context_decl ctx $ mkdecl 
        {| binder_name := nNamed d_name ; binder_relevance := d.(decl_name).(binder_relevance) |} 
        d.(decl_body) 
        d.(decl_type) 
      in
      (* Recurse in an extended named context. *)
      loop (d_name :: ctx) (d_doc :: acc) decls
    end
  in 
  loop ctx [] (List.rev decls).

Definition print_recursivity_kind k : doc unit :=
  match k with
  | Finite => str "Inductive"
  | CoFinite => str "CoInductive"
  | BiFinite => str "Record"
  end.

(** Helper function to print a single constructor.
    - [ctx] should contain the names of the other inductives in the block as well
      as the inductive parameters. 
    - [params] is the list of parameters (ordered from first to last) represented as 
      local variables (tRel). *)
Definition print_one_cstr (ctx : list ident) (ind : inductive) (params : list term) (ctor : constructor_body) : doc unit :=
  (* TODO : handle universes for [tInd]. *)
  let n_args := List.length ctor.(cstr_args) in
  let ctor_ty := 
    it_mkProd_or_LetIn ctor.(cstr_args) $ 
    mkApps (tInd ind []) $ 
    (List.map (lift0 n_args) params) ++ ctor.(cstr_indices) 
  in
  align $ group $ bstr ctor.(cstr_name) ^+^ str ":" ^//^ print_term true ctx ctor_ty.

(** Helper function to print a single inductive.
    - [header] is the keyword which should be printed before the inductive name 
      (usually it is [Inductive] or [with]).
    - [ctx] should contain the names of the other inductives in the block. *)
Definition print_one_ind (header : doc unit) (short : bool) (ctx : list ident) 
  (mbody : mutual_inductive_body) (body : one_inductive_body) (ind : inductive) : doc unit :=
  let '(ctx_params, param_docs) := print_context ctx mbody.(ind_params) in
  let params := List.rev (mapi (fun i _ => tRel i) mbody.(ind_params)) in
  let arity := it_mkProd_or_LetIn body.(ind_indices) (tSort body.(ind_sort)) in
  (* part1 is [ind_name@{univs} params : arity :=]*)
  let part1 := flow (break 2) $ 
    header ::
    (bstr body.(ind_name) ^^ print_univ_decl (snd env)) ::
    List.rev param_docs ++
    [ str ":"
    ; print_term true ctx_params arity
    ; str ":=" ]
  in 
  (* part2 is [C1 : ... | C2 : ... | C2 : ...] *)
  let part2 := 
    ifflat empty (str "|" ^^ space) ^^
    separate_map (break 0 ^^ str "|" ^^ space) (print_one_cstr ctx_params ind params) body.(ind_ctors)
  in
  align $ flow (break 0) [part1 ; if short then str "..." else part2].

(*Definition print_one_cstr_entry Γ (mie : mutual_inductive_entry) (c : ident × term) : t :=
  c.1 ^ " : " ^ print_term Γ true c.2.

Definition print_one_ind_entry (short : bool) Γ (mie : mutual_inductive_entry) (oie : one_inductive_entry) : t :=
  let '(Γpars, spars) := print_context Γ mie.(mind_entry_params) in
  oie.(mind_entry_typename) ^ spars ^ print_term Γpars true oie.(mind_entry_arity) ^ ":=" ^ nl ^
  if short then "..."
  else print_list (print_one_cstr_entry Γpars mie) nl (combine oie.(mind_entry_consnames) oie.(mind_entry_lc)).*)

End Env.

(** Print a mutual inductive block. *)
Definition print_mutual_inductive (env : global_env) (short : bool) (ind_kname : kername) 
  (mbody : mutual_inductive_body) : doc unit :=
  let ext_env := (env, mbody.(ind_universes)) in
  let ctx := push_context ext_env (arities_context mbody.(ind_bodies)) [] in
  align $ group $ 
    separate (break 0) $ mapi 
      (fun i body => 
        let header := if i == 0 then print_recursivity_kind mbody.(ind_finite) else str "with" in
        print_one_ind ext_env header short ctx mbody body (mkInd ind_kname i))
      mbody.(ind_bodies).
  
(** Print a constant. *)
Definition print_constant (env : global_env) (short : bool) (kname : kername) 
  (cst : constant_body) : doc unit :=
  let ext_env := (env, cst.(cst_universes)) in
  let ctx := [] in
  let header := 
    match cst.(cst_body) with 
    | Some _ => str "Definition" 
    | None => str "Axiom" 
    end
  in
  let body :=
    if short then group $ str ":=" ^/^ str "..." else 
    match cst.(cst_body) with 
    | Some body => group $ str ":=" ^/^ print_term ext_env true ctx body
    | None => empty 
    end
  in
  align $ flow (break 2)
    [ header ; (print_kername kname ^^ print_univ_decl cst.(cst_universes))
    ; str ":" ; print_term ext_env true ctx cst.(cst_type) 
    ; body ].
  
(** Print all the declarations in a global environment. *)
Definition print_env (env : global_env) (short : bool) : doc unit :=
  let fix loop decls acc :=
    match decls with 
    | [] => separate (hardline ^^ if short then empty else hardline) acc
    | (kname, decl) :: decls =>
      let doc := 
        match decl with 
        | ConstantDecl cst => print_constant env short kname cst 
        | InductiveDecl mbody => print_mutual_inductive env short kname mbody
        end
      in 
      loop decls (doc :: acc)
    end 
  in 
  loop env.(declarations) [].

End Printing.

(**********)
(* Testing. *)

(*From MetaCoq.Template Require Import TemplateMonad Loader.
Import MCMonadNotation.

Definition test_env : TemplateMonad unit :=
  mlet (env, _) <- tmQuoteRec term ;;
  tmPrint =<< tmEval cbv $ 
    pp_string 80 $ print_env Config.default env false.

(* TODO : use precedences *)
(* TODO : make [short] into a config option. maybe [skip_definitions] ?*)
(* TODO : group lambdas and products together *)

(*Definition test_ind : TemplateMonad unit :=
  mlet (env, ind) <- tmQuoteRec Even ;;
  mlet ind <- 
    match ind with 
    | tInd ind _ => ret ind 
    | _ => tmFail "not an inductive"%bs
    end
  ;;
  mlet (mbody, body) <- 
    match lookup_inductive env ind with
    | Some res => ret res 
    | None => tmFail "lookup_inductive failed"%bs
    end
  ;;
  tmPrint =<< tmEval cbv $ pp_string 80 $ 
    print_mutual_inductive (Config.with_universes Config.default) env false ind.(inductive_mind) mbody.*)

Definition mydef (env : global_env) (inst : Instance.t) (short : bool) (kname : kername) 
  (cst : constant_body) : doc unit :=
  let ext_env := (env, cst.(cst_universes)) in
  let ctx : list ident := [] in 
  @empty unit. 

Definition test_cst : TemplateMonad unit :=
  mlet (env, cst) <- tmQuoteRec mydef ;;
  mlet kname <- 
    match cst with 
    | tConst kname _ => ret kname 
    | _ => tmFail "not a constant"%bs
    end
  ;;
  mlet cst <- 
    match lookup_constant env kname with
    | Some res => ret res 
    | None => tmFail "lookup_constant failed"%bs
    end
  ;;
  tmPrint =<< tmEval cbv $ pp_string 80 $ 
    print_constant (Config.all) env false kname cst.*)
