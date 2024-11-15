(* Distributed under the terms of the MIT license. *)

(** This file defines a unification algorithm. It is intended for practical use 
    and is not verified. *)

From Coq.FSets Require Import FMapAVL.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import Ast AstUtils TemplateEnvMap.

Unset Guard Checking.

(** * Evar map. *)

Module EvarMap.

(** [NatMap T] are maps from natural numbers to elements of type [T]. *)
(** TODO : use binary numbers (or even primitive integers) instead of nats for the keys. *)
Module NatMap := FMapAVL.Make (OrderedTypeEx.Nat_as_OT).

(** An evar entry in the evar map. *)
Definition entry := context_decl.

(** An evar map is a map from evar identifiers to entries. *)
Definition t := NatMap.t entry.

(** The empty evar map. *)
Definition empty : t := @NatMap.empty entry.

(** [evar_def evm ev] retrieves the definition of evar [ev] in the evar map [evm]. *)
Definition evar_def evm ev : option term :=
  match NatMap.find ev evm with 
  | None => None 
  | Some entry => entry.(decl_body)
  end. 

End EvarMap.

(** [instantiate_all evm t] replaces all defined evars that appear in [t] 
    by their body. *)
Definition instantiate_all (evm : EvarMap.t) (t : term) : term. 
(* TODO : use map_term. *)
Admitted.

(** [instantiate_head evm t] expands evars just enough to expose the first 
    constructor which is not [tEvar] in [t].. *)
Fixpoint instantiate_head (evm : EvarMap.t) (t : term) : term :=
  match t with 
  | tEvar ev inst =>
    match EvarMap.evar_def evm ev with 
    | None => t 
    | Some def => instantiate_head evm $ def{inst}
    end
  | _ => t 
  end.

(** * Unification errors. *)

(** TODO *)
Inductive unif_error := 
  | AssertionFailure : string -> unif_error.

(** Unification returns a [unif_result]. *)
Inductive unif_result A : Type := 
  (** [Success x] : unification succeeded with result [x] (typically the updated evar map). *)
  | Success : A -> unif_result A
  (** [UnifError err] : unification failed with error [err]. *)
  | UnifError : unif_error -> unif_result A.
Arguments Success {A}%_type_scope a.
Arguments UnifError {A}%_type_scope error.

(** * Logging. *)

(*Module Log.

(** A log element contains the data pertaining to a single unification problem. *)
Record elem := mkelem 
  { (** Did this unification problem succeed ? *) 
    le_success : bool  
  ; (** The first term we are unifying. *)
    le_t1 : term 
  ; (** The second term we are unifying. *)
    le_t2 : term
  ; (** The conversion problem. *)
    le_pb : conv_pb }.

Definition t := list elem.

(** The empty log. *)
Definition empty : t := [].

Definition concat (l l' : t) : t := List.app l l'.

End Log.*)

(** * Utilities. *)

(** A convenient notation for function application, which saves many parentheses. *)
Notation "f $ x" := (f x) 
  (at level 10, x at level 100, right associativity, only parsing).

(** Monadic return. *)
Definition ret {A} (a : A) : unif_result A := Success a.

(** Monadic bind. *)
Definition bind {A} {B} (ma : unif_result A) (mf : A -> unif_result B) : unif_result B :=
  match ma with 
  | Success a => mf a 
  | UnifError err => UnifError err
  end.
Notation "'let*' x := c1 'in' c2" := (bind c1 (fun x => c2))
  (at level 100, x ident, c1 at next level, right associativity).

(** Monadic alternative. *)
Definition msum {A} (x y : unif_result A) : unif_result A :=
  match x with 
  | Success _ => x 
  | UnifError _ => y
  end.
Notation "x <|> y" := (msum x y) (at level 85, right associativity).

(*Definition assert (msg : string) s (cond : bool) : state :=
  if cond then s 
  else (s.1, UnifFailure (AssertionFailure msg)).*)

(** * Unification algorithm. *)

Section Algorithm.
Context (env : global_env).


Definition destruct_app evm (t : term) : term * list term :=
  match EvarMap.head evm t with
  | tApp f args => (f, args)
  | _ => (t, [])
  end.

Fixpoint decompose_evar (evm : EvarMap.t) (t : term * list term) : term * list term :=
  let 

(**  (** Given a head term c and with arguments l it whd reduces c if it is
      an evar, returning the new head and list of arguments.
  *)
  let rec decompose_evar sigma (c, l) =
    let (c', l') = decompose_app_list sigma c in
    if isCast sigma c' then
      let (t, _, _) = destCast sigma c' in
      decompose_evar sigma (t, l' @ l)
    else
      (c', l' @ l)
*)

Fixpoint unify_without_step pb s (t t' : term * list term) log evm : state :=
  (*let&& log evm := assert $ negb $ isApp evm t.1 in
  let&& log evm := assert $ negb $ isApp evm t'.1 in *)
  


(** Main unification function entry point. *)
Definition unify_constr (pb : conv_pb) (t1 t2 : term) (s : state) : state := 
  let (log, evm) := s in
  unify pb (decompose_app_list evm t1) (decompose_app_list evm t2) s.