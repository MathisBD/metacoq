(* Distributed under the terms of the MIT license. *)

From MetaCoq.Utils Require Import utils.
From MetaCoq.Common Require Import BasicAst.
From MetaCoq.Template Require Import Ast AstUtils Typing.

(** This file provides utilities to manipulate named variables and
    named contexts. *)

(** Fresh name in a named context. TODO *)
Definition fresh_in_nctx (id : ident) (nctx : named_context) : ident.
Admitted.

(** [abstract id t] replaces every occurence of [id] in [t] by [tRel 0].
    TODO *)
Definition abstract (id : ident) (t : term) : term. 
Admitted.

Definition with_local_decl.
Definition lambda.
Definition prod.

