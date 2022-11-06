From MetaCoq.Template Require Import Ast Typing TypingWf.

(* XXX TODO How to encapsulate safe global environment and context? *)
Local Set Primitive Projections.
Record env := { env_ :> global_env_ext ; checker_flags_ :> config.checker_flags  }.
Existing Class env.
#[export] Existing Instance checker_flags_.
Record context {Σ : env} :=
  { context_ :> Ast.Env.context ; context_wf_local : wf_local Σ context_ }.
Record sort {Σ : env} :=
  { sort_ :> Universe.t ; sort_wf : wf_universe Σ sort_ }.
Record type {Σ : env} (Γ : context) (s : sort) :=
  { type_ :> Ast.term ; type_well_typed : Σ ;;; Γ |- type_ : tSort s }.
Record term {Σ : env} {Γ : context} {s : sort} (T : type Γ s) :=
  { term_ :> Ast.term ; term_well_typed : Σ ;;; Γ |- term_ : T }.
