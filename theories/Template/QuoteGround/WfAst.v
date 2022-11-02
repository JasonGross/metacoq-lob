From MetaCoq.Lob.Template.QuoteGround Require Export config utils Ast AstUtils Induction UnivSubst.
From MetaCoq.Template Require Import Ast WfAst.

#[export] Instance quote_wf {Σ t} : ground_quotable (@wf Σ t).
Proof.
  cbv [ground_quotable]; revert t.
  fix quote_wf 2; change (forall t, ground_quotable (@wf Σ t)) in quote_wf.
  intro t; destruct 1; exact _.
Defined.

#[export] Instance quote_wf_Inv {Σ t} : ground_quotable (@wf_Inv Σ t) := ltac:(cbv [wf_Inv]; exact _).
#[export] Instance quote_wf_decl {Σ d} : ground_quotable (@wf_decl Σ d) := ltac:(cbv [wf_decl]; exact _).
Import StrongerInstances.
#[export] Instance quote_wf_decl_pred {Σ Γ t T} : ground_quotable (@wf_decl_pred Σ Γ t T) := ltac:(cbv [wf_decl_pred]; exact _).
