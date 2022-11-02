From MetaCoq.Lob.Template.QuoteGround Require Export Ast WfAst.
From MetaCoq.Template Require Import TypingWf.

#[export] Instance quote_wf_inductive_body {Σ idecl} : ground_quotable (@wf_inductive_body Σ idecl) := ltac:(destruct 1; exact _).
