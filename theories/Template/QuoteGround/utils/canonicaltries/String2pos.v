From MetaCoq.Lob.Template.QuoteGround Require Export Coq.Init.
From MetaCoq.Template.utils.canonicaltries Require Import String2pos.

#[export] Instance quote_positive : ground_quotable positive := ltac:(induction 1; exact _).
