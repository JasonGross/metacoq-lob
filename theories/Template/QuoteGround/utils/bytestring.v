From MetaCoq.Lob.Template.QuoteGround Require Export Coq.Init.
From MetaCoq.Template.utils Require Import bytestring.

Module String.
  #[export] Instance quote_t : ground_quotable String.t := ltac:(induction 1; exact _).
End String.
#[export] Existing Instance String.quote_t.
Notation quote_bs := String.quote_t.
Notation quote_string := String.quote_t.

Module Tree.
  #[export] Instance quote_t : ground_quotable Tree.t := ltac:(induction 1; exact _).
End Tree.
#[export] Existing Instance Tree.quote_t.
