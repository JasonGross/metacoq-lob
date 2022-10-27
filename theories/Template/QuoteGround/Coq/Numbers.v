Require Import Coq.Numbers.BinNums.
From MetaCoq.Lob.Template Require Export QuoteGround.Coq.Init.

#[export] Instance quote_positive : ground_quotable positive := ltac:(induction 1; exact _).
#[export] Instance quote_N : ground_quotable N := ltac:(induction 1; exact _).
#[export] Instance quote_Z : ground_quotable Z := ltac:(induction 1; exact _).
