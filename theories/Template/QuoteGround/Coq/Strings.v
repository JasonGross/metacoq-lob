Require Import Coq.Strings.String Coq.Strings.Ascii.
From MetaCoq.Lob.Template Require Export QuoteGround.Coq.Init.

#[export] Instance quote_ascii : ground_quotable Ascii.ascii := (ltac:(induction 1; exact _)).
#[export] Instance quote_string : ground_quotable string := (ltac:(induction 1; exact _)).
