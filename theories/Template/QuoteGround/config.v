From MetaCoq.Lob.Template.QuoteGround Require Export Coq.Init.
From MetaCoq.Template Require Import config.

#[export] Instance quote_checker_flags : ground_quotable checker_flags := ltac:(destruct 1; exact _).
