From MetaCoq.Lob.Template.QuoteGround Require Export Coq.Init.
From MetaCoq.Template Require Import Primitive.

#[export] Instance quote_prim_tag : ground_quotable prim_tag := ltac:(destruct 1; exact _).
