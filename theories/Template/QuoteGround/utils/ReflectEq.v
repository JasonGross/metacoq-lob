From MetaCoq.Lob.Template.QuoteGround Require Export Coq.Init.
From MetaCoq.Template.utils Require Import ReflectEq.

#[export] Instance quote_reflectProp {A:Prop} {qA : quotation_of A} {quoteA : ground_quotable A} {quote_negA : ground_quotable (~A)} {b} : ground_quotable (@reflectProp A b).
Proof.
  destruct b; adjust_ground_quotable_by_econstructor_inversion ().
Defined.
