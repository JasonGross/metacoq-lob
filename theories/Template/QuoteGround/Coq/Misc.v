Require Import Coq.Lists.List.
From MetaCoq.Lob.Template Require Export QuoteGround.Coq.Init.
Import ListNotations.

Local Notation iffT A B := (prod (A -> B) (B -> A)).
Lemma iff_forall_eq_some {A v P} : iffT match v return Type with Some v => P v | None => True end (forall a : A, v = Some a -> P a).
Proof.
  split; destruct v; auto; intros ??; inversion 1; subst; assumption.
Defined.
Lemma iff_forall_neq_nil {A} {v : list A} {P} : iffT match v return Type with nil => True | _ => P end (v <> nil -> P).
Proof.
  split; destruct v; intuition congruence.
Defined.
#[export] Instance quote_forall_eq_some {A v P} {q : ground_quotable (match v return Type with Some v => P v | None => True end)} {qv : quotation_of v} {qA : quotation_of A} {qP : quotation_of P} : ground_quotable (forall a : A, v = Some a -> P a)
  := quote_of_iffT iff_forall_eq_some.
#[export] Instance quote_forall_neq_nil {A v P} {q : ground_quotable (match v return Type with nil => True | _ => P end)} {qv : quotation_of v} {qA : quotation_of A} {qP : quotation_of P} : ground_quotable (v <> @nil A -> P)
  := quote_of_iffT iff_forall_neq_nil.
#[export] Instance quote_is_true_or_l {b} {P : Prop} {qP : quotation_of P} {quoteP : ground_quotable P} : ground_quotable (is_true b \/ P).
Proof.
  apply quote_or_dec_l; try exact _; cbv [is_true]; decide equality.
Defined.
#[export] Instance quote_is_true_or_r {b} {P : Prop} {qP : quotation_of P} {quoteP : ground_quotable P} : ground_quotable (P \/ is_true b).
Proof.
  apply quote_or_dec_r; try exact _; cbv [is_true]; decide equality.
Defined.
