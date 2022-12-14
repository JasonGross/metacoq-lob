From MetaCoq.Lob.Template.QuoteGround Require Export Coq.Init.
From MetaCoq.Template.utils Require Import MCOption.

#[local] Hint Extern 0 => reflexivity : typeclass_instances.

#[export] Instance quote_ForOption {A P o} {qA : quotation_of A} {qP : quotation_of P} {qo : quotation_of o} {quoteP : forall t, o = Some t -> ground_quotable (P t:Prop)} : ground_quotable (@ForOption A P o).
Proof.
  destruct o; adjust_ground_quotable_by_econstructor_inversion (); eauto.
Defined.

#[export] Instance quote_option_extends {A o1 o2} {qA : quotation_of A} {qo1 : quotation_of o1} {qo2 : quotation_of o2} {quoteA : forall t, o2 = Some t -> quotation_of t} : ground_quotable (@option_extends A o1 o2).
Proof.
  destruct o1 as [a|], o2 as [a'|].
  all: try specialize (quoteA _ eq_refl).
  all: try solve [ intro pf; exfalso; inversion pf ].
  all: try (intro pf; assert (a = a') by (now inversion pf); subst;
            let t := type of pf in
            revert pf; change (ground_quotable t)).
  all: adjust_ground_quotable_by_econstructor_inversion ().
Defined.

#[export] Polymorphic Instance quote_option_default {A P o b} {quoteP : forall x, o = Some x -> ground_quotable (P x)} {quoteP' : o = None -> ground_quotable b} : ground_quotable (@option_default A Type P o b) := ltac:(destruct o; exact _).

#[export] Instance quote_on_Some {A P o} {quoteP : forall x, o = Some x -> ground_quotable (P x:Prop)} : ground_quotable (@on_Some A P o) := ltac:(destruct o; exact _).
#[export] Instance quote_on_Some_or_None {A P o} {quoteP : forall x, o = Some x -> ground_quotable (P x:Prop)} : ground_quotable (@on_Some_or_None A P o) := ltac:(destruct o; exact _).
