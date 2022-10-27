From MetaCoq.Lob.Template.QuoteGround Require Export Coq.Init.
From Coq.ssr Require Import ssrbool.

#[export] Instance quote_if_spec {A b vT vF} {not_b:Prop} {b' a} {qA : quotation_of A} {qvT : quotation_of vT} {qvF : quotation_of vF} {qnot_b : quotation_of not_b} {quote_not_b : ground_quotable not_b} : ground_quotable (@if_spec A b vT vF not_b b' a) := ltac:(destruct 1; exact _).
Print alt_spec.
#[export] Instance quote_if_spec {A b vT vF} {not_b:Prop} {b' a} {qA : quotation_of A} {qvT : quotation_of vT} {qvF : quotation_of vF} {qnot_b : quotation_of not_b} {quote_not_b : ground_quotable not_b} : ground_quotable (@if_spec A b vT vF not_b b' a) := ltac:(destruct 1; exact _).
Variant alt_spec : bool -> Type :=
Variant implies P Q := Implies of P -> Q.
Inductive and3 (P1 P2 P3 : Prop) : Prop := And3 of P1 & P2 & P3.
Inductive and4 (P1 P2 P3 P4 : Prop) : Prop := And4 of P1 & P2 & P3 & P4.
Inductive and5 (P1 P2 P3 P4 P5 : Prop) : Prop :=
Inductive or3 (P1 P2 P3 : Prop) : Prop := Or31 of P1 | Or32 of P2 | Or33 of P3.
Inductive or4 (P1 P2 P3 P4 : Prop) : Prop :=
(** Variant of simpl_pred specialised to the membership operator. **)
Variant mem_pred T := Mem of pred T.
Variant qualifier (q : nat) T := Qualifier of {pred T}.
Variant pred_key (p : {pred T}) : Prop := DefaultPredKey.
Inductive external_view : Type := tactic_view of Type.
Variant put vT sT (v1 v2 : vT) (s : sT) : Prop := Put.
  Inductive indt_type (p : p_str) := Indt ... .
Variant phantom T (p : T) : Prop := Phantom.
Variant phant (p : Type) : Prop := Phant.
 construction of dependent Records and Structures. For example, if we need
    Record r := R {x; y : T(x)}.
Variant simpl_fun (aT rT : Type) := SimplFun of aT -> rT.
Variant bijective : Prop := Bijective g of cancel f g & cancel g f.

Locate and4.
