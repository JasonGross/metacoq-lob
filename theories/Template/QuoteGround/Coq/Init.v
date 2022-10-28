Require Import Coq.Lists.List.
From MetaCoq.Lob.Template Require Export QuoteGround.Init.
Import ListNotations.

Export QuoteGround.Init.Instances.

#[export] Instance quote_True : ground_quotable True := ltac:(destruct 1; exact _).
#[export] Instance quote_False : ground_quotable False := ltac:(destruct 1; exact _).
#[export] Instance quote_byte : ground_quotable Byte.byte := ltac:(destruct 1; exact _).
#[export] Instance quote_Empty_set : ground_quotable Empty_set := ltac:(destruct 1; exact _).
#[export] Instance quote_unit : ground_quotable unit := ltac:(destruct 1; exact _).
#[export] Instance quote_bool : ground_quotable bool := ltac:(destruct 1; exact _).

#[export] Instance quote_eq {A} {qA : quotation_of A} {qA : ground_quotable A} {x y : A} : ground_quotable (x = y :> A) := (ltac:(intros []; exact _)).

Definition ground_quotable_of_bp {b P} (H : b = true -> P) {qH : quotation_of H} (H_for_safety : P -> b = true) : ground_quotable P.
Proof.
  intro p.
  exact (Ast.mkApps qH [_ : quotation_of (@eq_refl bool true)]).
Defined.

Definition ground_quotable_neg_of_bp {b P} (H : b = false -> ~P) {qH : quotation_of H} (H_for_safety : ~P -> b = false) : ground_quotable (~P).
Proof.
  intro p.
  exact (Ast.mkApps qH [_ : quotation_of (@eq_refl bool false)]).
Defined.

Definition b_of_dec {P} (H : {P} + {~P}) : bool := if H then true else false.
Definition bp_of_dec {P H} : @b_of_dec P H = true -> P.
Proof. cbv [b_of_dec]; destruct H; auto; discriminate. Defined.
Definition pb_of_dec {P:Prop} {H} : P -> @b_of_dec P H = true.
Proof. cbv [b_of_dec]; destruct H; auto; discriminate. Defined.
Definition neg_bp_of_dec {P H} : @b_of_dec P H = false -> ~P.
Proof. cbv [b_of_dec]; destruct H; auto; discriminate. Defined.
Definition neg_pb_of_dec {P:Prop} {H} : ~P -> @b_of_dec P H = false.
Proof. cbv [b_of_dec]; destruct H; tauto. Defined.

Definition ground_quotable_of_dec {P} (H : {P} + {~P}) {qP : quotation_of P} {qH : quotation_of H} : ground_quotable P
  := ground_quotable_of_bp bp_of_dec pb_of_dec.
Definition ground_quotable_neg_of_dec {P} (H : {P} + {~P}) {qP : quotation_of P} {qH : quotation_of H} : ground_quotable (~P)
  := ground_quotable_neg_of_bp neg_bp_of_dec neg_pb_of_dec.

#[export] Instance quote_eq_true {b} : ground_quotable (eq_true b) := ltac:(destruct 1; exact _).
#[export] Instance quote_BoolSpec {P Q : Prop} {b} {qP : quotation_of P} {qQ : quotation_of Q} {quoteP : ground_quotable P} {quoteQ : ground_quotable Q} : ground_quotable (BoolSpec P Q b).
Proof.
  destruct b; adjust_ground_quotable_by_econstructor_inversion ().
Defined.
#[export] Instance quote_nat : ground_quotable nat := ltac:(induction 1; exact _).
#[export] Instance quote_option {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (option A) := (ltac:(induction 1; exact _)).
#[export] Instance quote_sum {A B} {qA : quotation_of A} {qB : quotation_of B} {quoteA : ground_quotable A} {quoteB : ground_quotable B} : ground_quotable (sum A B) := (ltac:(induction 1; exact _)).
#[export] Instance quote_prod {A B} {qA : quotation_of A} {qB : quotation_of B} {quoteA : ground_quotable A} {quoteB : ground_quotable B} : ground_quotable (prod A B) := (ltac:(induction 1; exact _)).
#[export] Instance quote_list {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (list A) := (ltac:(induction 1; exact _)).
#[export] Instance quote_comparison : ground_quotable comparison := ltac:(destruct 1; exact _).
#[export] Instance quote_CompareSpec {Peq Plt Pgt : Prop} {qPeq : quotation_of Peq} {qPlt : quotation_of Plt} {qPgt : quotation_of Pgt} {quote_Peq : ground_quotable Peq} {quote_Plt : ground_quotable Plt} {quote_Pgt : ground_quotable Pgt} {c} : ground_quotable (CompareSpec Peq Plt Pgt c).
Proof.
  destruct c; adjust_ground_quotable_by_econstructor_inversion ().
Defined.
#[export] Instance quote_CompareSpecT {Peq Plt Pgt : Prop} {qPeq : quotation_of Peq} {qPlt : quotation_of Plt} {qPgt : quotation_of Pgt} {quote_Peq : ground_quotable Peq} {quote_Plt : ground_quotable Plt} {quote_Pgt : ground_quotable Pgt} {c} : ground_quotable (CompareSpecT Peq Plt Pgt c) := ltac:(destruct 1; exact _).
Module Decimal.
  #[export] Instance quote_uint : ground_quotable Decimal.uint := ltac:(induction 1; exact _).
  #[export] Instance quote_neq_uint {x y} : ground_quotable (x <> y :> Decimal.uint) := ground_quotable_neg_of_dec (@Decimal.uint_eq_dec x y).
End Decimal.
#[export] Existing Instances Decimal.quote_uint Decimal.quote_neq_uint.
Module Hexadecimal.
  #[export] Instance quote_uint : ground_quotable Hexadecimal.uint := ltac:(induction 1; exact _).
  #[export] Instance quote_neq_uint {x y} : ground_quotable (x <> y :> Hexadecimal.uint) := ground_quotable_neg_of_dec (@Hexadecimal.uint_eq_dec x y).
End Hexadecimal.
#[export] Existing Instances Hexadecimal.quote_uint Hexadecimal.quote_neq_uint.
Module Number.
  #[export] Instance quote_uint : ground_quotable Number.uint := ltac:(induction 1; exact _).
  #[export] Instance quote_neq_uint {x y} : ground_quotable (x <> y :> Number.uint) := ground_quotable_neg_of_dec (@Number.uint_eq_dec x y).
End Number.
#[export] Existing Instances Number.quote_uint Number.quote_neq_uint.
#[export] Instance quote_and {A B : Prop} {qA : quotation_of A} {qB : quotation_of B} {quoteA : ground_quotable A} {quoteB : ground_quotable B} : ground_quotable (A /\ B) := (ltac:(destruct 1; exact _)).

#[export] Instance quote_le {n m} : ground_quotable (le n m) := ground_quotable_of_dec (Compare_dec.le_dec n m).

#[export] Instance quote_sig {A} {P : A -> Prop} {qA : quotation_of A} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteP : forall x, quotation_of x -> ground_quotable (P x)} : ground_quotable (@sig A P) := (ltac:(induction 1; exact _)).
#[export] Instance quote_sig2 {A} {P Q : A -> Prop} {qA : quotation_of A} {qP : quotation_of P} {qQ : quotation_of Q} {quoteA : ground_quotable A} {quoteP : forall x, quotation_of x -> ground_quotable (P x)} {quoteQ : forall x, quotation_of x -> ground_quotable (Q x)} : ground_quotable (@sig2 A P Q) := (ltac:(induction 1; exact _)).
#[export] Instance quote_sigT {A P} {qA : quotation_of A} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteP : forall x, quotation_of x -> ground_quotable (P x)} : ground_quotable (@sigT A P) := (ltac:(induction 1; exact _)).
#[export] Instance quote_sigT2 {A} {P Q} {qA : quotation_of A} {qP : quotation_of P} {qQ : quotation_of Q} {quoteA : ground_quotable A} {quoteP : forall x, quotation_of x -> ground_quotable (P x)} {quoteQ : forall x, quotation_of x -> ground_quotable (Q x)} : ground_quotable (@sigT2 A P Q) := (ltac:(induction 1; exact _)).
#[export] Instance quote_sumbool {A B : Prop} {qA : quotation_of A} {qB : quotation_of B} {quoteA : ground_quotable A} {quoteB : ground_quotable B} : ground_quotable (sumbool A B) := ltac:(destruct 1; exact _).
#[export] Instance quote_sumor {A} {B : Prop} {qA : quotation_of A} {qB : quotation_of B} {quoteA : ground_quotable A} {quoteB : ground_quotable B} : ground_quotable (sumor A B) := ltac:(destruct 1; exact _).

(* TODO: Move *)
Local Notation iffT A B := (prod (A -> B) (B -> A)).
Definition quote_of_iffT {A B} {quoteA : ground_quotable A} {qA : quotation_of A} {qB : quotation_of B} (H : iffT A B) {qH : quotation_of H} : ground_quotable B.
Proof.
  intro b.
  change (@quotation_of B (fst H (snd H b))).
  exact _.
Defined.
(* Transparent versions *)
Definition proj1 {A B} (x : A /\ B) : A := ltac:(apply x).
Definition proj2 {A B} (x : A /\ B) : B := ltac:(apply x).
Definition quote_of_iff {A B : Prop} {quoteA : ground_quotable A} {qA : quotation_of A} {qB : quotation_of B} (H : iff A B) {qH : quotation_of H} : ground_quotable B.
Proof.
  intro b.
  change (@quotation_of B (proj1 H (proj2 H b))).
  exact _.
Defined.
Definition quote_neg_of_iffT {A B} {quoteA : ground_quotable (A -> False)} {qA : quotation_of A} {qB : quotation_of B} (H : iffT A B) {qH : quotation_of H} : ground_quotable (B -> False).
Proof.
  intro nb.
  assert (na : A -> False) by (intro a; apply nb, H, a).
  change (@quotation_of (B -> False) (fun b => na (snd H b))).
  exact _.
Defined.
Definition quote_neg_of_iff {A B : Prop} {quoteA : ground_quotable (~A)} {qA : quotation_of A} {qB : quotation_of B} (H : iff A B) {qH : quotation_of H} : ground_quotable (~B).
Proof.
  intro nb.
  assert (na : ~A) by (intro a; apply nb, H, a).
  change (@quotation_of (~B) (fun b => na (proj2 H b))).
  exact _.
Defined.

Definition quote_or_dec_l {P Q : Prop} (decP : {P} + {~P}) {qP : quotation_of P} {qQ : quotation_of Q} {quoteP : ground_quotable P} {quoteQ : ground_quotable Q} : ground_quotable (or P Q).
Proof.
  destruct decP.
  all: intro pf; adjust_quotation_of_by_econstructor_then ltac:(fun _ => destruct pf; first [ eassumption | tauto ]) ltac:(fun _ => exact _).
Defined.
Definition quote_or_dec_r {P Q : Prop} (decQ : {Q} + {~Q}) {qP : quotation_of P} {qQ : quotation_of Q} {quoteP : ground_quotable P} {quoteQ : ground_quotable Q} : ground_quotable (or P Q).
Proof.
  destruct decQ.
  all: intro pf; adjust_quotation_of_by_econstructor_then ltac:(fun _ => destruct pf; first [ eassumption | tauto ]) ltac:(fun _ => exact _).
Defined.

(* These are not possible *)
(*
#[export] Instance quote_or : ground_quotable or := ltac:(destruct 1; exact _). (A B:Prop) : Prop :=
#[export] Instance quote_ex : ground_quotable ex := ltac:(destruct 1; exact _). (A:Type) (P:A -> Prop) : Prop :=
#[export] Instance quote_ex2 : ground_quotable ex2 := ltac:(destruct 1; exact _). (A:Type) (P Q:A -> Prop) : Prop :=
#[export] Instance quote_inhabited : ground_quotable inhabited := ltac:(destruct 1; exact _). (A:Type) : Prop := inhabits : A -> inhabited A.
*)

#[export] Instance quote_neq_True {x y : True} : ground_quotable (x <> y).
Proof. destruct x, y; intro; exfalso; congruence. Defined.
#[export] Instance quote_neq_False {x y : False} : ground_quotable (x <> y) := ltac:(destruct x).
#[export] Instance quote_neq_byte {x y} : ground_quotable (x <> y :> Byte.byte) := ground_quotable_neg_of_dec (@Byte.byte_eq_dec x y).
#[export] Instance quote_neq_Empty_set {x y : Empty_set} : ground_quotable (x <> y) := ltac:(destruct x).
#[export] Instance quote_neq_unit {x y : unit} : ground_quotable (x <> y).
Proof. destruct x, y; intro; exfalso; congruence. Defined.
#[export] Instance quote_neq_bool {x y} : ground_quotable (x <> y :> bool) := ground_quotable_neg_of_dec (@Bool.bool_dec x y).
#[export] Instance quote_neq_nat {x y} : ground_quotable (x <> y :> nat) := ground_quotable_neg_of_dec (@PeanoNat.Nat.eq_dec x y).
Scheme Equality for comparison.
#[export] Instance quote_neq_comparison {x y} : ground_quotable (x <> y :> comparison) := ground_quotable_neg_of_dec (@comparison_eq_dec x y).

#[export] Instance quote_nle {n m} : ground_quotable (~le n m) := ground_quotable_neg_of_dec (Compare_dec.le_dec n m).
