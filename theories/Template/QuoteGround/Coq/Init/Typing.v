Require Import Coq.Lists.List.
From MetaCoq.Template Require Export Typing utils.bytestring.
From MetaCoq.Lob.Template.QuoteGround Require Export Coq.Init.
From MetaCoq.Lob.Util.Tactics Require Import
     Head
.
Import ListNotations.

#[export] Instance quote_True_well_typed : ground_quotable_well_typed True.
Proof.
  intro t; destruct t; hnf.
  intros.
  vm_compute quote_ground.
  repeat match goal with
         | [ |- _ ;;; _ |- ?t : _ ]
           => let h := head t in
              is_constructor h;
              econstructor
         end.
  all: cbn.
  2: {
    cbv [Ast.declared_constructor Ast.declared_inductive Ast.declared_minductive]; cbn. (*
    Print Ast.Env.InductiveDecl.
    Locate global_decl.
    Print Ast.Env.mutual_inductive_body.
    Print Template.Universes.universes_decl.
    Print Template.Universes.ConstraintSet.Equal.

    Search Ast.Env.global_decl.
    cbn.
    cbv [].
    cbn.
    cbv [].
    cbn.
    Import Template.All.
    Import MCMonadNotation.
    pose (let t := True in
          qt <- tmQuote t;;
          mind <- match qt with
                  | tInd {| inductive_mind := mind |} _ => ret mind
                  | _ => tmPrint ("ensure present not inductive"%bs, qt);; tmFail "ensure present not inductive"%bs
                  end;;
          ind <- tmQuoteInductive mind;;
          tmPrint ind;;
          ret (fun Σ : global_env_ext
               => match lookup_env Σ.1 mind with
                  | Some (InductiveDecl mdecl)
                    => true
                  | _ => false
                  end)) as p.
    run_template_program p (fun v => idtac v).
    (*
    Print ind_finite.
    Search mutual_inductive_body "dec".
    Search (mutual_inductive_body -> mutual_inductive_body -> sumbool _ _).
          pose <% True %>.
    run_template_program (tmQuoteInductive (Kernames.MPfile ["Logic"%bs; "Init"%bs; "Coq"%bs], "True"%bs)) (fun v => idtac v).
    Print ind_bodies.
    Print Ast.Env.lookup_env.
    cbv [
  Print
  Print Ast.declared_minductive.
  Print Ast.Env.lookup_env.
  9 : { cbv [Universes.subst_instance].
        cbn.
        cbv [Ast.subst_instance_constr].
              | Ast.tConstruct _ _ _ => econstructor
              | Ast.tInd _ _ => econstructor
              | Ast.tSort _ => econstructor
              end
         end.
  cbv [quotation_of_well_typed].
  destruct 1.
  intro t.
cbv [quotation_of_well_typed].
intros.
cbv [quote_ground].
cbv [quote_True].
destruct t.

all: repeat match goal with
            | [ |- _ ;;; _ |- _ : _ ] => econstructor
            | [ |- _ ;;; _ |- _ <= _ ] => econstructor
            end.
10: cbv [type_of_constructor].
10: cbn.

10: {
econstructor.
econstructor.
4: econstructor.
5: econstructor.
4: econstructor.
10: econstructor.
2: { hnf.
     Print declared_inductive.
     cbv [declared_inductive].
     cbv.
eapply type_Construct.
Print typing.
econstructor.



#[export] Instance quote_True : ground_quotable True := ltac:(destruct 1; exact _).
#[export] Instance quote_False : ground_quotable False := ltac:(destruct 1; exact _).
#[export] Instance quote_byte : ground_quotable Byte.byte := ltac:(destruct 1; exact _).
#[export] Instance quote_Empty_set : ground_quotable Empty_set := ltac:(destruct 1; exact _).
#[export] Instance quote_unit : ground_quotable unit := ltac:(destruct 1; exact _).
#[export] Instance quote_bool : ground_quotable bool := ltac:(destruct 1; exact _).

#[export] Instance quote_eq {A} {qA : quotation_of A} {qA : ground_quotable A} {x y : A} : ground_quotable (x = y :> A) := ltac:(intros []; exact _).
#[export] Instance quote_eq_refl_l {A} {qA : quotation_of A} {x y : A} {qx : quotation_of x} : ground_quotable (x = y :> A) := ltac:(intros []; exact _).
#[export] Instance quote_eq_refl_r {A} {qA : quotation_of A} {x y : A} {qy : quotation_of y} : ground_quotable (x = y :> A) := ltac:(intro; subst; exact _).

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
Definition ground_quotable_of_iffT {A B} {quoteA : ground_quotable A} {qA : quotation_of A} {qB : quotation_of B} (H : iffT A B) {qH : quotation_of H} : ground_quotable B.
Proof.
  intro b.
  change (@quotation_of B (fst H (snd H b))).
  exact _.
Defined.
(* Transparent versions *)
Definition proj1 {A B} (x : A /\ B) : A := ltac:(apply x).
Definition proj2 {A B} (x : A /\ B) : B := ltac:(apply x).
Definition ground_quotable_of_iff {A B : Prop} {quoteA : ground_quotable A} {qA : quotation_of A} {qB : quotation_of B} (H : iff A B) {qH : quotation_of H} : ground_quotable B.
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
*)
*)