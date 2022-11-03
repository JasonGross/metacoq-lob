Require Import Coq.Lists.List.
From MetaCoq.Template Require Import Typing.
From MetaCoq.Lob.Template Require Export QuoteGround.Init.Typing.
From MetaCoq.Lob.Template.QuoteGround Require Export Coq.Init.
From MetaCoq.Lob.Util.Tactics Require Import
     Head
.
From Coq.ssr Require Import ssreflect ssrbool.

Import ListNotations.

Import Universes.
Lemma use_fold_right_andb_true {ls} (H : is_true (fold_right andb true ls)) {P}
  : fold_right (fun b acc => is_true b -> acc) P ls -> P.
Proof.
  revert P; induction ls; cbn in *; eauto.
  move: H.
  case/andP => //.
  intros.
  apply IHls; eauto.
Qed.

Ltac pre_begin_ground_quotable_well_typed _ :=
  let t := fresh "t" in
  intro t; hnf; intros; revert dependent t;
  cbv [config.global_env_ext_constraint] in *.

Ltac handle_env_constraints _ :=
  progress repeat match goal with
                  | [ H : is_true (fold_right andb true ?ls) |- ?P ]
                    => apply (@use_fold_right_andb_true ls H P); cbn [fold_right map]; clear H
                  end;
  repeat match goal with
         | [ |- is_true (@eqb ?A ?r ?x ?y) -> _ ]
           => let H := fresh in
              intro H; apply eqb_eq in H
         end.

Ltac begin_ground_quotable_well_typed _ :=
  let t := fresh "t" in
  intro t; destruct t; vm_compute quote_ground.

Ltac ground_quotable_well_typed_step _ :=
  first [ match goal with
          | [ |- _ ;;; _ |- ?t : _ ]
            => let h := head t in
               is_constructor h;
               econstructor
          | [ |- _ ;;; _ |- ?t <= _ ]
            => let h := head t in
               is_constructor h;
               econstructor
          | [ |- TermEquality.compare_term _ _ _ ?t _ ]
            => let h := head t in
               is_constructor h;
               econstructor
          | [ H : wf_local _ _ |- wf_local _ _ ]
            => exact H
          end
        | progress cbv [Ast.declared_constructor Ast.declared_inductive Ast.declared_minductive]
        | progress cbv [TermEquality.R_global_instance TermEquality.R_opt_variance TermEquality.global_variance TermEquality.lookup_inductive Ast.Env.fst_ctx TermEquality.lookup_minductive TermEquality.R_universe_instance]
        | match goal with
          | [ H : ?x = Some _ |- context[?x] ]
            => rewrite H
          | [ |- _ /\ _ ] => split
          | [ |- Some _ = Some _ ] => reflexivity
          | [ |- ?x = ?x ] => reflexivity
          | [ |- Forall2 _ nil nil ] => constructor
          | [ |- match ?ev with
                 | Universe.lProp => ?x = ?x
                 | _ => _
                 end ]
            => unify ev Universe.lProp
          | [ |- match ?ev with Universe.lType _ => _ | Universe.lProp => False | Universe.lSProp => False end ]
            => let ev' := open_constr:(Universe.lType _) in unify ev ev'
          | [ |- match ?ev with Universe.lType _ => False | Universe.lProp => _ | Universe.lSProp => False end ]
            => unify ev Universe.lProp
          | [ |- match ?ev with Universe.lType _ => False | Universe.lProp => False | Universe.lSProp => _ end ]
            => unify ev Universe.lSProp
          end
        | exact I
        | progress cbn ].

Ltac make_ground_quotable_well_typed _ :=
  pre_begin_ground_quotable_well_typed ();
  handle_env_constraints ();
  begin_ground_quotable_well_typed ();
  repeat repeat ground_quotable_well_typed_step ().

From MetaCoq.SafeChecker Require Import SafeTemplateChecker.
From MetaCoq.Template Require Import All utils.
Import MCMonadNotation.
#[local,program] Instance fake_abstract_guard_impl : PCUICWfEnvImpl.abstract_guard_impl :=
  {
    guard_impl := PCUICWfEnvImpl.fake_guard_impl
  }.
Next Obligation. todo "this axiom is inconsitent, onlu used to make infer compute". Qed.
Definition default_normal : @PCUICSN.normalizing_flags config.default_checker_flags.
now econstructor.
Defined.

#[export] Instance quote_True_well_typed : ground_quotable_well_typed_using [True] True := ltac:(make_ground_quotable_well_typed ()).
#[export] Instance quote_False_well_typed : ground_quotable_well_typed_using [False] False := ltac:(make_ground_quotable_well_typed ()).
#[export] Instance quote_byte_well_typed : ground_quotable_well_typed_using [Byte.byte] Byte.byte.
pre_begin_ground_quotable_well_typed ().
clear.
intro t.
replace cf with config.default_checker_flags.
run_template_program (tmQuoteRec Byte.byte) (fun x => pose x as v).
lazymatch goal with
| [ |- @typing ?cf ?Σ ?Γ ?t ?T ]
  => pose (@infer_template_program cf default_normal (* PCUICSN.default_normalizing*) _ (fst v, t) Monomorphic_ctx) as ch
end.
destruct t.
clear -ch.
replace Σ with (fst v, Monomorphic_ctx).
let k := open_constr:([]) in
replace Γ with k.
pose (match ch with PCUICErrors.CorrectDecl d => Some d.π1 | _ => None end) as ch'.
Time Timeout 30 vm_compute in ch'.
Print EnvCheck_wf_env_ext.
Print PCUICErrors.EnvCheck. EnvCheck
Timeout 10 vm_compute in ch.
cbv [program] in *.

handle_env_constraints ().
cbv [global_env_ext] in *.

replace Σ with (fst v, Monomorphic_ctx).
let k := open_constr:([]) in
replace Γ with k.
intro t; destruct t.
(*
Require Import MetaCoq.Template.Checker.
Check infer.*)
Check @infer_template_program.
Search PCUICSN.normalizing_flags.
lazymatch goal with
| [ |- @typing ?cf ?Σ ?Γ ?t ?T ]
  => epose (@infer_template_program cf 100 (fst Σ) init_graph Γ t)
end.
Print typing_result.
Search infer.
Timeout 10 vm_compute in t.
Search universes_graph.

Set Printing Implicit.
Search ConstraintSet.t universes_decl.
Print universes_decl.
Print config.checker_flags.
begin_ground_quotable_well_typed ().
all: ground_quotable_well_typed_step ().
all: try ground_quotable_well_typed_step ().
all: try ground_quotable_well_typed_step ().
Abort.
*)
#[export] Instance quote_Empty_set_well_typed : ground_quotable_well_typed_using [Empty_set] Empty_set := ltac:(make_ground_quotable_well_typed ()).
#[export] Instance quote_unit_well_typed : ground_quotable_well_typed_using [unit] unit.
  pre_begin_ground_quotable_well_typed ();
  handle_env_constraints ();
  begin_ground_quotable_well_typed ().
  ground_quotable_well_typed_step ().
  repeat repeat ground_quotable_well_typed_step ().
  2: ground_quotable_well_typed_step ().
  2: repeat repeat ground_quotable_well_typed_step ().
  set (v := Ast.tSort _).
  let v' := open_constr:(_) in replace v with v'.
  all: subst v.
  repeat repeat ground_quotable_well_typed_step ().
  ground_quotable_well_typed_step ().
  reflexivity.
Defined.
(*  := ltac:(make_ground_quotable_well_typed ()).*)
#[export] Instance quote_bool_well_typed : ground_quotable_well_typed_using [bool] bool := ltac:(make_ground_quotable_well_typed ()).
(*
2: repeat repeat ground_quotable_well_typed_step ().
3: repeat repeat ground_quotable_well_typed_step ().
2: { cbv [leq_levelalg_n].
     cbv [leq0_levelalg_n].
     cbv [NonEmptySetFacts.singleton].
2: { Print Universe.lType.
     match goal with
  end.
repeat repeat ground_quotable_well_typed_step ().
introduce
  := ltac:(make_ground_quotable_well_typed ()).
(*
#[export] Instance quote_False : ground_quotable False := ltac:(destruct 1; exact _).
#[export] Instance quote_byte : ground_quotable Byte.byte := ltac:(destruct 1; exact _).

#[export] Instance quote_eq {A} {qA : quotation_of A} {quoteA : ground_quotable A} {x y : A} : ground_quotable (x = y :> A) := ltac:(intros []; exact _).
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
Definition ground_quotable_neq_of_EqDec {A x y} {qA : quotation_of A} {quoteA : ground_quotable A} {H : EqDec A} {qH : quotation_of H} : ground_quotable (x <> y :> A)
  := ground_quotable_neg_of_dec (H x y).
#[export] Hint Extern 1 (ground_quotable (?x <> ?y :> ?A)) => simple notypeclasses refine (@ground_quotable_neq_of_EqDec A x y _ _ _ _) : typeclass_instances.

#[export] Instance quote_eq_true {b} : ground_quotable (eq_true b) := ltac:(destruct 1; exact _).
#[export] Instance quote_BoolSpec {P Q : Prop} {b} {qP : quotation_of P} {qQ : quotation_of Q} {quoteP : ground_quotable P} {quoteQ : ground_quotable Q} : ground_quotable (BoolSpec P Q b).
Proof.
  destruct b; adjust_ground_quotable_by_econstructor_inversion ().
Defined.
#[export] Instance quote_nat : ground_quotable nat := ltac:(induction 1; exact _).
#[export] Polymorphic Instance quote_option {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (option A) := (ltac:(induction 1; exact _)).
#[export] Polymorphic Instance quote_sum {A B} {qA : quotation_of A} {qB : quotation_of B} {quoteA : ground_quotable A} {quoteB : ground_quotable B} : ground_quotable (sum A B) := (ltac:(induction 1; exact _)).
#[export] Polymorphic Instance quote_prod {A B} {qA : quotation_of A} {qB : quotation_of B} {quoteA : ground_quotable A} {quoteB : ground_quotable B} : ground_quotable (prod A B) := (ltac:(induction 1; exact _)).
#[export] Polymorphic Instance quote_list {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (list A) := (ltac:(induction 1; exact _)).
#[export] Polymorphic Instance quotation_of_list {A ls} {qA : quotation_of A} {qls : @All A quotation_of ls} : quotation_of ls := ltac:(induction qls; exact _).
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

#[export] Polymorphic Instance quote_sig {A} {P : A -> Prop} {qA : quotation_of A} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteP : forall x, quotation_of x -> ground_quotable (P x)} : ground_quotable (@sig A P) := (ltac:(induction 1; exact _)).
#[export] Polymorphic Instance quote_sig2 {A} {P Q : A -> Prop} {qA : quotation_of A} {qP : quotation_of P} {qQ : quotation_of Q} {quoteA : ground_quotable A} {quoteP : forall x, quotation_of x -> ground_quotable (P x)} {quoteQ : forall x, quotation_of x -> ground_quotable (Q x)} : ground_quotable (@sig2 A P Q) := (ltac:(induction 1; exact _)).
#[export] Polymorphic Instance quote_sigT {A P} {qA : quotation_of A} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteP : forall x, quotation_of x -> ground_quotable (P x)} : ground_quotable (@sigT A P) := (ltac:(induction 1; exact _)).
#[export] Polymorphic Instance quote_sigT2 {A} {P Q} {qA : quotation_of A} {qP : quotation_of P} {qQ : quotation_of Q} {quoteA : ground_quotable A} {quoteP : forall x, quotation_of x -> ground_quotable (P x)} {quoteQ : forall x, quotation_of x -> ground_quotable (Q x)} : ground_quotable (@sigT2 A P Q) := (ltac:(induction 1; exact _)).
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

Definition option_eq_None_dec_r {A} {l : option A} : {l = None} + {l <> None}.
Proof. destruct l; [ right | left ]; try reflexivity; congruence. Defined.
Definition option_eq_None_dec_l {A} {l : option A} : {None = l} + {None <> l}.
Proof. destruct l; [ right | left ]; try reflexivity; congruence. Defined.
#[export] Instance quote_option_neq_None_r {A} {qA : quotation_of A} (l : option A) {ql : quotation_of l} : ground_quotable (l <> None)
  := ground_quotable_neg_of_dec option_eq_None_dec_r.
#[export] Instance quote_option_neq_None_l {A} {qA : quotation_of A} (l : option A) {ql : quotation_of l} : ground_quotable (None <> l)
  := ground_quotable_neg_of_dec option_eq_None_dec_l.
*)
*)
