From MetaCoq.Lob.Template.QuoteGround Require Export Coq.Init Coq.MSets utils.MCOption utils.bytestring BasicAst (*utils  config*).
From MetaCoq.Template Require Import Universes.
(*

From Coq Require Import MSetList MSetAVL MSetFacts MSetProperties MSetDecide.
From Equations Require Import Equations.
From MetaCoq.Template Require Import utils BasicAst config.
Require Import ssreflect.
 *)
(* Grrr, [valuation]s cause so much trouble, because they're not quotable *)
(*
Record valuation :=
  { valuation_mono : string -> positive ;
    valuation_poly : nat -> nat }.
Class Evaluable (A : Type) := val : valuation -> A -> nat.
 *)
Module QuoteLevelSet := QuoteMSetAVL Level LevelSet.
Export QuoteLevelSet.Instances.
Module QuoteLevelExprSet := QuoteMSetListWithLeibniz LevelExpr LevelExprSet.
Export QuoteLevelExprSet.Instances.
Module QuoteConstraintSet := QuoteMSetAVL UnivConstraint ConstraintSet.
Export QuoteConstraintSet.Instances.

Module QuoteUniverses1.
  Module Import Level.
    #[export] Instance quote_t_ : ground_quotable Level.t_ := ltac:(destruct 1; exact _).
    #[export] Instance quote_lt_ {x y} : ground_quotable (Level.lt_ x y).
    Proof.
      destruct x, y;
        solve [ intro pf; exfalso; inversion pf
              | adjust_ground_quotable_by_econstructor_inversion () ].
    Defined.

    Module Export Instances.
      #[export] Existing Instances
       quote_t_
       quote_lt_
      .
    End Instances.
  End Level.

  Module Import PropLevel.
    #[export] Instance quote_t : ground_quotable PropLevel.t := ltac:(destruct 1; exact _).
    #[export] Instance quote_lt_ {x y} : ground_quotable (PropLevel.lt_ x y).
    Proof.
      destruct x, y;
        solve [ intro pf; exfalso; inversion pf
              | adjust_ground_quotable_by_econstructor_inversion () ].
    Defined.

    Module Export Instances.
      #[export] Existing Instances
       quote_t
       quote_lt_
      .
    End Instances.
  End PropLevel.

  Module Import LevelExpr.
    #[export] Instance quote_lt_ {x y} : ground_quotable (LevelExpr.lt_ x y)
    := ground_quotable_of_dec (@LevelExprSet.Raw.MX.lt_dec x y).

    Module Export Instances.
      #[export] Existing Instances
       quote_lt_
      .
    End Instances.
  End LevelExpr.
End QuoteUniverses1.
Export QuoteUniverses1.Level.Instances.
Export QuoteUniverses1.PropLevel.Instances.
Export QuoteUniverses1.LevelExpr.Instances.

#[export] Instance quote_nonEmptyLevelExprSet : ground_quotable nonEmptyLevelExprSet := ltac:(destruct 1; exact _).

#[export] Instance quote_concreteUniverses : ground_quotable concreteUniverses := ltac:(destruct 1; exact _).
Import StrongerInstances.
#[export] Instance quote_leq_cuniverse_n {cf n u u'} : ground_quotable (@leq_cuniverse_n cf n u u') := ltac:(cbv [leq_cuniverse_n]; exact _).
#[export] Instance quote_is_uprop {u} : ground_quotable (@is_uprop u) := ltac:(cbv [is_uprop]; exact _).
#[export] Instance quote_is_usprop {u} : ground_quotable (@is_usprop u) := ltac:(cbv [is_usprop]; exact _).
#[export] Instance quote_is_uproplevel {u} : ground_quotable (@is_uproplevel u) := ltac:(cbv [is_uproplevel]; exact _).
#[export] Instance quote_is_uproplevel_or_set {u} : ground_quotable (@is_uproplevel_or_set u) := ltac:(cbv [is_uproplevel_or_set]; exact _).
#[export] Instance quote_is_utype {u} : ground_quotable (@is_utype u) := ltac:(cbv [is_utype]; exact _).

#[export] Instance quote_allowed_eliminations : ground_quotable allowed_eliminations := ltac:(destruct 1; exact _).
#[export] Instance quote_is_allowed_elimination_cuniv {allowed u} : ground_quotable (is_allowed_elimination_cuniv allowed u) := ltac:(destruct allowed; exact _).

Module QuoteUniverses2.
  Module Import Universe.
    #[export] Instance quote_t_ : ground_quotable Universe.t_ := ltac:(destruct 1; exact _).
    #[local] Hint Constructors or eq : typeclass_instances.
    #[export] Instance quote_on_sort {P def s} {quoteP : forall l, s = Universe.lType l -> ground_quotable (P l:Prop)} {quote_def : s = Universe.lProp \/ s = Universe.lSProp -> ground_quotable (def:Prop)} : ground_quotable (@Universe.on_sort P def s) := ltac:(cbv [Universe.on_sort]; exact _).

    Module Instances.
      #[export] Existing Instances
       quote_t_
       quote_on_sort
      .
    End Instances.
  End Universe.

  Module Import ConstraintType.
    #[export] Instance quote_t_ : ground_quotable ConstraintType.t_ := ltac:(destruct 1; exact _).

    #[export] Instance quote_lt_ {x y} : ground_quotable (ConstraintType.lt_ x y).
    Proof.
      destruct x, y;
        solve [ intro pf; exfalso; inversion pf
              | adjust_ground_quotable_by_econstructor_inversion () ].
    Defined.

    Module Export Instances.
      #[export] Existing Instances
       quote_t_
       quote_lt_
      .
    End Instances.
  End ConstraintType.

  Module Import UnivConstraint.
    #[export] Instance quote_lt_ {x y} : ground_quotable (UnivConstraint.lt_ x y)
    := ground_quotable_of_dec (@ConstraintSet.Raw.MX.lt_dec x y).

    Module Export Instances.
      #[export] Existing Instances
       quote_lt_
      .
    End Instances.
  End UnivConstraint.

  Module Import Variance.
    #[export] Instance quote_t : ground_quotable Variance.t := ltac:(destruct 1; exact _).

    Module Export Instances.
      #[export] Existing Instances
       quote_t
      .
    End Instances.
  End Variance.
End QuoteUniverses2.
Export QuoteUniverses2.Universe.Instances.
Export QuoteUniverses2.ConstraintType.Instances.
Export QuoteUniverses2.UnivConstraint.Instances.
Export QuoteUniverses2.Variance.Instances.

#[export] Instance quote_declared_cstr_levels {levels cstr} : ground_quotable (declared_cstr_levels levels cstr) := ltac:(cbv [declared_cstr_levels]; exact _).
#[export] Instance quote_universes_decl : ground_quotable universes_decl := ltac:(destruct 1; exact _).

#[export] Instance quote_satisfies0 {v s} {qv : quotation_of v} : ground_quotable (@satisfies0 v s)
  := quote_of_iff (iff_sym (@uGraph.gc_of_constraint_spec config.default_checker_flags v s)).
#[export] Instance quote_satisfies {v s} {qv : quotation_of v} : ground_quotable (@satisfies v s)
  := quote_of_iff (iff_sym (@uGraph.gc_of_constraints_spec config.default_checker_flags v s)).

(* XXX FIXME *)
Definition consistent_dec ctrs : {@consistent ctrs} + {~@consistent ctrs}.
Proof.
  destruct (@uGraph.gc_consistent_iff config.default_checker_flags ctrs) as [f1 f2].
  cbv [MCOption.on_Some] in *; destruct @uGraph.gc_of_constraints.
Admitted.
#[export] Instance quote_consistent {ctrs} : ground_quotable (@consistent ctrs)
  := ground_quotable_of_dec (@consistent_dec ctrs).
(*
refine (quote_of_iff (iff_sym (@uGraph.gc_consistent_iff config.default_checker_flags s))).
 *)

Search consistent_extension_on.

Section Univ.
  Context {cf: checker_flags}.


  Definition consistent ctrs := exists v, satisfies v ctrs.

  Definition consistent_extension_on cs cstr :=
    forall v, satisfies v (ContextSet.constraints cs) -> exists v',
        satisfies v' cstr /\
          LevelSet.For_all (fun l => val v l = val v' l) (ContextSet.levels cs).


  Definition leq0_levelalg_n n φ (u u' : LevelAlgExpr.t) :=
    forall v, satisfies v φ -> (Z.of_nat (val v u) <= Z.of_nat (val v u') - n)%Z.

  Definition leq_levelalg_n n φ (u u' : LevelAlgExpr.t) :=
    if check_univs then leq0_levelalg_n n φ u u' else True.

  Definition leq_universe_n_ {CS} leq_levelalg_n n (φ: CS) s s' :=
    match s, s' with
    | Universe.lProp,   Universe.lProp
    | Universe.lSProp,  Universe.lSProp => (n = 0)%Z
    | Universe.lType u, Universe.lType u' => leq_levelalg_n n φ u u'
    | Universe.lProp,   Universe.lType u => prop_sub_type
    | _, _ => False
    end.

  Definition leq_universe_n := leq_universe_n_ leq_levelalg_n.

  Definition leqb_universe_n_ leqb_levelalg_n b s s' :=
    match s, s' with
    | Universe.lProp,   Universe.lProp
    | Universe.lSProp,  Universe.lSProp => negb b
    | Universe.lType u, Universe.lType u' => leqb_levelalg_n b u u'
    | Universe.lProp,   Universe.lType u => prop_sub_type
    | _, _ => false
    end.

  Definition eq0_levelalg φ (u u' : LevelAlgExpr.t) :=
    forall v, satisfies v φ -> val v u = val v u'.

  Definition eq_levelalg φ (u u' : LevelAlgExpr.t) :=
    if check_univs then eq0_levelalg φ u u' else True.

  Definition eq_universe_ {CS} eq_levelalg (φ: CS) s s' :=
    match s, s' with
    | Universe.lProp,   Universe.lProp
    | Universe.lSProp,  Universe.lSProp => True
    | Universe.lType u, Universe.lType u' => eq_levelalg φ u u'
    | _, _ => False
    end.

  Definition eq_universe := eq_universe_ eq_levelalg.

  Definition lt_levelalg := leq_levelalg_n 1.
  Definition leq_levelalg := leq_levelalg_n 0.
  Definition lt_universe := leq_universe_n 1.
  Definition leq_universe := leq_universe_n 0.

  Definition compare_universe (pb : conv_pb) :=
    match pb with
    | Conv => eq_universe
    | Cumul => leq_universe
    end.

  Lemma leq_levelalg_leq_levelalg_n (φ : ConstraintSet.t) u u' :
    leq_levelalg φ u u' <-> leq_levelalg_n 0 φ u u'.
  Proof using Type. intros. reflexivity. Qed.

  Lemma leq_universe_leq_universe_n (φ : ConstraintSet.t) u u' :
    leq_universe φ u u' <-> leq_universe_n 0 φ u u'.
  Proof using Type. intros. reflexivity. Qed.

  (* ctrs are "enforced" by φ *)

  Definition valid_constraints0 φ ctrs
    := forall v, satisfies v φ -> satisfies v ctrs.

  Definition valid_constraints φ ctrs
    := if check_univs then valid_constraints0 φ ctrs else True.

  Lemma valid_subset φ φ' ctrs
    : ConstraintSet.Subset φ φ' -> valid_constraints φ ctrs
      ->  valid_constraints φ' ctrs.
  Proof using Type.
    unfold valid_constraints.
    destruct check_univs; [|trivial].
    intros Hφ H v Hv. apply H.
    intros ctr Hc. apply Hv. now apply Hφ.
  Qed.

  Lemma switch_minus (x y z : Z) : (x <= y - z <-> x + z <= y)%Z.
  Proof using Type. split; lia. Qed.

  (* Lemma llt_lt n m : (n < m)%u -> (n < m)%Z.
  Proof. lled; lia. Qed.

  Lemma lle_le n m : (n <= m)%u -> (n <= m)%Z.
  Proof. lled; lia. Qed.

  Lemma lt_llt n m : prop_sub_type -> (n < m)%Z -> (n < m)%u.
  Proof. unfold llt. now intros ->. Qed.

  Lemma le_lle n m : prop_sub_type -> (n <= m)%Z -> (n <= m)%u.
  Proof. lled; [lia|discriminate]. Qed.

  Lemma lt_llt' n m : (0 <= n)%Z -> (n < m)%Z -> (n < m)%u.
  Proof. lled; lia. Qed.

  Lemma le_lle' n m : (0 <= n)%Z -> (n <= m)%Z -> (n <= m)%u.
  Proof. lled; lia. Qed. *)



  Definition is_lSet φ s := eq_universe φ s Universe.type0.
    (* Unfolded definition :
    match s with
    | Universe.lType u =>
      if check_univs then forall v, satisfies v φ -> val v u = 0 else True
    | _ => False
    end. *)

  Definition is_allowed_elimination φ allowed : Universe.t -> Prop :=
    match allowed with
    | IntoSProp => Universe.is_sprop
    | IntoPropSProp => is_propositional
    | IntoSetPropSProp => fun s => is_propositional s \/ is_lSet φ s
    | IntoAny => fun s => True
    end.

End Univ.

Inductive universes_entry :=
| Monomorphic_entry (ctx : ContextSet.t)
| Polymorphic_entry (ctx : UContext.t).
Derive NoConfusion for universes_entry.
