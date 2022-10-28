From Coq Require Import MSetInterface MSetList MSetAVL MSetFacts MSetProperties MSetDecide.
From MetaCoq.Lob.Util.Tactics Require Import
     DestructHead.
From MetaCoq.Lob.Template.QuoteGround Require Export Coq.Numbers Coq.Init Coq.Lists.

Module QuoteWSetsOn (E : DecidableType) (Import W : WSetsOn E).
  Module WFacts := WFactsOn E W.
  Module WProperties := WPropertiesOn E W.
  Module WDecide := WDecideOn E W.

  #[export] Instance quote_In {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (In x y)
    := ground_quotable_of_dec (WProperties.In_dec x y).
  #[export] Instance quote_neg_In {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (~In x y)
    := ground_quotable_neg_of_dec (WProperties.In_dec x y).
  #[export] Instance quote_Equal {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (Equal x y)
    := ground_quotable_of_dec (eq_dec x y).
  #[export] Instance quote_neg_Equal {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (~Equal x y)
    := ground_quotable_neg_of_dec (eq_dec x y).
  #[export] Instance quote_Subset {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (Subset x y) := quote_of_iff (@subset_spec x y).
  #[export] Instance quote_neg_Subset {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (~Subset x y) := quote_neg_of_iff (@subset_spec x y).
  #[export] Instance quote_Empty {x} {qx : quotation_of x} : ground_quotable (Empty x) := quote_of_iff (conj (@WProperties.empty_is_empty_2 x) (@WProperties.empty_is_empty_1 x)).
  #[export] Instance quote_neg_Empty {x} {qx : quotation_of x} : ground_quotable (~Empty x) := quote_neg_of_iff (conj (@WProperties.empty_is_empty_2 x) (@WProperties.empty_is_empty_1 x)).
  #[export] Instance quote_Add {x s s'} {qx : quotation_of x} {qs : quotation_of s} {qs' : quotation_of s'} : ground_quotable (WProperties.Add x s s')
    := quote_of_iff (iff_sym (WProperties.Add_Equal _ _ _)).
  #[export] Instance quote_neg_Add {x s s'} {qx : quotation_of x} {qs : quotation_of s} {qs' : quotation_of s'} : ground_quotable (~WProperties.Add x s s')
    := quote_neg_of_iff (iff_sym (WProperties.Add_Equal _ _ _)).

  Definition For_all_alt (P : elt -> Prop) (s : t) : Prop
    := List.Forall P (elements s).
  #[local] Hint Extern 1 (E.eq _ _) => reflexivity : core.
  Lemma For_all_alt_iff {P} {P_Proper : Proper (E.eq ==> Basics.impl) P} {s}
    : For_all_alt P s <-> For_all P s.
  Proof.
    cbv [For_all_alt For_all].
    setoid_rewrite WFacts.elements_iff.
    induction (elements s) as [|x xs IH].
    { split; solve [ constructor | inversion 2 ]. }
    { setoid_rewrite Forall_cons_iff; setoid_rewrite InA_cons; setoid_rewrite IH.
      intuition auto.
      eapply P_Proper; (idtac + symmetry); eassumption. }
  Defined.
  #[export] Instance quote_For_all {P s} {quote_elt : ground_quotable elt} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {P_Proper : Proper (E.eq ==> Basics.impl) P} {qP_Proper : quotation_of P_Proper} {qs : quotation_of s} : ground_quotable (For_all P s)
    := quote_of_iff For_all_alt_iff.
  Lemma For_all_forall_iff {P s} : (For_all P s) <-> (forall v, In v s -> P v).
  Proof. reflexivity. Qed.
  Lemma For_all_forall2_iff {P s} : (For_all (fun v1 => For_all (P v1) s) s) <-> (forall v1 v2, In v1 s -> In v2 s -> P v1 v2).
  Proof. cbv [For_all]; intuition eauto. Qed.
  #[export] Instance quote_forall2_In {P s} {qP : quotation_of P} {qs : quotation_of s} {quote_For_all : ground_quotable (For_all (fun v1 => For_all (P v1) s) s)} : ground_quotable (forall v1 v2, In v1 s -> In v2 s -> P v1 v2)
    := quote_of_iff For_all_forall2_iff.

  Definition Exists_alt (P : elt -> Prop) (s : t) : Prop
    := List.Exists P (elements s).
  Lemma Exists_alt_iff {P} {P_Proper : Proper (E.eq ==> Basics.impl) P} {s}
    : Exists_alt P s <-> Exists P s.
  Proof.
    cbv [Exists_alt Exists].
    setoid_rewrite WFacts.elements_iff.
    induction (elements s) as [|x xs IH].
    { split; try solve [ constructor | inversion 1 | intros [x [H H']]; inversion H ]. }
    { setoid_rewrite Exists_cons; setoid_rewrite InA_cons; setoid_rewrite IH.
      firstorder intuition auto. }
  Defined.
  Definition Exists_dec {P s} (P_dec : forall x, {P x} + {~P x}) {P_Proper : Proper (E.eq ==> Basics.impl) P} : {Exists P s} + {~Exists P s}.
  Proof.
    destruct (List.Exists_dec P (elements s) P_dec) as [H|H]; [ left | right ]; revert H.
    { intro H; apply Exists_alt_iff, H. }
    { intros H H'; apply H, Exists_alt_iff, H'. }
  Defined.
  Definition quote_Exists_dec {P} (P_dec : forall x, {P x} + {~P x}) {s} {quote_elt : ground_quotable elt} {qP_dec : quotation_of P_dec} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {P_Proper : Proper (E.eq ==> Basics.impl) P} {qP_Proper : quotation_of P_Proper} {qs : quotation_of s} : ground_quotable (Exists P s)
    := ground_quotable_of_dec (Exists_dec P_dec).
  Module Export Instances.
    #[export] Existing Instances
     quote_In
     quote_Equal
     quote_Subset
     quote_Empty
     quote_Add
     quote_neg_In
     quote_neg_Equal
     quote_neg_Subset
     quote_neg_Empty
     quote_neg_Add
     quote_For_all
     quote_forall2_In
    .
  End Instances.
End QuoteWSetsOn.

Module QuoteSetsOn (E : OrderedType) (Import M : SetsOn E).
  Include QuoteWSetsOn E M.
  Module Import MOrdProperties. Module E := E. Include M <+ OrdProperties. End MOrdProperties.

  Definition above x s : bool := for_all (fun y => if ME.lt_dec y x then true else false) s.
  Definition below x s : bool := for_all (fun y => if ME.lt_dec x y then true else false) s.
  Lemma above_spec x s : above x s = true <-> Above x s.
  Proof.
    cbv [Above above].
    rewrite for_all_spec
      by (intros ?? H; repeat (let H' := fresh in destruct ME.lt_dec as [H'|H']; rewrite ?H in H'); try reflexivity; tauto).
    cbv [For_all].
    split; intros H y H'; generalize (H y H'); destruct ME.lt_dec; try reflexivity; eauto; congruence.
  Qed.
  Lemma below_spec x s : below x s = true <-> Below x s.
  Proof.
    cbv [Below below].
    rewrite for_all_spec
      by (intros ?? H; repeat (let H' := fresh in destruct ME.lt_dec as [H'|H']; rewrite ?H in H'); try reflexivity; tauto).
    cbv [For_all].
    split; intros H y H'; generalize (H y H'); destruct ME.lt_dec; try reflexivity; eauto; congruence.
  Qed.
  #[export] Instance quote_Above {x s} {qx : quotation_of x} {qs : quotation_of s} : ground_quotable (Above x s)
    := quote_of_iff (above_spec x s).
  #[export] Instance quote_Below {x s} {qx : quotation_of x} {qs : quotation_of s} : ground_quotable (Below x s)
    := quote_of_iff (below_spec x s).

  Module Export OnlyOrdInstances.
    #[export] Existing Instances
     quote_Above
     quote_Below
    .
  End OnlyOrdInstances.
  Module Export OrdInstances.
    Export Instances.
    Export OnlyOrdInstances.
  End OrdInstances.
End QuoteSetsOn.

Module Type MSetAVL_MakeT (T : OrderedType). Include MSetAVL.Make T. End MSetAVL_MakeT.

Module QuoteMSetAVL (T : OrderedType) (M : MSetAVL_MakeT T).
  Module Import QM := QuoteSetsOn T M.

  Scheme Induction for M.Raw.tree Sort Type.
  Scheme Induction for M.Raw.tree Sort Set.
  Scheme Induction for M.Raw.tree Sort Prop.
  Scheme Case for M.Raw.tree Sort Type.
  Scheme Case for M.Raw.tree Sort Prop.
  Scheme Minimality for M.Raw.tree Sort Type.
  Scheme Minimality for M.Raw.tree Sort Set.
  Scheme Minimality for M.Raw.tree Sort Prop.

  Section with_t.
    Context {quote_T_t : ground_quotable T.t}.

    #[export] Instance quote_M_Raw_t : ground_quotable M.Raw.t := (ltac:(induction 1; exact _)).
    Fixpoint M_Raw_lt_tree_dec x t : { M.Raw.lt_tree x t } + {~ M.Raw.lt_tree x t}.
    Proof.
      refine match t with
             | M.Raw.Leaf => left _
             | M.Raw.Node z l n r
               => match T.compare n x as c, M_Raw_lt_tree_dec x l, M_Raw_lt_tree_dec x r return CompareSpec _ _ _ c -> _ with
                  | Lt, left p2, left p3 => fun pfc => left _
                  | _, right pf, _ => fun pfc => right _
                  | _, _, right pf => fun pfc => right _
                  | _, _, _ => fun pfc => right _
                  end (T.compare_spec _ _)
             end;
        try solve [ inversion 1; inversion pfc
                  | inversion 1; inversion pfc; subst; auto;
                    match goal with
                    | [ H : T.lt _ _, H' : T.eq _ _ |- _ ]
                      => now first [ rewrite -> H' in H | rewrite <- H' in H ]
                    end
                  | intro f; apply pf; hnf in *; intros; apply f; constructor; (assumption + reflexivity)
                  | intro f; inversion pfc; eapply M.Raw.MX.lt_irrefl; (idtac + etransitivity); (eassumption + (eapply f; constructor; (idtac + symmetry); (eassumption + reflexivity))) ].
    Defined.
    Fixpoint M_Raw_gt_tree_dec x t : { M.Raw.gt_tree x t } + {~ M.Raw.gt_tree x t}.
    Proof.
      refine match t with
             | M.Raw.Leaf => left _
             | M.Raw.Node z l n r
               => match T.compare n x as c, M_Raw_gt_tree_dec x l, M_Raw_gt_tree_dec x r return CompareSpec _ _ _ c -> _ with
                  | Gt, left p2, left p3 => fun pfc => left _
                  | _, right pf, _ => fun pfc => right _
                  | _, _, right pf => fun pfc => right _
                  | _, _, _ => fun pfc => right _
                  end (T.compare_spec _ _)
             end;
        try solve [ inversion 1; inversion pfc
                  | inversion 1; inversion pfc; subst; auto;
                    match goal with
                    | [ H : T.lt _ _, H' : T.eq _ _ |- _ ]
                      => now first [ rewrite -> H' in H | rewrite <- H' in H ]
                    end
                  | intro f; apply pf; hnf in *; intros; apply f; constructor; (assumption + reflexivity)
                  | intro f; inversion pfc; eapply M.Raw.MX.lt_irrefl; (idtac + etransitivity); (eassumption + (eapply f; constructor; (idtac + symmetry); (eassumption + reflexivity))) ].
    Defined.
    Fixpoint M_Raw_bst_dec t : { M.Raw.bst t } + {~ M.Raw.bst t}.
    Proof.
      refine match t with
             | M.Raw.Leaf => left _
             | M.Raw.Node z l n r
               => match M_Raw_bst_dec l, M_Raw_bst_dec r, M_Raw_lt_tree_dec n l, M_Raw_gt_tree_dec n r with
                  | right pf, _, _, _ => right _
                  | _, right pf, _, _ => right _
                  | _, _, right pf, _ => right _
                  | _, _, _, right pf => right _
                  | left p1, left p2, left p3, left p4 => left _
                  end
             end;
        try solve [ constructor; assumption
                  | inversion 1; subst; auto ].
    Defined.
    #[export] Instance quote_Raw_bst t : ground_quotable (M.Raw.bst t)
      := ground_quotable_of_dec (@M_Raw_bst_dec t).
    #[export] Instance quote_Raw_Ok s : ground_quotable (M.Raw.Ok s) := (ltac:(cbv [M.Raw.Ok]; exact _)).
    #[export] Instance quote_t : ground_quotable M.t := (ltac:(induction 1; exact _)).
  End with_t.

  Module Export Instances.
    Export QM.OrdInstances.
    #[export] Existing Instances
     quote_M_Raw_t
     quote_Raw_bst
     quote_Raw_Ok
     quote_t
    .
  End Instances.
End QuoteMSetAVL.

Module QuoteUsualWSetsOn (E : UsualDecidableType) (Import M : WSetsOn E).
  Module Import QM := QuoteWSetsOn E M.

  #[export] Instance quote_For_all {P s} {quote_elt : ground_quotable elt} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (For_all P s)
    := QM.quote_For_all.
  Definition quote_Exists_dec {P} (P_dec : forall x, {P x} + {~P x}) {s} {quote_elt : ground_quotable elt} {qP_dec : quotation_of P_dec} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (Exists P s)
    := QM.quote_Exists_dec P_dec.
  #[export] Instance quote_forall2_In {P s} {qP : quotation_of P} {qs : quotation_of s} {quote_elt : ground_quotable elt} {quote_P : forall x y, ground_quotable (P x y:Prop)} : ground_quotable (forall v1 v2, In v1 s -> In v2 s -> P v1 v2) := _.

  Notation quote_In := QM.quote_In.
  Notation quote_Equal := QM.quote_Equal.
  Notation quote_Subset := QM.quote_Subset.
  Notation quote_Empty := QM.quote_Empty.
  Notation quote_Add := QM.quote_Add.
  Notation quote_neg_In := QM.quote_neg_In.
  Notation quote_neg_Equal := QM.quote_neg_Equal.
  Notation quote_neg_Subset := QM.quote_neg_Subset.
  Notation quote_neg_Empty := QM.quote_neg_Empty.
  Notation quote_neg_Add := QM.quote_neg_Add.

  Module Export Instances.
    #[export] Existing Instances
     QM.quote_In
     QM.quote_Equal
     QM.quote_Subset
     QM.quote_Empty
     QM.quote_Add
     QM.quote_neg_In
     QM.quote_neg_Equal
     QM.quote_neg_Subset
     QM.quote_neg_Empty
     QM.quote_neg_Add
     quote_For_all
     quote_forall2_In
    .
  End Instances.
End QuoteUsualWSetsOn.

Module QuoteUsualSetsOn (E : UsualOrderedType) (Import M : SetsOn E).
  Module QM := QuoteUsualWSetsOn E M.
  Module QM' := QuoteSetsOn E M.

  Notation quote_In := QM.quote_In.
  Notation quote_Equal := QM.quote_Equal.
  Notation quote_Subset := QM.quote_Subset.
  Notation quote_Empty := QM.quote_Empty.
  Notation quote_Add := QM.quote_Add.
  Notation quote_neg_In := QM.quote_neg_In.
  Notation quote_neg_Equal := QM.quote_neg_Equal.
  Notation quote_neg_Subset := QM.quote_neg_Subset.
  Notation quote_neg_Empty := QM.quote_neg_Empty.
  Notation quote_neg_Add := QM.quote_neg_Add.
  Notation quote_Above := QM'.quote_Above.
  Notation quote_Below := QM'.quote_Below.

  Module Export Instances.
    Export QM.Instances QM'.OnlyOrdInstances.
  End Instances.
End QuoteUsualSetsOn.

Module QuoteSetsOnWithLeibniz (E : OrderedTypeWithLeibniz) (Import M : SetsOn E).
  Module Import QM := QuoteSetsOn E M.

  #[local] Instance all_P_Proper {P : E.t -> Prop} : Proper (E.eq ==> Basics.impl) P.
  Proof.
    intros ?? H.
    apply E.eq_leibniz in H; subst; exact id.
  Defined.

  #[export] Instance quote_For_all {P s} {quote_elt : ground_quotable elt} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (For_all P s)
    := QM.quote_For_all.
  Definition quote_Exists_dec {P} (P_dec : forall x, {P x} + {~P x}) {s} {quote_elt : ground_quotable elt} {qP_dec : quotation_of P_dec} {quote_P : forall x, ground_quotable (P x:Prop)} {qP : quotation_of P} {qs : quotation_of s} : ground_quotable (Exists P s)
    := QM.quote_Exists_dec P_dec.
  #[export] Instance quote_forall2_In {P s} {qP : quotation_of P} {qs : quotation_of s} {quote_elt : ground_quotable elt} {quote_P : forall x y, ground_quotable (P x y:Prop)} : ground_quotable (forall v1 v2, In v1 s -> In v2 s -> P v1 v2) := _.

  Notation quote_In := QM.quote_In.
  Notation quote_Equal := QM.quote_Equal.
  Notation quote_Subset := QM.quote_Subset.
  Notation quote_Empty := QM.quote_Empty.
  Notation quote_Add := QM.quote_Add.
  Notation quote_neg_In := QM.quote_neg_In.
  Notation quote_neg_Equal := QM.quote_neg_Equal.
  Notation quote_neg_Subset := QM.quote_neg_Subset.
  Notation quote_neg_Empty := QM.quote_neg_Empty.
  Notation quote_neg_Add := QM.quote_neg_Add.
  Notation quote_Above := QM.quote_Above.
  Notation quote_Below := QM.quote_Below.

  Module Export Instances.
    #[export] Existing Instances
     QM.quote_In
     QM.quote_Equal
     QM.quote_Subset
     QM.quote_Empty
     QM.quote_Add
     QM.quote_neg_In
     QM.quote_neg_Equal
     QM.quote_neg_Subset
     QM.quote_neg_Empty
     QM.quote_neg_Add
     quote_For_all
     quote_forall2_In
     QM.quote_Above
     QM.quote_Below
    .
  End Instances.
End QuoteSetsOnWithLeibniz.
