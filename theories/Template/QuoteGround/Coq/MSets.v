From Coq Require Import MSetInterface MSetList MSetAVL MSetFacts MSetProperties MSetDecide.
From MetaCoq.Lob.Util.Tactics Require Import
     DestructHead.
From MetaCoq.Lob.Template.QuoteGround Require Export Coq.Numbers Coq.Init.

Module Type MSetAVL_MakeT (T : OrderedType). Include MSetAVL.Make T. End MSetAVL_MakeT.

Module QuoteMSetAVL (T : OrderedType) (M : MSetAVL_MakeT T).
  Module MFact := WFactsOn T M.
  Module MProp := WPropertiesOn T M.
  Module MDecide := WDecide (M).
  Local Ltac msets := MDecide.fsetdec.

  Scheme Induction for M.Raw.tree Sort Type.
  Scheme Induction for M.Raw.tree Sort Set.
  Scheme Induction for M.Raw.tree Sort Prop.
  Scheme Case for M.Raw.tree Sort Type.
  Scheme Case for M.Raw.tree Sort Prop.
  Scheme Minimality for M.Raw.tree Sort Type.
  Scheme Minimality for M.Raw.tree Sort Set.
  Scheme Minimality for M.Raw.tree Sort Prop.

  Fixpoint Raw_InT_dec x t : { M.Raw.InT x t } + {~ M.Raw.InT x t}.
  Proof.
    refine match t with
           | M.Raw.Leaf => right _
           | M.Raw.Node z l n r
             => match T.compare x n as c, Raw_InT_dec x l, Raw_InT_dec x r return CompareSpec _ _ _ c -> _ with
                | Eq, _, _ => fun pf => left (_ pf)
                | _, left pf, _ => fun _ => left _
                | _, _, left pf => fun _ => left _
                | _, right p2, right p3 => fun p1 => right (_ p1)
                end (T.compare_spec x n)
           end;
      try solve [ inversion 1
                | inversion 1; first [ constructor; first [ assumption | subst; reflexivity ] | exfalso; discriminate ]
                | constructor; assumption
                | do 2 inversion 1; subst; exfalso;
                  try congruence;
                  match goal with
                  | [ H : T.lt _ _, H' : T.eq _ _ |- False ]
                    => rewrite H' in H; now eapply M.Raw.MX.lt_irrefl
                  end ].
  Defined.
  Definition Raw_In_dec x y : {M.Raw.In x y} + {~M.Raw.In x y}.
  Proof.
    cbv [M.Raw.In]; apply Raw_InT_dec.
  Defined.
  Definition In_dec x y : {M.In x y} + {~M.In x y}.
  Proof.
    cbv [M.In]; apply Raw_In_dec.
  Defined.
  Definition Inb x y := b_of_dec (In_dec x y).
  Definition Inb_bp x y : Inb x y = true -> M.In x y := bp_of_dec.
  Definition Inb_pb x y : M.In x y -> Inb x y = true := pb_of_dec.

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
    Definition M_Raw_bstb t := b_of_dec (M_Raw_bst_dec t).
    Definition M_Raw_bstb_bst t : M_Raw_bstb t = true -> M.Raw.bst t := bp_of_dec.
    Definition M_Raw_bstb_bst_alt t : M.Raw.bst t -> M_Raw_bstb t = true := pb_of_dec.
    #[export] Instance quote_Raw_bst t : ground_quotable (M.Raw.bst t)
      := ground_quotable_of_bp (@M_Raw_bstb_bst t) (@M_Raw_bstb_bst_alt t).
    #[export] Instance quote_Raw_Ok s : ground_quotable (M.Raw.Ok s) := (ltac:(cbv [M.Raw.Ok]; exact _)).
    #[export] Instance quote_t : ground_quotable M.t := (ltac:(induction 1; exact _)).

    #[export] Instance quote_In x y : ground_quotable (M.In x y)
      := ground_quotable_of_bp (@Inb_bp x y) (@Inb_pb x y).

    Definition Raw_For_all_alt (P : M.elt -> Prop) : M.Raw.t -> Prop
      := fix Raw_For_all_alt (s : M.Raw.t) : Prop
        := match s with
           | M.Raw.Leaf => True
           | M.Raw.Node z l n r => Raw_For_all_alt l /\ P n /\ Raw_For_all_alt r
           end.
    Definition For_all_alt (P : M.elt -> Prop) (s : M.t) : Prop
      := Raw_For_all_alt P (M.this s).
    #[local] Hint Constructors M.Raw.InT : core typeclass_instances.
    #[local] Hint Extern 1 (T.eq _ _) => reflexivity : core.
    Lemma For_all_alt_iff P {P_Proper : Proper (T.eq ==> Basics.impl) P} s
      : M.For_all P s <-> For_all_alt P s.
    Proof using Type.
      cbv [For_all_alt M.For_all M.In M.Raw.In M.this]; destruct s as [s _].
      split; induction s; cbn; intro H'; auto; try inversion 1; subst; repeat apply conj; destruct_head'_and.
      all: (idtac + (eapply P_Proper; (idtac + symmetry))); now eauto.
    Defined.
    Definition For_all_alt1 {P} {P_Proper : Proper (T.eq ==> Basics.impl) P} {s}
      : M.For_all P s -> For_all_alt P s.
    Proof. apply For_all_alt_iff; assumption. Defined.
    Definition For_all_alt2 {P} {P_Proper : Proper (T.eq ==> Basics.impl) P} {s}
      : For_all_alt P s -> M.For_all P s.
    Proof. apply For_all_alt_iff; assumption. Defined.
    #[export] Instance quote_For_all_alt {P s} {quote_P : forall x, M.In x s -> ground_quotable (P x:Prop)} {qP : quotation_of P} : ground_quotable (For_all_alt P s).
    Proof.
      cbv [For_all_alt M.For_all M.In M.Raw.In M.this] in *; destruct s as [s _].
      induction s; cbn [Raw_For_all_alt]; try exact _.
      apply @quote_and; try exact _.
      2: apply @quote_and; try exact _.
      all: eauto.
    Defined.
    #[export] Instance quote_For_all {P s} {quote_P : forall x, M.In x s -> ground_quotable (P x:Prop)} {qP : quotation_of P} {P_Proper : Proper (T.eq ==> Basics.impl) P} {qP_Proper : quotation_of P_Proper} : ground_quotable (M.For_all P s).
    Proof.
      intro pf.
      let f := match goal with |- ?f _ => f end in
      change (f (For_all_alt2 (For_all_alt1 pf))).
      exact _.
    Defined.
  End with_t.
End QuoteMSetAVL.

(*
Module Type MSetList_MakeWithLeibnizT (T : OrderedTypeWithLeibniz). Include MSetList.MakeWithLeibniz T. End MSetList_MakeWithLeibnizT.

Module QuoteMSetListWithLeibniz (T : OrderedTypeWithLeibniz) (M : MSetList_MakeWithLeibnizT T).
  Module MFact := WFactsOn T M.
  Module MProp := WPropertiesOn T M.
  Module MDecide := WDecide (M).
  Local Ltac msets := MDecide.fsetdec.

  Search M.In "dec".
  Print MDecide.

  Definition Raw_In_dec x y : {M.Raw.In x y} + {~M.Raw.In x y}.
  Proof.
    cbv [M.Raw.In]; apply InA_dec, T.eq_dec.
  Defined.
  Definition In_dec x y : {M.In x y} + {~M.In x y}.
  Proof.
    cbv [M.In]; apply Raw_In_dec.
  Defined.
End QuoteMSetListWithLeibniz.
*)
