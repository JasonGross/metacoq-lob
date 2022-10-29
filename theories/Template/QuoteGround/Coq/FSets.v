From Coq Require Import FMapInterface FMapList FMapAVL FMapFullAVL FMapFacts.
From MetaCoq.Lob.Template.QuoteGround Require Export Coq.Numbers Coq.Init Coq.Lists.
From MetaCoq.Lob.Util.Tactics Require Import
     SplitInContext
     SpecializeBy
     SpecializeAllWays
     DestructHead
     SpecializeUnderBindersBy
     InHypUnderBindersDo
     BreakMatch
.

Module QuoteWSfun (E : DecidableType) (Import W : WSfun E).
  Module Import WFacts := WFacts_fun E W.

  Section with_quote.
    Context {elt : Type}
            {qE_t : quotation_of E.t} {qelt : quotation_of elt} {qt : quotation_of t}
            {qMapsTo : quotation_of MapsTo}
            {qfind : quotation_of find} {qmem : quotation_of mem} {qelements : quotation_of elements}
            {qfind_mapsto_iff : quotation_of find_mapsto_iff}.

    #[export] Instance qIn : quotation_of In := ltac:(cbv [In]; exact _).
    #[export] Instance qEmpty : quotation_of Empty := ltac:(cbv [Empty]; exact _).
    #[export] Instance qEqual : quotation_of (@Equal) := ltac:(cbv -[quotation_of]; exact _).
    #[export] Instance qEquiv : quotation_of (@Equiv) := ltac:(cbv -[quotation_of]; exact _).

    #[export] Instance quote_MapsTo {x y z} {qx : quotation_of x} {qy : quotation_of y} {qz : quotation_of z} : ground_quotable (@MapsTo elt x y z)
        := quote_of_iff (iff_sym (@find_mapsto_iff _ _ _ _)).

    #[export] Instance quote_In {k m} {qk : quotation_of k} {qm : quotation_of m} : ground_quotable (@In elt k m)
      := quote_of_iff (iff_sym (@mem_in_iff _ _ _)).
    #[export] Instance quote_neg_In {k m} {qk : quotation_of k} {qm : quotation_of m} : ground_quotable (~@In elt k m)
      := quote_neg_of_iff (iff_sym (@mem_in_iff _ _ _)).

    #[export] Instance quote_Empty {m} {qm : quotation_of m} : ground_quotable (@Empty elt m)
      := quote_of_iff (iff_sym (@is_empty_iff _ _)).
    #[export] Instance quote_neg_Empty {m} {qm : quotation_of m} : ground_quotable (~@Empty elt m)
      := quote_neg_of_iff (iff_sym (@is_empty_iff _ _)).

    Definition Equiv_alt (eq_elt : elt -> elt -> Prop) m m' :=
      let eq_opt_elt x y := match x, y with
                            | Some x, Some y => eq_elt x y
                            | None, None => True
                            | Some _, None | None, Some _ => False
                            end in
      List.Forall (fun '(k, _) => eq_opt_elt (find k m) (find k m')) (@elements elt m)
      /\ List.Forall (fun '(k, _) => eq_opt_elt (find k m) (find k m')) (@elements elt m').
    Import StrongerInstances.
    #[export] Instance quote_Equiv_alt {eq_elt} {m m'} {qeq_elt : quotation_of eq_elt} {quote_elt : ground_quotable elt} {quote_key : ground_quotable key} {quote_eq_elt : forall x y, ground_quotable (eq_elt x y:Prop)} {qm : quotation_of m} {qm' : quotation_of m'} : ground_quotable (@Equiv_alt eq_elt m m') := _.
    Lemma Equiv_alt_iff {eq_elt m m'} : Equiv_alt eq_elt m m' <-> Equiv eq_elt m m'.
    Proof using Type.
      cbv [Equiv Equiv_alt].
      cbv [In] in *.
      setoid_rewrite find_mapsto_iff.
      rewrite !Forall_forall.
      pose proof (@find_o elt m).
      pose proof (@find_o elt m').
      transitivity
        (let eq_opt_elt x y := match x, y with
                               | Some x, Some y => eq_elt x y
                               | None, None => True
                               | Some _, None | None, Some _ => False
                               end in
         (forall k, In k m -> eq_opt_elt (find k m) (find k m'))
         /\ (forall k, In k m' -> eq_opt_elt (find k m) (find k m'))).
      1: cbv [In]; setoid_rewrite elements_mapsto_iff; setoid_rewrite InA_alt; cbv [eq_key_elt]; cbn [fst snd].
      2: cbv [In]; setoid_rewrite find_mapsto_iff.
      all: repeat (split || intros || destruct_head'_and || split_iff || destruct_head'_prod || destruct_head'_ex || subst).
      all: specialize_dep_under_binders_by eapply ex_intro.
      all: specialize_dep_under_binders_by eapply conj.
      all: specialize_dep_under_binders_by eapply eq_refl.
      all: specialize_dep_under_binders_by eapply pair.
      all: cbn [fst snd] in *.
      all: specialize_all_ways_under_binders_by apply E.eq_refl.
      all: repeat first [ progress destruct_head'_ex
                        | match goal with
                          | [ H : List.In _ _ |- _ ]
                            => progress specialize_under_binders_by exact H
                          | [ H : E.eq _ _ |- _ ]
                            => progress specialize_under_binders_by exact H
                          | [ H : find _ _ = Some _ |- _ ]
                            => progress specialize_under_binders_by exact H
                          end ].
      all: try solve [ break_innermost_match; break_innermost_match_hyps; try congruence; eauto ].
    Qed.

    #[export] Instance quote_Equiv {eq_elt m m'} {qm : quotation_of m} {qm' : quotation_of m'} {quote_elt : ground_quotable elt} {quote_key : ground_quotable key} {qeq_elt : quotation_of eq_elt} {quote_eq_elt : forall x y, ground_quotable (eq_elt x y:Prop)} : ground_quotable (@Equiv elt eq_elt m m') := quote_of_iff Equiv_alt_iff.

    #[export] Instance quote_Equal {m m'} {qm : quotation_of m} {qm' : quotation_of m'} {quote_elt : ground_quotable elt} {quote_key : ground_quotable key} : ground_quotable (@Equal elt m m') := quote_of_iff (iff_sym (@Equal_Equiv elt m m')).

    #[export] Instance quote_Equivb {cmp m m'} {qm : quotation_of m} {qm' : quotation_of m'} {quote_elt : ground_quotable elt} {quote_key : ground_quotable key} {qcmp : quotation_of cmp} : ground_quotable (@Equivb elt cmp m m') := _.
  End with_quote.

  Module Export Instances.
    #[export] Existing Instances
     qIn
     qEmpty
     qEqual
     qEquiv
     quote_MapsTo
     quote_In
     quote_neg_In
     quote_Empty
     quote_neg_Empty
     quote_Equiv_alt
     quote_Equiv
     quote_Equal
     quote_Equivb
    .
  End Instances.
End QuoteWSfun.


Module Type FMapAVL_MakeT (T : OrderedType). Include FMapAVL.Make T. End FMapAVL_MakeT.

Module QuoteFMapAVL (T : OrderedType) (M : FMapAVL_MakeT T).
  Module Import QM := QuoteWSfun T M.

  Scheme Induction for M.Raw.tree Sort Type.
  Scheme Induction for M.Raw.tree Sort Set.
  Scheme Induction for M.Raw.tree Sort Prop.
  Scheme Case for M.Raw.tree Sort Type.
  Scheme Case for M.Raw.tree Sort Prop.
  Scheme Minimality for M.Raw.tree Sort Type.
  Scheme Minimality for M.Raw.tree Sort Set.
  Scheme Minimality for M.Raw.tree Sort Prop.

  Section with_t.
    Context {elt : Type}
            {qelt : quotation_of elt}
            {quote_elt : ground_quotable elt} {quote_T_t : ground_quotable T.t}.

    #[export] Instance quote_M_Raw_t : ground_quotable (M.Raw.t elt) := (ltac:(induction 1; exact _)).
    Fixpoint M_Raw_lt_tree_dec x t : { @M.Raw.lt_tree elt x t } + {~ @M.Raw.lt_tree elt x t}.
    Proof.
      refine match t with
             | M.Raw.Leaf => left _
             | M.Raw.Node l k n r z
               => match T.compare k x, M_Raw_lt_tree_dec x l, M_Raw_lt_tree_dec x r with
                  | LT p1, left p2, left p3 => left _
                  | _, right pf, _ => right _
                  | _, _, right pf => right _
                  | _, _, _ => right _
                  end
             end;
        try solve [ inversion 1
                  | inversion 1; subst; auto;
                    match goal with
                    | [ H : T.lt _ _, H' : T.eq _ _ |- _ ]
                      => now first [ rewrite -> H' in H | rewrite <- H' in H ]
                    end
                  | intro f; apply pf; hnf in *; intros; apply f; constructor; (assumption + reflexivity)
                  | intro f; eapply M.Raw.Proofs.MX.lt_antirefl; (idtac + etransitivity); (eassumption + (eapply f; constructor; (idtac + symmetry); (eassumption + reflexivity))) ].
    Defined.
    Fixpoint M_Raw_gt_tree_dec x t : { @M.Raw.gt_tree elt x t } + {~ @M.Raw.gt_tree elt x t}.
    Proof.
      refine match t with
             | M.Raw.Leaf => left _
             | M.Raw.Node l k n r z
               => match T.compare k x, M_Raw_gt_tree_dec x l, M_Raw_gt_tree_dec x r with
                  | GT p1, left p2, left p3 => left _
                  | _, right pf, _ => right _
                  | _, _, right pf => right _
                  | _, _, _ => right _
                  end
             end;
        try solve [ inversion 1
                  | inversion 1; subst; auto;
                    match goal with
                    | [ H : T.lt _ _, H' : T.eq _ _ |- _ ]
                      => now first [ rewrite -> H' in H | rewrite <- H' in H ]
                    end
                  | intro f; apply pf; hnf in *; intros; apply f; constructor; (assumption + reflexivity)
                  | intro f; eapply M.Raw.Proofs.MX.lt_antirefl; (idtac + etransitivity); (eassumption + (eapply f; constructor; (idtac + symmetry); (eassumption + reflexivity))) ].
    Defined.
    Fixpoint M_Raw_bst_dec t : { @M.Raw.bst elt t } + {~ @M.Raw.bst elt t}.
    Proof.
      refine match t with
             | M.Raw.Leaf => left _
             | M.Raw.Node l k n r z
               => match M_Raw_bst_dec l, M_Raw_bst_dec r, M_Raw_lt_tree_dec k l, M_Raw_gt_tree_dec k r with
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
    #[export] Instance quote_t : ground_quotable (M.t elt) := (ltac:(induction 1; exact _)).
  End with_t.

  Module Export Instances.
    Export QM.Instances.
    #[export] Existing Instances
     quote_M_Raw_t
     quote_Raw_bst
     quote_t
    .
  End Instances.
End QuoteFMapAVL.
