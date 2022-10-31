From MetaCoq.Lob.Template.QuoteGround Require Export Coq.Init Coq.MSets Coq.Numbers.
From MetaCoq.Template.utils Require Import wGraph.
From Coq Require Import MSetDecide MSetInterface.

Module Nbar.
  #[export] Instance quote_le {x y} : ground_quotable (Nbar.le x y) := ltac:(cbv [Nbar.le]; exact _).
  #[export] Instance quote_lt {x y} : ground_quotable (Nbar.lt x y) := ltac:(cbv [Nbar.lt]; exact _).
  Module Export Instances.
    #[export] Existing Instances
     quote_le
     quote_lt
    .
  End Instances.
End Nbar.
Export Nbar.Instances.

Module Type WeightedGraphSig (V : UsualOrderedType) (VSet : MSetInterface.S with Module E := V).
  Include WeightedGraph V VSet.
End WeightedGraphSig.

Module QuoteWeightedGraph (V : UsualOrderedType) (VSet : MSetInterface.S with Module E := V) (Import W : WeightedGraphSig V VSet).
  Module Import QuoteVSet := QuoteUsualSetsOn V VSet.
  Module Import QuoteEdgeSet := QuoteMSetAVL Edge EdgeSet.

  Section with_quote.
    Context {qEdgeSet_t : quotation_of EdgeSet.t} {qV_t : quotation_of V.t} {qVSet_t : quotation_of VSet.t}
            {qVSet_In : quotation_of VSet.In} {qEdgeSet_In : quotation_of EdgeSet.In}
            {qVSet_eq_dec : quotation_of VSet.eq_dec} {qVSet_add : quotation_of VSet.add} {qEdgeSet_subset_spec : quotation_of EdgeSet.subset_spec} {qlsp : quotation_of lsp}
            {quote_V_t : ground_quotable V.t} {quote_VSet_t : ground_quotable VSet.t}.

    #[export] Instance qEdgeSet_elt : quotation_of EdgeSet.elt := ltac:(cbv -[quotation_of]; exact _).
    #[export] Instance qt : quotation_of t := ltac:(cbv [t]; exact _).
    #[export] Instance qWE : quotation_of W.E := ltac:(cbv [W.E]; exact _).
    #[export] Instance qWV : quotation_of W.V := ltac:(cbv [W.V]; exact _).
    #[export] Instance qVSetProp_Add : quotation_of VSetProp.Add := ltac:(cbv [VSetProp.Add]; exact _).
    #[export] Instance qVSet : quotation_of VSetProp.Add := ltac:(cbv [VSetProp.Add]; exact _).

    #[export] Instance quote_PathOf {G x y} : ground_quotable (@PathOf G x y) := ltac:(induction 1; exact _).
    #[export] Instance quote_SPath {G s x y} : ground_quotable (@SPath G s x y) := ltac:(induction 1; exact _).
    #[export] Instance quote_subgraph {G1 G2} : ground_quotable (@subgraph G1 G2) := ltac:(induction 1; exact _).
    #[export] Instance quote_full_subgraph {G1 G2} : ground_quotable (@full_subgraph G1 G2) := ltac:(induction 1; exact _).
  End with_quote.

  Module Import Edge.
    Definition lt_dec x y : {Edge.lt x y} + {~Edge.lt x y}.
    Proof.
      pose proof (Edge.compare_spec x y) as H.
      destruct (Edge.compare x y);
        solve [ left; inversion H; assumption
              | right; intro H'; inversion H; subst;
                eapply Edge.lt_strorder; (idtac + etransitivity); eassumption ].
    Defined.

    Section with_quote.
      Context {qV_t : quotation_of V.t} {qV_lt : quotation_of V.lt}.

      #[export] Instance qEdge_t : quotation_of Edge.t := ltac:(cbv -[quotation_of]; exact _).
      #[export] Instance qlt : quotation_of Edge.lt := ltac:(cbv [Edge.lt V.eq]; try exact _).
      #[export] Instance quote_lt {x y} {qx : quotation_of x} {qy : quotation_of y} : ground_quotable (Edge.lt x y) := ground_quotable_of_dec (@lt_dec x y).
    End with_quote.

    Module Export Instances.
      #[export] Existing Instances
       quote_lt
      .
    End Instances.
  End Edge.
  Module Export Instances.
    Export QuoteVSet.Instances.
    Export QuoteEdgeSet.Instances.
    Export Edge.Instances.
    #[export] Existing Instances
     quote_PathOf
     quote_SPath
     quote_subgraph
     quote_full_subgraph
    .
  End Instances.
End QuoteWeightedGraph.
