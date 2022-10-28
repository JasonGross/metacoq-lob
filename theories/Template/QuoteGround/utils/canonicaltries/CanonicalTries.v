From MetaCoq.Lob.Template.QuoteGround Require Export Coq.Init.
From MetaCoq.Template.utils.canonicaltries Require Import CanonicalTries.

Module PTree.
  Scheme Induction for PTree.tree' Sort Type.
  Scheme Induction for PTree.tree' Sort Set.
  Scheme Induction for PTree.tree' Sort Prop.
  #[export] Instance quote_tree' {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (PTree.tree' A) := ltac:(induction 1; exact _).
  #[export] Instance quote_tree {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (PTree.tree A) := ltac:(destruct 1; exact _).
  #[export] Instance quote_not_trivially_empty {A l o r} : ground_quotable (@PTree.not_trivially_empty A l o r) := ltac:(cbv [PTree.not_trivially_empty]; exact _).

  Module Export Instances.
    #[export] Existing Instances
     quote_tree'
     quote_tree
     quote_not_trivially_empty
    .
  End Instances.
End PTree.

Export PTree.Instances.
