Require Export MetaCoq.Lob.Util.Notations.

Ltac zeta1 x :=
  lazymatch x with
  | let a := ?b in ?f => constr:(subst_let a := b in f)
  end.
