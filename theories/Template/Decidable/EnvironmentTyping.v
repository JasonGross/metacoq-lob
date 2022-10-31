From MetaCoq.Template Require Import BasicAst Environment EnvironmentTyping Universes.

Module LookupDecide (Import T : Term) (Import E : EnvironmentSig T) (Import L : LookupSig T E).

  Definition wf_universe_dec Σ s : {@wf_universe Σ s} + {~@wf_universe Σ s}.
  Proof.
    destruct s; try (left; exact I).
    cbv [wf_universe Universe.on_sort LevelExprSet.In LevelExprSet.this t_set].
    destruct t as [[t _] _].
    induction t as [|t ts [IHt|IHt]]; [ left | | right ].
    { inversion 1. }
    { destruct (LevelSetProp.In_dec (LevelExpr.get_level t) (global_ext_levels Σ)) as [H|H]; [ left | right ].
      { inversion 1; subst; auto. }
      { intro H'; apply H, H'; now constructor. } }
    { intro H; apply IHt; intros; apply H; now constructor. }
  Defined.
End LookupDecide.
