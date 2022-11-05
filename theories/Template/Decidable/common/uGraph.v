From MetaCoq.Template Require Import common.uGraph.

Definition gc_leq0_levelalg_n_dec n ctrs u u' : {@gc_leq0_levelalg_n n ctrs u u'} + {~@gc_leq0_levelalg_n n ctrs u u'}.
Proof.
  (*Print check_leqb_levelalg.
  Print leqb_levelalg_n.
  Print leqb_expr_univ_n.
  Search leqb_expr_univ_n.
  Search gc_leq0_levelalg_n.
  Print gc_leq0_levelalg_n.
  Search gc_leq_levelalg is_true.
  S
  Check Universes.LevelAlgExpr.make'.
  Print Template.Universes.Level.t_.
  Search gc_leq0_levelalg_n iff is_true.
  Check Universes.LevelAlgExpr.make.
  cbv [gc_leq0_levelalg_n].
  S
  Require Import MetaCoq.Template.All.*)
Admitted.
