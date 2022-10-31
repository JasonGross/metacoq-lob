From MetaCoq.Template Require Import common.uGraph.

(* XXX FIXME *)
Definition gc_consistent_dec ctrs : {@gc_consistent ctrs} + {~@gc_consistent ctrs}.
Proof.
  (*epose proof (fun v => make_graph_spec2 (v, ctrs)) as H; cbn [snd] in H.
  cbv [global_gc_uctx_invariants] in *.
  cbn [fst snd] in *.
  Print make_graph.
  Search Good
  Search GoodConstraintSet.t.
  Compute GoodConstraintSet.elt.
  Print
  Search GoodConstraint.t_
  Search gc_consistent.
  Search wGraph.correct_labelling.*)
Admitted.

(* XXX FIXME *)
Definition gc_leq0_levelalg_n_dec n ctrs u u' : {@gc_leq0_levelalg_n n ctrs u u'} + {~@gc_leq0_levelalg_n n ctrs u u'}.
Proof.
Admitted.
