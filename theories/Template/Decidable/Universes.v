From MetaCoq.Template Require Import Universes.
From MetaCoq.Lob.Template.Decidable Require Import common.uGraph.
From MetaCoq.Lob.Util.Tactics Require Import
     BreakMatch
     SplitInContext
.

Definition consistent_dec ctrs : {@consistent ctrs} + {~@consistent ctrs}.
Proof.
  destruct (@uGraph.gc_consistent_iff config.default_checker_flags ctrs) as [f1 f2].
  cbv [MCOption.on_Some] in *; destruct @uGraph.gc_of_constraints as [t|];
    [ | solve [ auto ] ].
  destruct (gc_consistent_dec t); [ left | right ]; auto.
Defined.

(* XXX FIXME *)
Definition consistent_extension_on_dec cs cstr : {@consistent_extension_on cs cstr} + {~@consistent_extension_on cs cstr}.
Proof.
Admitted.

Definition leq0_levelalg_n_dec n ϕ u u' : {@leq0_levelalg_n n ϕ u u'} + {~@leq0_levelalg_n n ϕ u u'}.
Proof.
  destruct (@uGraph.gc_leq0_levelalg_n_iff config.default_checker_flags n ϕ u u') as [f1 f2].
  cbv [MCOption.on_Some_or_None] in *; destruct @uGraph.gc_of_constraints as [t|];
    [ | solve [ auto ] ].
  destruct (gc_leq0_levelalg_n_dec n t u u'); [ left | right ]; auto.
Defined.

Definition leq_levelalg_n_dec cf n ϕ u u' : {@leq_levelalg_n cf n ϕ u u'} + {~@leq_levelalg_n cf n ϕ u u'}.
Proof.
  cbv [leq_levelalg_n]; destruct (@leq0_levelalg_n_dec n ϕ u u'); break_innermost_match; auto.
Defined.

Definition eq0_levelalg_dec ϕ u u' : {@eq0_levelalg ϕ u u'} + {~@eq0_levelalg ϕ u u'}.
Proof.
  destruct (@eq0_leq0_levelalg ϕ u u') as [f1 f2].
  destruct (@leq0_levelalg_n_dec BinNums.Z0 ϕ u u'), (@leq0_levelalg_n_dec BinNums.Z0 ϕ u' u); split_and; auto.
Defined.

Definition eq_levelalg_dec {cf ϕ} u u' : {@eq_levelalg cf ϕ u u'} + {~@eq_levelalg cf ϕ u u'}.
Proof.
  cbv [eq_levelalg]; break_innermost_match; auto using eq0_levelalg_dec.
Defined.

Definition eq_universe__dec {CS eq_levelalg ϕ}
           (eq_levelalg_dec : forall u u', {@eq_levelalg ϕ u u'} + {~@eq_levelalg ϕ u u'})
           s s'
  : {@eq_universe_ CS eq_levelalg ϕ s s'} + {~@eq_universe_ CS eq_levelalg ϕ s s'}.
Proof.
  cbv [eq_universe_]; break_innermost_match; auto.
Defined.

Definition eq_universe_dec {cf ϕ} s s' : {@eq_universe cf ϕ s s'} + {~@eq_universe cf ϕ s s'} := eq_universe__dec eq_levelalg_dec _ _.

(* XXX FIXME *)
Definition valid_constraints_dec cf ϕ cstrs : {@valid_constraints cf ϕ cstrs} + {~@valid_constraints cf ϕ cstrs}.
Proof.
  pose proof (fun G uctx a b c => uGraph.check_constraints_spec (uGraph.make_graph G) (uctx, ϕ) a b c cstrs) as H1.
  pose proof (fun G uctx a b c => uGraph.check_constraints_complete (uGraph.make_graph G) (uctx, ϕ) a b c cstrs) as H2.
  cbn [fst snd] in *.
  cbv [valid_constraints] in *; break_match; try solve [ left; exact I ].
  specialize (fun G uctx a b c => H2 G uctx a b c eq_refl).
  cbv [uGraph.is_graph_of_uctx MCOption.on_Some uGraph.global_uctx_invariants uGraph.uctx_invariants] in *; cbn [fst snd] in *.
Admitted.

Definition valid_constraints0_dec ϕ ctrs : {@valid_constraints0 ϕ ctrs} + {~@valid_constraints0 ϕ ctrs}
  := @valid_constraints_dec config.default_checker_flags ϕ ctrs.

Definition is_lSet_dec cf ϕ s : {@is_lSet cf ϕ s} + {~@is_lSet cf ϕ s}.
Proof.
  apply eq_universe_dec.
Defined.

Definition is_allowed_elimination_dec cf ϕ allowed u : {@is_allowed_elimination cf ϕ allowed u} + {~@is_allowed_elimination cf ϕ allowed u}.
Proof.
  cbv [is_allowed_elimination is_true]; break_innermost_match; auto;
    try solve [ repeat decide equality ].
  destruct (@is_lSet_dec cf ϕ u), is_propositional; intuition auto.
Defined.
