From MetaCoq.Template Require Import Universes utils.MCList.
From MetaCoq.Lob.Template.Decidable Require Import common.uGraph.
From MetaCoq.Lob.Util.Tactics Require Import
     BreakMatch
     SplitInContext
     SpecializeBy
     SpecializeUnderBindersBy
     DestructHead
.

Definition consistent_dec ctrs : {@consistent ctrs} + {~@consistent ctrs}.
Proof.
  pose proof (@uGraph.is_consistent_spec config.default_checker_flags).
  destruct (@uGraph.gc_consistent_iff config.default_checker_flags ctrs) as [f1 f2].
  cbv [MCOption.on_Some] in *; destruct @uGraph.gc_of_constraints as [t|];
    [ | solve [ auto ] ].
  destruct (gc_consistent_dec t); [ left | right ]; auto.
Defined.

Definition levels_of_cs (cstr : ConstraintSet.t) : LevelSet.t
  := ConstraintSet.fold (fun '(l1, _, l2) acc => LevelSet.add l1 (LevelSet.add l2 acc)) cstr (LevelSet.singleton Level.lzero).
Lemma levels_of_cs_spec cstr (lvls := levels_of_cs cstr)
  : uGraph.global_uctx_invariants (lvls, cstr).
Proof.
  subst lvls; cbv [levels_of_cs].
  cbv [uGraph.global_uctx_invariants uGraph.uctx_invariants ConstraintSet.For_all declared_cstr_levels]; cbn [fst snd ContextSet.levels ContextSet.constraints].
  repeat first [ apply conj
               | progress intros
               | progress break_innermost_match
               | match goal with
                 | [ |- ?x \/ ?y ]
                   => first [ lazymatch x with context[LevelSet.In ?l (LevelSet.singleton ?l)] => idtac end;
                              left
                            | lazymatch y with context[LevelSet.In ?l (LevelSet.singleton ?l)] => idtac end;
                              right ]
                 | [ H : ConstraintSet.In ?l ?c |- ?x \/ ?y ]
                   => first [ lazymatch x with context[LevelSet.In _ (ConstraintSet.fold _ c _)] => idtac end;
                              left
                            | lazymatch y with context[LevelSet.In _ (ConstraintSet.fold _ c _)] => idtac end;
                              right ]
                 end
               | rewrite !LevelSet.union_spec
               | progress rewrite <- ?ConstraintSet.elements_spec1, ?InA_In_eq in *
               | rewrite ConstraintSetProp.fold_spec_right ].
  all: lazymatch goal with
       | [ |- LevelSet.In Level.lzero (List.fold_right ?f ?init ?ls) ]
         => first [ LevelSetDecide.fsetdec
                  | cut (LevelSet.In Level.lzero init);
                    [ generalize init; induction ls; intros; cbn in *
                    | LevelSetDecide.fsetdec ] ]
       | [ H : List.In ?v ?ls |- LevelSet.In ?v' (List.fold_right ?f ?init (List.rev ?ls)) ]
         => rewrite List.in_rev in H;
            let ls' := fresh "ls" in
            set (ls' := List.rev ls);
            change (List.In v ls') in H;
            change (LevelSet.In v' (List.fold_right f init ls'));
            generalize init; induction ls'; cbn in *
       end.
  all: repeat first [ exfalso; assumption
                    | progress destruct_head'_or
                    | progress subst
                    | progress intros
                    | progress break_innermost_match
                    | rewrite !LevelSetFact.add_iff
                    | solve [ auto ] ].
Qed.

(* MOVE ME *)
Lemma global_uctx_invariants_union_or lvls1 lvls2 cs
  : uGraph.global_uctx_invariants (lvls1, cs) \/ uGraph.global_uctx_invariants (lvls2, cs)
    -> uGraph.global_uctx_invariants (LevelSet.union lvls1 lvls2, cs).
Proof.
  cbv [uGraph.global_uctx_invariants uGraph.uctx_invariants ConstraintSet.For_all declared_cstr_levels]; cbn [fst snd ContextSet.levels ContextSet.constraints].
  repeat first [ apply conj
               | progress intros
               | progress cbv beta iota in *
               | progress break_innermost_match
               | progress destruct_head'_and
               | progress destruct_head'_or
               | progress split_and
               | rewrite !LevelSet.union_spec
               | progress specialize_dep_under_binders_by eapply pair
               | solve [ eauto ] ].
Qed.

Definition levels_of_cs2 (cs1 cs2 : ConstraintSet.t) : LevelSet.t
  := LevelSet.union (levels_of_cs cs1) (levels_of_cs cs2).
Lemma levels_of_cs2_spec cs1 cs2 (lvls := levels_of_cs2 cs1 cs2)
  : uGraph.global_uctx_invariants (lvls, cs1)
    /\ uGraph.global_uctx_invariants (lvls, cs2).
Proof.
  split; apply global_uctx_invariants_union_or; constructor; apply levels_of_cs_spec.
Qed.

Definition levels_of_cscs (cs : ContextSet.t) (cstr : ConstraintSet.t) : LevelSet.t
  := LevelSet.union (ContextSet.levels cs) (levels_of_cs2 cstr (ContextSet.constraints cs)).
Lemma levels_of_cscs_spec cs cstr (lvls := levels_of_cscs cs cstr)
  : uGraph.global_uctx_invariants (lvls, ContextSet.constraints cs)
    /\ uGraph.global_uctx_invariants (lvls, cstr).
Proof.
  generalize (levels_of_cs2_spec cstr (ContextSet.constraints cs)).
  split; apply global_uctx_invariants_union_or; constructor; apply levels_of_cs2_spec.
Qed.

Lemma consistent_extension_on_iff cs cstr
      (cf := config.default_checker_flags) (lvls := levels_of_cscs cs cstr)
  : @consistent_extension_on cs cstr
    <-> is_true
          match uGraph.is_consistent (lvls, ContextSet.constraints cs), uGraph.is_consistent (lvls, cstr),
            uGraph.gc_of_uctx (lvls, ContextSet.constraints cs), uGraph.gc_of_uctx (lvls, cstr) with
          | false, _, _, _
          | _, _, None, _
            => true
          | _, true, Some G, Some G'
            => uGraph.wGraph.IsFullSubgraph.is_full_extension (uGraph.make_graph G) (uGraph.make_graph G')
          | _, _, _, _ => false
          end.
Proof.
  destruct (levels_of_cscs_spec cs cstr).
  cbv zeta; break_innermost_match.
  let H := fresh in pose proof (fun uctx uctx' G => @uGraph.consistent_ext_on_full_ext _ uctx G (lvls, uctx')) as H; cbn [fst snd] in H; erewrite H; clear H.
  1: reflexivity.
  all: cbn [fst snd ContextSet.constraints] in *.
  all: repeat
         repeat
         first [ match goal with
                 | [ H : _ = Some _ |- _ ] => rewrite H
                 | [ H : _ = None |- _ ] => rewrite H
                 | [ |- _ <-> is_true false ]
                   => cbv [is_true]; split; [ let H := fresh in intro H; contradict H | congruence ]
                 | [ |- _ <-> is_true true ]
                   => split; [ reflexivity | intros _ ]
                 end
               | progress cbv [uGraph.is_graph_of_uctx monad_utils.bind monad_utils.ret monad_utils.option_monad] in *
               | progress cbn [MCOption.on_Some fst snd] in *
               | rewrite <- uGraph.is_consistent_spec2
               | progress subst
               | progress break_innermost_match_hyps
               | assert_fails (idtac; lazymatch goal with |- ?G => has_evar G end);
                 first [ reflexivity | assumption ]
               | match goal with
                 | [ H : ?T, H' : ~?T |- _ ] => exfalso; apply H', H
                 | [ H : uGraph.gc_of_uctx _ = None |- _ ] => cbv [uGraph.gc_of_uctx] in *
                 | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
                 | [ H : Some _ = None |- _ ] => inversion H
                 | [ H : None = Some _ |- _ ] => inversion H
                 | [ H : ?T <-> False |- _ ] => destruct H as [H _]; try change (~T) in H
                 | [ H : ~consistent ?cs |- consistent_extension_on (_, ?cs) _ ]
                   => intros ? ?; exfalso; apply H; eexists; eassumption
                 | [ H : @uGraph.is_consistent ?cf ?uctx = false |- _ ]
                   => assert (~consistent (snd uctx));
                      [ rewrite <- (@uGraph.is_consistent_spec cf uctx), H; clear H; auto
                      | clear H ]
                 | [ H : @uGraph.gc_of_constraints ?cf ?ctrs = None |- _ ]
                   => let H' := fresh in
                      pose proof (@uGraph.gc_consistent_iff cf ctrs) as H';
                      rewrite H in H';
                      clear H
                 | [ H : @uGraph.is_consistent ?cf ?uctx = true |- _ ]
                   => assert_fails (idtac; match goal with
                                           | [ H' : consistent ?v |- _ ] => unify v (snd uctx)
                                           end);
                      assert (consistent (snd uctx));
                      [ rewrite <- (@uGraph.is_consistent_spec cf uctx), H; clear H; auto
                      | ]
                 end ].
  all: try solve [ repeat first [ progress cbv [consistent consistent_extension_on not] in *
                                | progress intros
                                | progress destruct_head'_ex
                                | progress destruct_head'_and
                                | progress specialize_under_binders_by eassumption
                                | solve [ eauto ] ] ].
  all: cbv [uGraph.global_uctx_invariants].
  all: cbn [fst].
  all: cbv [uGraph.uctx_invariants].
  all: cbn [fst snd].
(*
  all: try match goal with |- uGraph.global_uctx_invariants _ => shelve end.

  2: {
      ].
    intro H;
    hnf in H.
       cbv [consistent] in *.
       destruct_head'_ex.

       speiclai
       match goal with
       end.
       auto.

            | ]
       end.
    match goal with
    end.
    cbv [consistent_extension_on consistent] in *.
       cbv [not] in *.

       intuition eauto.
       | [
  4: {
    match goal with
    end.
    pose (@uGraph.gc_consistent_iff).
       lazymatch goal with
       end.

         cbv [uGraph.gc_of_uctx monad_utils.bind monad_utils.ret monad_utils.option_monad] in *.
       cbn [fst snd] in *.
       break_innermost_match_hyps; try congruence.
       match goal w
       Search uGraph.gc_of_constraints.
  Search uGraph.wGraph.subgraph.
  7: {
    cbv [consistent_extension_on].
    pose proof (uGraph.is_consistent_spec).
    cbv [consistent] in *.

    Search (~is_true _) false.
    setoid_rewrite H in Heqb.
    Search uGraph.is_consistent.
    match goal with
    end.
    cbv [
  all: repeat first [ match goal with
                      | [ H : _ = Some _ |- _ ] => rewrite H
                      | [ H : _ = None |- _ ] => rewrite H
                      end
                    | progress cbv [uGraph.is_graph_of_uctx]
                    | progress cbn [MCOption.on_Some]
                    | rewrite <- uGraph.is_consistent_spec2
                    | assert_fails (idtac; lazymatch goal with |- ?G => has_evar G end);
                      first [ reflexivity | cbv [is_true] in *; assumption ] ].
  3: { cbv [is_true] in *.
  3: assumption.
  pose uGraph.is_consistent_spec.
  3:

  Search uGraph.Equal_graph.
  Print uGraph.gc_of_uctx.
  Search uGraph.is_graph_of_uctx.
  rewrite
Next Obligation.
  cbv [uGraph.wGraph.t] in *.
 *)
Abort.
(* XXX FIXME *)
Definition consistent_extension_on_dec cs cstr : {@consistent_extension_on cs cstr} + {~@consistent_extension_on cs cstr}.
Proof.
  (*
  pose proof (fun levels G G' => @uGraph.consistent_ext_on_full_ext config.default_checker_flags cs G (levels, cstr) G').
  pose proof (@uGraph.gc_consistent_iff config.default_checker_flags (ContextSet.constraints cs)).
  pose proof (@uGraph.gc_consistent_iff config.default_checker_flags cstr).
  cbn [fst snd ContextSet.constraints] in *.
  pose proof (@uGraph.is_consistent_spec config.default_checker_flags cs) as Hcs1.
  pose proof (@uGraph.is_consistent_spec config.default_checker_flags (fst cs, cstr)) as Hcstr1.
  specialize_under_binders_by eapply (fun levels G' pf => proj1 (@uGraph.is_consistent_spec2 config.default_checker_flags G' (levels, cstr) pf)), @uGraph.is_consistent_spec.
  cbv [uGraph.global_uctx_invariants] in *.
  cbv [uGraph.uctx_invariants] in *.
  cbn [fst snd] in *.
  unshelve epose (let lvls := _ in
         match uGraph.gc_of_constraints (ContextSet.constraints cs), uGraph.gc_of_constraints cstr with
         | Some G, Some G'
           => let G := uGraph.make_graph (lvls, G) in
              let G' := uGraph.make_graph (lvls, G') in
              _
         | _, _ => false
         end).
  4: {
    pose .
    cbv [

  Search declared_cstr_levels.
  Print declared_cstr_levels.
  specialize_under_binders_by eassumption.
  Print consistent_extension_on.
  Print uGraph.uctx_invariants.
  Locate uGraph.global_uctx_invariants.
  destruct (uGraph.gc_of_constraints cstr) as [Gcstr|] eqn:Hcstr,
        (uGraph.gc_of_constraints (ContextSet.constraints cs)) as [Gcs|] eqn:Hcs.
  all: cbn [MCOption.on_Some] in *.
  all: try solve [ cbv [uGraph.universes_graph ContextSet.t uGraph.is_graph_of_uctx] in *;
                   cbv [MCOption.on_Some consistent consistent_extension_on] in *;
                   split_iff; left; intros; exfalso; rewrite ?Hcstr, ?Hcs in *; eauto ].
  2: {
  Search uGraph.is_consistent.
  specialize_under_binders_by eassumption.
  setoid_rewrite <- H2 in H.
  2: { Search uGraph.gc_consistent.
  all:   cbv [uGraph.universes_graph ContextSet.t uGraph.is_graph_of_uctx] in *;
    cbv [MCOption.on_Some consistent consistent_extension_on] in *.
  2: {
  all:
  2: { left; intros; exfalso.

  2: {
  .
  specialize_under_binders_by (erewrite <- (@uGraph.is_consistent_spec2 config.default_checker_flags)).
  pose uGraph.make_graph.
  Search uGraph.make_graph.
  pose (@uGraph.wGraph.invariants).
  Print uGraph.is_graph_of_uctx.
  destruct (uGraph.gc_of_constraints cstr)
  cbv [
  pose uGraph.make_graph.
  cbv [consistent_extension_on].
  Print consistent.
  Search uGraph.gc_of_constraints.
    S
  Search uGraph.GoodConstraintSet.t ConstraintSet.t.
  (*
  Search consistent_extension_on.
  *)*)
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

Definition valid_constraints_dec cf ϕ cstrs : {@valid_constraints cf ϕ cstrs} + {~@valid_constraints cf ϕ cstrs}.
Proof.
  pose proof (fun G a b c => uGraph.check_constraints_spec (uGraph.make_graph G) (levels_of_cs2 ϕ cstrs, ϕ) a b c cstrs) as H1.
  pose proof (fun G a b c => uGraph.check_constraints_complete (uGraph.make_graph G) (levels_of_cs2 ϕ cstrs, ϕ) a b c cstrs) as H2.
  pose proof (levels_of_cs2_spec ϕ cstrs).
  cbn [fst snd] in *.
  destruct (consistent_dec ϕ); [ | now left; cbv [valid_constraints valid_constraints0 consistent not] in *; break_innermost_match; intros; eauto; exfalso; eauto ].
  destruct_head'_and.
  specialize_under_binders_by assumption.
  cbv [uGraph.is_graph_of_uctx MCOption.on_Some] in *.
  cbv [valid_constraints] in *; break_innermost_match; auto.
  break_innermost_match_hyps.
  { specialize_under_binders_by reflexivity.
    destruct uGraph.check_constraints; specialize_by reflexivity; auto. }
  { rewrite uGraph.gc_consistent_iff in *.
    cbv [uGraph.gc_of_uctx monad_utils.bind monad_utils.ret monad_utils.option_monad MCOption.on_Some] in *; cbn [fst snd] in *.
    break_innermost_match_hyps.
    all: try congruence.
    all: exfalso; assumption. }
Defined.

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
