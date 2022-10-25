From Coq Require Import MSetInterface MSetList MSetAVL MSetFacts MSetProperties MSetDecide.
Require Import Coq.derive.Derive.
Require Import Coq.Bool.Bool.
From MetaCoq.Lob.Util.Tactics Require Import BreakMatch.
From MetaCoq.Template Require Import utils All.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope bs.
Import MCMonadNotation.

Class quotation_of {T} (t : T) := quoted_term_of : Ast.term.
Class ground_quotable T := quote_ground : forall t : T, quotation_of t.
#[export] Existing Instance quote_ground.

Class debug_opt := debug : bool.
#[local] Instance default_debug : debug_opt := false.

Definition make_quotation_of {debug : debug_opt} {T} (t : T) : TemplateMonad (quotation_of t).
Proof.
  simple
    refine
    (qt <- tmQuote t;;
     let tmInferQuotation t
       := (t <- tmUnquote t;;
           v <- (let '(existT_typed_term _ t) := t in tmInferInstance None (quotation_of t));;
           match v with
           | my_Some v => tmReturn v
           | my_None => (if debug then tmPrint (quotation_of t) else tmReturn tt);; tmFail "No typeclass instance"
           end) in
     match qt return TemplateMonad Ast.term with
     | tSort _
     | tConst _ _
     | tConstruct _ _ _
     | tInt _
     | tFloat _
     | tInd _ _
       => tmReturn qt
     | tCast t kind v
       => tmInferQuotation t
     | tApp f args
       => qf <- tmInferQuotation f;;
          qargs <- list_rect
                     (fun _ => _)
                     (tmReturn [])
                     (fun arg args qargs
                      => qarg <- tmInferQuotation arg;;
                         qargs <- qargs;;
                         tmReturn (qarg :: qargs))
                     args;;
          tmReturn (tApp qf qargs)
     | tProj proj t => tmFail "Proj is not reduced"
     | tRel n => tmFail "Rel is not ground"
     | tVar id => tmFail "Var is not ground"
     | tEvar ev args => tmFail "Evar is not ground"
     | tProd na ty body => tmFail "Prod not yet handled"
     | tLambda na ty body => tmFail "Lambda not yet handled"
     | tLetIn na def def_ty body => tmFail "LetIn not yet handled"
     | tCase ci type_info discr branches => tmFail "Case not yet handled"
     | tFix mfix idx => tmFail "Fix not yet handled"
     | tCoFix mfix idx => tmFail "CoFix not yet handled"
     end);
    exact _.
Defined.

Ltac make_quotation_of_goal _ :=
  let t := match goal with |- quotation_of ?t => t end in
  run_template_program (make_quotation_of t) (fun v => exact v).

#[export]
 Hint Extern 1 (quotation_of ?t) => make_quotation_of_goal () : typeclass_instances.
#[export]
 Hint Extern 1 (quotation_of match ?t with _ => _ end) => is_var t; destruct t : typeclass_instances.
#[export]
 Hint Extern 1 (ground_quotable match ?t with _ => _ end) => is_var t; destruct t : typeclass_instances.


#[export] Typeclasses Opaque quotation_of.

#[export] Instance quote_nat : ground_quotable nat := (ltac:(induction 1; exact _)).
#[export] Instance quote_True : ground_quotable True := (ltac:(destruct 1; exact _)).
#[export] Instance quote_False : ground_quotable False := (ltac:(destruct 1; exact _)).
#[export] Instance quote_comparison : ground_quotable comparison := (ltac:(induction 1; exact _)).
#[export] Instance quote_positive : ground_quotable positive := (ltac:(induction 1; exact _)).
#[export] Instance quote_Z : ground_quotable Z := (ltac:(induction 1; exact _)).
#[export] Instance quote_bool : ground_quotable bool := (ltac:(induction 1; exact _)).
#[export] Instance quote_byte : ground_quotable Byte.byte := (ltac:(induction 1; exact _)).
#[export] Instance quote_string : ground_quotable string := (ltac:(induction 1; exact _)).
#[export] Instance quote_list {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (list A) := (ltac:(induction 1; exact _)).
#[export] Instance quote_option {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (option A) := (ltac:(induction 1; exact _)).
#[export] Instance quote_prod {A B} {qA : quotation_of A} {qB : quotation_of B} {quoteA : ground_quotable A} {quoteB : ground_quotable B} : ground_quotable (A × B) := (ltac:(induction 1; exact _)).
#[export] Instance quote_sigT {A P} {qA : quotation_of A} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteP : forall x, quotation_of x -> ground_quotable (P x)} : ground_quotable (@sigT A P) := (ltac:(induction 1; exact _)).
#[export] Instance quote_and {A B : Prop} {qA : quotation_of A} {qB : quotation_of B} {quoteA : ground_quotable A} {quoteB : ground_quotable B} : ground_quotable (A /\ B) := (ltac:(destruct 1; exact _)).
#[export] Instance quote_Level_t : ground_quotable Level.t := (ltac:(induction 1; exact _)).
#[export] Instance quote_LevelExprSet_Raw_elt : ground_quotable LevelExprSet.Raw.elt := (ltac:(induction 1; exact _)).
#[export] Instance quote_LevelExprSet_Raw_t : ground_quotable LevelExprSet.Raw.t := (ltac:(induction 1; exact _)).
#[export] Instance quotation_of_eq_refl {A} {qA : quotation_of A} {a : A} {qa : quotation_of a} : quotation_of (@eq_refl A a) := _.
#[export] Instance quote_eq {A} {qA : quotation_of A} {qA : ground_quotable A} {x y : A} : ground_quotable (x = y :> A) := (ltac:(intros []; exact _)).
#[export] Instance quote_LevelExprSet_Raw_Ok s : ground_quotable (LevelExprSet.Raw.Ok s) := (ltac:(cbv [LevelExprSet.Raw.Ok]; exact _)).
#[export] Instance quote_LevelExprSet_t : ground_quotable LevelExprSet.t := (ltac:(induction 1; exact _)).
#[export] Instance quote_LevelAlgExpr_t : ground_quotable LevelAlgExpr.t := (ltac:(induction 1; exact _)).
#[export] Instance quote_Universe : ground_quotable Universe.t := (ltac:(induction 1; exact _)).
#[export] Instance quote_ident : ground_quotable ident := (ltac:(cbv [ident]; exact _)).
#[export] Instance quote_name : ground_quotable name := (ltac:(induction 1; exact _)).
#[export] Instance quote_relevance : ground_quotable relevance := (ltac:(induction 1; exact _)).
#[export] Instance quote_binder_annot {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (binder_annot A) := (ltac:(induction 1; exact _)).
#[export] Instance quote_aname : ground_quotable aname := _.
#[export] Instance quote_cast_kind : ground_quotable cast_kind := (ltac:(induction 1; exact _)).
#[export] Instance quote_modpath : ground_quotable modpath := (ltac:(induction 1; exact _)).
#[export] Instance quote_kername : ground_quotable kername := (ltac:(induction 1; exact _)).
#[export] Instance quote_Instance_t : ground_quotable Instance.t := _.
#[export] Instance quote_inductive : ground_quotable inductive := (ltac:(induction 1; exact _)).
#[export] Instance quote_case_info : ground_quotable case_info := (ltac:(induction 1; exact _)).
#[export] Instance quote_projection : ground_quotable projection := (ltac:(induction 1; exact _)).
#[export] Instance quote_PrimInt63_int : ground_quotable PrimInt63.int := tInt.
#[export] Instance quote_PrimFloat_float : ground_quotable PrimFloat.float := tFloat.
#[export] Instance quote_predicate {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (predicate A) := (ltac:(induction 1; exact _)).
#[export] Instance quote_branch {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (branch A) := (ltac:(induction 1; exact _)).
#[export] Instance quote_def {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (def A) := (ltac:(induction 1; exact _)).
#[export] Instance quote_mfixpoint {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (mfixpoint A) := _.
#[export] Instance quote_term : ground_quotable term.
Proof.
  hnf. fix quote_term 1; change (ground_quotable term) in quote_term; destruct 1.
  all: make_quotation_of_goal ().
Defined.

Module Import BasicAst.
  #[export] Instance quote_context_decl {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (BasicAst.context_decl A) := (ltac:(induction 1; exact _)).
  #[export] Instance quote_typ_or_sort_ {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (BasicAst.typ_or_sort_ A) := (ltac:(induction 1; exact _)).
End BasicAst.

#[export] Instance quote_context : ground_quotable context := (ltac:(induction 1; exact _)).
Definition quote_Nat_le_dec x y : { p : Nat.le x y & quotation_of p } + {~Nat.le x y}.
Proof.
  destruct (Nat.eq_dec x y); [ left | ].
  { subst; unshelve econstructor; [ constructor | exact _ ]. }
  revert dependent x; induction y as [|y IHy]; intros.
  { destruct x; solve [ exfalso; congruence
                      | right; inversion 1 ]. }
  { destruct (Nat.eq_dec x y).
    { left; subst; unshelve econstructor; [ constructor; constructor | exact _ ]. }
    { specialize (IHy _ ltac:(eassumption)).
      destruct IHy as [[p IHy]|IHy]; [ left; unshelve econstructor; [ constructor; assumption | exact _ ] | right; lia ]. } }
Defined.
Definition Nat_le_dec x y : { Nat.le x y } + {~Nat.le x y}.
Proof.
  destruct (quote_Nat_le_dec x y) as [[? ?]|?]; [ left | right ]; assumption.
Defined.
#[export] Instance quote_Nat_le x y : ground_quotable (Nat.le x y).
Proof.
  intro p; destruct (quote_Nat_le_dec x y) as [[? q]|?]; [ exact q | exfalso; auto ].
Defined.
#[export] Instance quote_Nat_lt x y : ground_quotable (Nat.lt x y) := _.
Derive Level_lt_' SuchThat (forall x y, Level_lt_' x y <-> Level.lt_ x y) As Level_lt_'_lt_.
Proof.
  instantiate (1:=ltac:(intros x y; destruct x, y)) in (value of Level_lt_').
  destruct x, y; subst Level_lt_'; cbn;
    (split;
     [ first [ solve [ instantiate (1 := True); constructor ] | constructor | idtac ]
     | first [ solve [ instantiate (1 := False); inversion 1 ] | inversion 1 | idtac ] ]);
    let G := match goal with |- ?G => G end in
    tryif has_evar G
    then idtac
    else (try solve [ exact I | inversion 1 ]);
    eassumption.
Defined.

Definition ground_quotable_of_bp {b P} (H : b = true -> P) {qH : quotation_of H} (H_for_safety : P -> b = true) : ground_quotable P.
Proof.
  intro p.
  exact (mkApps qH [_ : quotation_of (@eq_refl bool true)]).
Defined.

Definition ground_quotable_neg_of_bp {b P} (H : b = false -> ~P) {qH : quotation_of H} (H_for_safety : ~P -> b = false) : ground_quotable (~P).
Proof.
  intro p.
  exact (mkApps qH [_ : quotation_of (@eq_refl bool false)]).
Defined.

Definition b_of_dec {P} (H : {P} + {~P}) : bool := if H then true else false.
Definition bp_of_dec {P H} : @b_of_dec P H = true -> P.
Proof. cbv [b_of_dec]; destruct H; auto; discriminate. Defined.
Definition pb_of_dec {P:Prop} {H} : P -> @b_of_dec P H = true.
Proof. cbv [b_of_dec]; destruct H; auto; discriminate. Defined.
Definition neg_bp_of_dec {P H} : @b_of_dec P H = false -> ~P.
Proof. cbv [b_of_dec]; destruct H; auto; discriminate. Defined.
Definition neg_pb_of_dec {P:Prop} {H} : ~P -> @b_of_dec P H = false.
Proof. cbv [b_of_dec]; destruct H; tauto. Defined.

Definition list_neq_nil_dec {A} (l : list A) : {l = []} + {l <> []}.
Proof. destruct l; [ left | right ]; try reflexivity; congruence. Defined.
Definition list_beq_nil {A} (l : list A) : bool := b_of_dec (list_neq_nil_dec l).
Definition list_beq_nil_bl {A} (l : list A) : list_beq_nil l = true -> l = [] := bp_of_dec.
Definition list_beq_nil_lb {A} (l : list A) : l = [] -> list_beq_nil l = true := pb_of_dec.
Definition list_nbeq_nil_bl {A} (l : list A) : list_beq_nil l = false -> l <> [] := neg_bp_of_dec.
Definition list_nbeq_nil_lb {A} (l : list A) : l <> [] -> list_beq_nil l = false := neg_pb_of_dec.
#[export] Instance quote_list_neq_nil {A} {qA : quotation_of A} (l : list A) {ql : quotation_of l} : ground_quotable (l <> [])
  := ground_quotable_neg_of_bp (@list_nbeq_nil_bl A l) (@list_nbeq_nil_lb A l).

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
  End with_t.
End QuoteMSetAVL.

Module Type MSetList_MakeWithLeibnizT (T : OrderedTypeWithLeibniz). Include MSetList.MakeWithLeibniz T. End MSetList_MakeWithLeibnizT.

Module QuoteMSetListWithLeibniz (T : OrderedTypeWithLeibniz) (M : MSetList_MakeWithLeibnizT T).
  Module MFact := WFactsOn T M.
  Module MProp := WPropertiesOn T M.
  Module MDecide := WDecide (M).
  Local Ltac msets := MDecide.fsetdec.

  Definition Raw_In_dec x y : {M.Raw.In x y} + {~M.Raw.In x y}.
  Proof.
    cbv [M.Raw.In]; apply InA_dec, T.eq_dec.
  Defined.
  Definition In_dec x y : {M.In x y} + {~M.In x y}.
  Proof.
    cbv [M.In]; apply Raw_In_dec.
  Defined.
  (*
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
    Definition M_Raw_bstb t := if M_Raw_bst_dec t then true else false.
    Definition M_Raw_bstb_bst t : M_Raw_bstb t = true -> M.Raw.bst t.
    Proof.
      cbv [M_Raw_bstb]; destruct M_Raw_bst_dec; auto; discriminate.
    Defined.
    Definition M_Raw_bstb_bst_alt t : M.Raw.bst t -> M_Raw_bstb t = true.
    Proof.
      cbv [M_Raw_bstb]; destruct M_Raw_bst_dec; auto; discriminate.
    Defined.
    #[export] Instance quote_Raw_bst t : ground_quotable (M.Raw.bst t)
      := ground_quotable_of_bp (@M_Raw_bstb_bst t) (@M_Raw_bstb_bst_alt t).
    #[export] Instance quote_Raw_Ok s : ground_quotable (M.Raw.Ok s) := (ltac:(cbv [M.Raw.Ok]; exact _)).
    #[export] Instance quote_t : ground_quotable M.t := (ltac:(induction 1; exact _)).
  End with_t.
*)
End QuoteMSetListWithLeibniz.

Module QuoteLevelSet := QuoteMSetAVL Level LevelSet.
#[export] Instance quote_LevelSet_t : ground_quotable LevelSet.t := QuoteLevelSet.quote_t.
Module QuoteConstraintSet := QuoteMSetAVL UnivConstraint ConstraintSet.
Module QuoteLevelExprSet := QuoteMSetListWithLeibniz LevelExpr LevelExprSet.
#[export] Instance quote_ConstraintType_t : ground_quotable ConstraintType.t := ltac:(destruct 1; exact _).
#[export] Instance quote_ConstraintSet_t : ground_quotable ConstraintSet.t := QuoteConstraintSet.quote_t.
#[export] Instance quote_ContextSet_t : ground_quotable ContextSet.t := (ltac:(induction 1; exact _)).
#[export] Instance quote_Retroknowledge_t : ground_quotable Environment.Retroknowledge.t := (ltac:(induction 1; exact _)).
#[export] Instance quote_universes_decl : ground_quotable universes_decl := (ltac:(induction 1; exact _)).
#[export] Instance quote_constant_body : ground_quotable constant_body := (ltac:(induction 1; exact _)).
#[export] Instance quote_recursivity_kind : ground_quotable recursivity_kind := (ltac:(induction 1; exact _)).
#[export] Instance quote_allowed_eliminations : ground_quotable allowed_eliminations := (ltac:(induction 1; exact _)).
#[export] Instance quote_constructor_body : ground_quotable constructor_body := (ltac:(induction 1; exact _)).
#[export] Instance quote_projection_body : ground_quotable projection_body := (ltac:(induction 1; exact _)).
#[export] Instance quote_one_inductive_body : ground_quotable one_inductive_body := (ltac:(induction 1; exact _)).
#[export] Instance quote_Variance_t : ground_quotable Variance.t := (ltac:(induction 1; exact _)).
#[export] Instance quote_mutual_inductive_body : ground_quotable mutual_inductive_body := (ltac:(induction 1; exact _)).
#[export] Instance quote_global_decl : ground_quotable global_decl := (ltac:(induction 1; exact _)).
#[export] Instance quote_global_declarations : ground_quotable global_declarations := (ltac:(induction 1; exact _)).
#[export] Instance quote_global_env : ground_quotable global_env := (ltac:(induction 1; exact _)).
#[export] Instance quote_global_env_ext : ground_quotable global_env_ext := (ltac:(induction 1; exact _)).
#[export] Instance quote_config_checker_flags : ground_quotable config.checker_flags := (ltac:(induction 1; exact _)).

Module Import Primitive.
  #[export] Instance quote_prim_tag : ground_quotable Primitive.prim_tag := (ltac:(induction 1; exact _)).
End Primitive.

Definition wf_universe_dec Σ s : {@wf_universe Σ s} + {~@wf_universe Σ s}.
Proof.
  destruct s; try (left; exact I).
  cbv [wf_universe Universe.on_sort LevelExprSet.In LevelExprSet.this t_set].
  destruct t as [[t _] _].
  induction t as [|t ts [IHt|IHt]]; [ left | | right ].
  { inversion 1. }
  { destruct (QuoteLevelSet.In_dec (LevelExpr.get_level t) (global_ext_levels Σ)) as [H|H]; [ left | right ].
    { inversion 1; subst; auto. }
    { intro H'; apply H, H'; now constructor. } }
  { intro H; apply IHt; intros; apply H; now constructor. }
Defined.

Definition wf_universeb Σ s := b_of_dec (wf_universe_dec Σ s).
Definition wf_universe_bp Σ s : wf_universeb Σ s = true -> wf_universe Σ s := bp_of_dec.
Definition wf_universe_pb Σ s : wf_universe Σ s -> wf_universeb Σ s = true := pb_of_dec.

#[export] Instance quote_wf_universe {Σ s} : ground_quotable (@wf_universe Σ s) := ground_quotable_of_bp (@wf_universe_bp Σ s) (@wf_universe_pb Σ s).

#[export] Instance quote_valid_constraints {cf ϕ cstrs} : ground_quotable (@valid_constraints cf ϕ cstrs).
cbv [valid_constraints]; destruct uctx; try exact _.
repeat apply @quote_and; try exact _.
#[export] Instance quote_consistent_instance {H lvls ϕ uctx u} : ground_quotable (@consistent_instance H lvls ϕ uctx u).
cbv [consistent_instance]; destruct uctx; try exact _.
repeat apply @quote_and; try exact _.
Print valid_constraints.
Print valid_constraints.
#[export] Instance quote_consistent_instance_ext {H Σ u i} : ground_quotable (@consistent_instance_ext H Σ u i).
cbv [consistent_instance_ext].
cbv [consistent_instance_ext].

Module Import Typing.
  #[export] Instance quote_All_local_env {typing} {qtyping : quotation_of typing} {quote_typing : forall Γ t T, ground_quotable (typing Γ t T)} {Γ} {qΓ : quotation_of Γ} : ground_quotable (@All_local_env typing Γ) := (ltac:(induction 1; exact _)).
  #[local] Hint Extern 1 (_ = _) => reflexivity : typeclass_instances.
  #[export] Instance quote_lift_judgment {check infer_sort}
   {Σ Γ t T}
   {quote_check : forall T', Typ T' = T -> ground_quotable (check Σ Γ t T')}
   {quote_infer_sort : T = Sort -> ground_quotable (infer_sort Σ Γ t)}
    : ground_quotable (@lift_judgment check infer_sort Σ Γ t T)
    := (ltac:(cbv [lift_judgment]; exact _)).
  #[export] Instance quote_infer_sort {sorting} {Σ Γ T} {qsorting : quotation_of (sorting Σ Γ T)} {quote_sorting : forall U, quotation_of U -> ground_quotable (sorting Σ Γ T U)} : ground_quotable (@infer_sort sorting Σ Γ T) := @quote_sigT _ (sorting Σ Γ T) _ _ _ _.
  #[local] Instance quotation_of_compose_tSort {A} (f : _ -> A) {qf : quotation_of f} : quotation_of (fun s => f (tSort s)).
  Proof.
    lazymatch constr:(<% fun s => f (tSort s) %>) with
    | context qt[tVar "f"]
      => let qt := context qt[qf] in
         exact qt
    end.
  Defined.
  #[local] Hint Extern 1 => progress (intros; subst) : typeclass_instances.
  #[export] Instance quote_lift_typing {typing} {Σ Γ t T}
   {quote_typing : forall T', Typ T' = T -> ground_quotable (typing Σ Γ t T')}
   {quote_typing' : forall U, T = Sort -> quotation_of U -> ground_quotable (typing Σ Γ t (tSort U))}
   {qtyping : T = Sort -> quotation_of (typing Σ Γ t)}
    : ground_quotable (@lift_typing typing Σ Γ t T)
    := ltac:(cbv [lift_typing]; exact _).
  Print wf_universe.
  Fixpoint quote_typing' {H Σ Γ t1 t2} (t : @typing H Σ Γ t1 t2) : quotation_of t
  with quote_typing_spine' {H Σ Γ t1 s t2} (t : @typing_spine H Σ Γ t1 s t2) : quotation_of t.
  Proof.
    all: change (forall H Σ Γ t1 t2, ground_quotable (@typing H Σ Γ t1 t2)) in quote_typing'.
    all: change (forall H Σ Γ t1 s t2, ground_quotable (@typing_spine H Σ Γ t1 s t2)) in quote_typing_spine'.
    all: destruct t.
    exact _.
    exact _.
    exact _.
    exact _.
    exact _.
    exact _.
    exact _.
    all: revgoals. 2: exact _. all: revgoals.
    Guarded.
    pose (_ : quotation_of H).
    pose (_ : quotation_of Σ).
    pose (_ : quotation_of Γ).
    pose (_ : quotation_of cst).
    pose (_ : quotation_of u).
    pose (_ : quotation_of a).
    pose (_ : quotation_of decl).
    pose (_ : quotation_of isdecl).
    Print consistent_instance_ext.
    pose (_ : quotation_of c).
    pose (_ : quotation_of e).
    pose (_ : quotation_of n).
    pose (_ : quotation_of t1).
    exact _.
    Guarded.
    HERE
    pose (_ : quotation_of w).
    Guarded.
    Guarded.
    Set Printing All.
    assert (quotation_of a).
    { eapply @quote_All_local_env; try exact _.
      intros; eapply @quote_lift_typing; try exact _.

    pose (true : debug_opt).
    try make_quotation_of_goal ().
  Set Printing All.
  pose (_ : quotation_of a).
Module Import PCUICTyping.
  #[export] Instance quote_typing {checker_flags Σ Γ x T} : ground_quotable (@PCUICTyping.typing checker_flags Σ Γ x T).
  Proof.
    hnf. fix quote_typing 1; change (ground_quotable (@PCUICTyping.typing checker_flags Σ Γ x T)) in quote_typing; destruct 1.
    Typeclasses eauto := debug.
    all: try make_quotation_of_goal ().
    pose (_ : quotation_of n).
    pose (_ : quotation_of decl).
    pose (_ : quotation_of e).
    pose (_ : quotation_of a).
  Defined.
