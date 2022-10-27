From Coq Require Import MSetInterface MSetList MSetAVL MSetFacts MSetProperties MSetDecide.
Require Import Coq.Bool.Bool.
From MetaCoq.Lob Require Import TermUtils.
From MetaCoq.Lob.Util.Tactics Require Import
     BreakMatch
     DestructHead.
From MetaCoq.Template Require Import MonadBasicAst MonadAst utils All.
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

Fixpoint replace_quotation_of {debug : debug_opt} (qt : term) : TemplateMonad term.
Proof.
  specialize (replace_quotation_of debug).
  simple
    refine
    (let tmInferQuotation t
       := (t <- tmUnquote t;;
           v <- (let '(existT_typed_term _ t) := t in tmInferInstance None (quotation_of t));;
           match v with
           | my_Some v => tmReturn v
           | my_None => (if debug then tmPrint (quotation_of t) else tmReturn tt);; tmFail "No typeclass instance"
           end) in
     match qt return TemplateMonad Ast.term with
     | tRel _
     | tSort _
     | tConstruct _ _ _
     | tInt _
     | tFloat _
     | tConst _ _
     | tInd _ _
       => ret qt
     | tVar id
       => tmInferQuotation qt
     | tEvar ev args => args <- monad_map replace_quotation_of args;; ret (tEvar ev args)
     | tLambda na T M => T <- replace_quotation_of T;; M <- replace_quotation_of M;; ret (tLambda na T M)
     | tApp u v => u <- replace_quotation_of u;; v <- monad_map replace_quotation_of v;; ret (mkApps u v)
     | tProd na A B => A <- replace_quotation_of A;; B <- replace_quotation_of B;; ret (tProd na A B)
     | tCast c kind ty => c <- replace_quotation_of c;; ty <- replace_quotation_of ty;; ret (tCast c kind ty)
     | tLetIn na b ty b' => b <- replace_quotation_of b;; ty <- replace_quotation_of ty;; b' <- replace_quotation_of b';; ret (tLetIn na b ty b')
     | tProj p c => replace_quotation_of c;; ret (tProj p c)
     | tFix mfix idx =>
         mfix' <- monad_map (monad_map_def (TM:=TypeInstance) replace_quotation_of replace_quotation_of) mfix;;
         ret (tFix mfix' idx)
     | tCoFix mfix idx =>
         mfix' <- monad_map (monad_map_def (TM:=TypeInstance) replace_quotation_of replace_quotation_of) mfix;;
         ret (tCoFix mfix' idx)
     | tCase ind p c brs =>
         p' <- monad_map_predicate (TM:=TypeInstance) ret replace_quotation_of replace_quotation_of p;;
         brs' <- monad_map_branches (TM:=TypeInstance) replace_quotation_of brs;;
         c <- replace_quotation_of c;;
         ret (tCase ind p' c brs')
     end); exact _.
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

Ltac replace_quotation_of_goal _ :=
  let G := match goal with |- quotation_of ?G => G end in
  tryif is_var G
  then fail "Avoiding loops"
  else run_template_program (replace_quotation_of <% G %>) (fun v => exact v).

#[export]
 Hint Extern 1 (quotation_of _) => replace_quotation_of_goal () : typeclass_instances.

Ltac quote_true_ground_goal _ :=
  lazymatch goal with
  | [ H : _ |- quotation_of _ ]
    => clear H; quote_true_ground_goal ()
  | [ |- quotation_of ?x ] => exact <% x %>
  end.
#[export]
 Hint Extern 1 (quotation_of _) => quote_true_ground_goal () : typeclass_instances.

#[export] Typeclasses Opaque quotation_of.

#[export] Instance quote_nat : ground_quotable nat := (ltac:(induction 1; exact _)).
#[export] Instance quote_True : ground_quotable True := (ltac:(destruct 1; exact _)).
#[export] Instance quote_unit : ground_quotable unit := (ltac:(destruct 1; exact _)).
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
#[export] Instance quote_ssrbool_and3 {A B C : Prop} {qA : quotation_of A} {qB : quotation_of B} {qC : quotation_of C} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteC : ground_quotable C} : ground_quotable (ssrbool.and3 A B C) := (ltac:(destruct 1; exact _)).
#[export] Instance quote_and4 {A B C D} {qA : quotation_of A} {qB : quotation_of B} {qC : quotation_of C} {qD : quotation_of D} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteC : ground_quotable C} {quoteD : ground_quotable D} : ground_quotable (and4 A B C D) := (ltac:(destruct 1; exact _)).
(* XXX MOVE ME *)
(** Transparent version of [proj1], [proj2] *)
Definition proj1 {A B} (x : A /\ B) : A := let (a, b) := x in a.
Definition proj2 {A B} (x : A /\ B) : B := let (a, b) := x in b.
(* TODO: Move *)
Local Notation iffT A B := ((A -> B) × (B -> A)).
Definition quote_of_iff {A B : Prop} {quoteA : ground_quotable A} {qA : quotation_of A} {qB : quotation_of B} (H : A <-> B) {qH : quotation_of H} : ground_quotable B.
Proof.
  intro b.
  change (@quotation_of B (proj1 H (proj2 H b))).
  exact _.
Defined.
Definition quote_of_iffT {A B} {quoteA : ground_quotable A} {qA : quotation_of A} {qB : quotation_of B} (H : iffT A B) {qH : quotation_of H} : ground_quotable B.
Proof.
  intro b.
  change (@quotation_of B (fst H (snd H b))).
  exact _.
Defined.
Lemma iff_forall_eq_some {A v P} : iffT match v return Type with Some v => P v | None => True end (forall a : A, v = Some a -> P a).
Proof.
  split; destruct v; auto; intros ??; inversion 1; subst; assumption.
Defined.
Lemma iff_forall_neq_nil {A} {v : list A} {P} : iffT match v return Type with nil => True | _ => P end (v <> nil -> P).
Proof.
  split; destruct v; intuition congruence.
Defined.
#[export] Instance quote_forall_eq_some {A v P} {q : ground_quotable (match v return Type with Some v => P v | None => True end)} {qv : quotation_of v} {qA : quotation_of A} {qP : quotation_of P} : ground_quotable (forall a : A, v = Some a -> P a)
  := quote_of_iffT iff_forall_eq_some.
#[export] Instance quote_forall_neq_nil {A v P} {q : ground_quotable (match v return Type with nil => True | _ => P end)} {qv : quotation_of v} {qA : quotation_of A} {qP : quotation_of P} : ground_quotable (v <> @nil A -> P)
  := quote_of_iffT iff_forall_neq_nil.
#[export] Instance quote_is_true_or_l {b} {P : Prop} {qP : quotation_of P} {quoteP : ground_quotable P} : ground_quotable (is_true b \/ P).
Proof.
  destruct b; intro H; [ | assert (H' : P) by now destruct H ].
  all: [ > let f := match goal with |- ?f _ => f end in
           change (f (or_introl eq_refl))
       | let f := match goal with |- ?f _ => f end in
         change (f (or_intror H')) ].
  all: exact _.
Defined.
#[export] Instance quote_is_true_or_r {b} {P : Prop} {qP : quotation_of P} {quoteP : ground_quotable P} : ground_quotable (P \/ is_true b).
Proof.
  destruct b; intro H; [ | assert (H' : P) by now destruct H ].
  all: [ > let f := match goal with |- ?f _ => f end in
           change (f (or_intror eq_refl))
       | let f := match goal with |- ?f _ => f end in
         change (f (or_introl H')) ].
  all: exact _.
Defined.
#[export] Instance quote_Level_t : ground_quotable Level.t := (ltac:(induction 1; exact _)).
#[export] Instance quote_LevelExprSet_Raw_elt : ground_quotable LevelExprSet.Raw.elt := (ltac:(induction 1; exact _)).
#[export] Instance quote_LevelExprSet_Raw_t : ground_quotable LevelExprSet.Raw.t := (ltac:(induction 1; exact _)).
#[export] Instance quotation_of_eq_refl {A} {qA : quotation_of A} {a : A} {qa : quotation_of a} : quotation_of (@eq_refl A a) := _.
#[export] Instance quote_eq {A} {qA : quotation_of A} {qA : ground_quotable A} {x y : A} : ground_quotable (x = y :> A) := (ltac:(intros []; exact _)).
#[export] Instance quote_All {A R ls} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x, ground_quotable (R x)} : ground_quotable (@All A R ls) := ltac:(induction 1; exact _).
#[export] Instance quote_All2 {A B R lsA lsB} {qA : quotation_of A} {qB : quotation_of B} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteR : forall x y, ground_quotable (R x y)} : ground_quotable (@All2 A B R lsA lsB) := ltac:(induction 1; exact _).
(* TODO: Move *)
Definition Forall2_hd {A B R x xs y ys} (H : @Forall2 A B R (x :: xs) (y :: ys)) : R x y.
Proof.
  refine match H in Forall2 _ xs ys return match xs, ys with
                                           | x :: xs, y :: ys => R x y
                                           | _, _ => True
                                           end with
         | Forall2_nil => I
         | Forall2_cons _ _ _ _ _ _ => _
         end; assumption.
Defined.
Definition Forall2_tl {A B R x xs y ys} (H : @Forall2 A B R (x :: xs) (y :: ys)) : Forall2 R xs ys.
Proof.
  refine match H in Forall2 _ xs ys return match xs, ys with
                                           | x :: xs, y :: ys => Forall2 R xs ys
                                           | _, _ => True
                                           end with
         | Forall2_nil => I
         | Forall2_cons _ _ _ _ _ _ => _
         end; assumption.
Defined.
#[export] Instance quote_Forall2 {A B R lsA lsB} {qA : quotation_of A} {qB : quotation_of B} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteR : forall x y, ground_quotable (R x y:Prop)} : ground_quotable (@Forall2 A B R lsA lsB).
Proof.
  revert lsB; induction lsA as [|a lsA IH], lsB as [|b lsB]; intro pf;
    try solve [ exfalso; inversion pf ];
    try (pose proof (Forall2_hd pf);
         pose proof (Forall2_tl pf));
    let f := match goal with |- ?f _ => f end in
    unshelve (let v := open_constr:(f ltac:(econstructor)) in
              change v);
    try (eapply Forall2_hd; eassumption);
    try (eapply Forall2_tl; eassumption);
    try exact _.
Defined.
#[export] Instance quote_All2i {A B R n lsA lsB} {qA : quotation_of A} {qB : quotation_of B} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteR : forall n x y, ground_quotable (R n x y)} : ground_quotable (@All2i A B R n lsA lsB) := ltac:(induction 1; exact _).
#[export] Instance quote_Alli {A P n ls} {qA : quotation_of A} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteP : forall n x, ground_quotable (P n x)} : ground_quotable (@Alli A P n ls) := ltac:(induction 1; exact _).
#[export] Instance quote_OnOne2 {A R lsA lsB} {qA : quotation_of A} {qR : quotation_of R} {quoteA : ground_quotable A} {quoteR : forall x y, ground_quotable (R x y)} : ground_quotable (@OnOne2 A R lsA lsB) := ltac:(induction 1; exact _).
#[export] Instance quote_OnOne2All {A B P lsB lsA1 lsA2} {qA : quotation_of A} {qB : quotation_of B} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteB : ground_quotable B} {quoteP : forall b x y, ground_quotable (P b x y)} : ground_quotable (@OnOne2All A B P lsB lsA1 lsA2) := ltac:(induction 1; exact _).
#[export] Instance quote_All2_fold {A P ls1 ls2} {qA : quotation_of A} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteP : forall x y z w, ground_quotable (P x y z w)} : ground_quotable (@All2_fold A P ls1 ls2) := ltac:(induction 1; exact _).

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
  Definition Inb x y := b_of_dec (In_dec x y).
  Definition Inb_bp x y : Inb x y = true -> M.In x y := bp_of_dec.
  Definition Inb_pb x y : M.In x y -> Inb x y = true := pb_of_dec.

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

    #[export] Instance quote_In x y : ground_quotable (M.In x y)
      := ground_quotable_of_bp (@Inb_bp x y) (@Inb_pb x y).

    Definition Raw_For_all_alt (P : M.elt -> Prop) : M.Raw.t -> Prop
      := fix Raw_For_all_alt (s : M.Raw.t) : Prop
        := match s with
           | M.Raw.Leaf => True
           | M.Raw.Node z l n r => Raw_For_all_alt l /\ P n /\ Raw_For_all_alt r
           end.
    Definition For_all_alt (P : M.elt -> Prop) (s : M.t) : Prop
      := Raw_For_all_alt P (M.this s).
    #[local] Hint Constructors M.Raw.InT : core typeclass_instances.
    #[local] Hint Extern 1 (T.eq _ _) => reflexivity : core.
    Lemma For_all_alt_iff P {P_Proper : Proper (T.eq ==> Basics.impl) P} s
      : M.For_all P s <-> For_all_alt P s.
    Proof using Type.
      cbv [For_all_alt M.For_all M.In M.Raw.In M.this]; destruct s as [s _].
      split; induction s; cbn; intro H'; auto; try inversion 1; subst; repeat apply conj; destruct_head'_and.
      all: (idtac + (eapply P_Proper; (idtac + symmetry))); now eauto.
    Defined.
    Definition For_all_alt1 {P} {P_Proper : Proper (T.eq ==> Basics.impl) P} {s}
      : M.For_all P s -> For_all_alt P s.
    Proof. apply For_all_alt_iff; assumption. Defined.
    Definition For_all_alt2 {P} {P_Proper : Proper (T.eq ==> Basics.impl) P} {s}
      : For_all_alt P s -> M.For_all P s.
    Proof. apply For_all_alt_iff; assumption. Defined.
    #[export] Instance quote_For_all_alt {P s} {quote_P : forall x, M.In x s -> ground_quotable (P x:Prop)} {qP : quotation_of P} : ground_quotable (For_all_alt P s).
    Proof.
      cbv [For_all_alt M.For_all M.In M.Raw.In M.this] in *; destruct s as [s _].
      induction s; cbn [Raw_For_all_alt]; try exact _.
      apply @quote_and; try exact _.
      2: apply @quote_and; try exact _.
      all: eauto.
    Defined.
    #[export] Instance quote_For_all {P s} {quote_P : forall x, M.In x s -> ground_quotable (P x:Prop)} {qP : quotation_of P} {P_Proper : Proper (T.eq ==> Basics.impl) P} {qP_Proper : quotation_of P_Proper} : ground_quotable (M.For_all P s).
    Proof.
      intro pf.
      let f := match goal with |- ?f _ => f end in
      change (f (For_all_alt2 (For_all_alt1 pf))).
      exact _.
    Defined.
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
End QuoteMSetListWithLeibniz.

#[export] Instance quote_ConstraintType_t : ground_quotable ConstraintType.t := ltac:(destruct 1; exact _).

Module QuoteLevelSet := QuoteMSetAVL Level LevelSet.
#[export] Instance quote_LevelSet_t : ground_quotable LevelSet.t := QuoteLevelSet.quote_t.
#[export] Instance quote_LevelSet_In {x y} : ground_quotable (LevelSet.In x y) := QuoteLevelSet.quote_In x y.
#[export] Existing Instance QuoteLevelSet.quote_For_all.
Module QuoteConstraintSet := QuoteMSetAVL UnivConstraint ConstraintSet.
#[export] Instance quote_ConstraintSet_t : ground_quotable ConstraintSet.t := QuoteConstraintSet.quote_t.
#[export] Instance quote_ConstraintSet_In {x y} : ground_quotable (ConstraintSet.In x y) := QuoteConstraintSet.quote_In x y.
#[export] Existing Instance QuoteConstraintSet.quote_For_all.
Module QuoteLevelExprSet := QuoteMSetListWithLeibniz LevelExpr LevelExprSet.
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
#[export] Instance quote_primitive_invariants cdecl : ground_quotable (primitive_invariants cdecl) := _.

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

Definition consistent_dec ctrs : {@consistent ctrs} + {~@consistent ctrs}.
Proof.
  destruct (@gc_consistent_iff config.default_checker_flags ctrs) as [f1 f2].
  cbv [on_Some] in *; destruct @gc_of_constraints.
Admitted.
Definition consistent_b ctrs : bool := b_of_dec (@consistent_dec ctrs).
Definition consistent_bp ctrs : @consistent_b ctrs = true -> @consistent ctrs := bp_of_dec.
Definition consistent_pb ctrs : @consistent ctrs -> @consistent_b ctrs = true := pb_of_dec.
#[export] Instance quote_consistent {ctrs} : ground_quotable (@consistent ctrs)
  := ground_quotable_of_bp (@consistent_bp ctrs) (@consistent_pb ctrs).

Definition valid_constraints_dec cf ϕ cstrs : {@valid_constraints cf ϕ cstrs} + {~@valid_constraints cf ϕ cstrs}.
Proof.
  pose proof (fun G uctx a b c => check_constraints_spec (make_graph G) (uctx, ϕ) a b c cstrs) as H1.
  pose proof (fun G uctx a b c => check_constraints_complete (make_graph G) (uctx, ϕ) a b c cstrs) as H2.
  cbn [fst snd] in *.
  cbv [valid_constraints] in *; break_match; try solve [ left; exact I ].
  specialize (fun G uctx a b c => H2 G uctx a b c eq_refl).
  cbv [is_graph_of_uctx on_Some global_uctx_invariants uctx_invariants] in *; cbn [fst snd] in *.
Admitted.

Definition valid_constraints_b cf ϕ cstrs : bool := b_of_dec (@valid_constraints_dec cf ϕ cstrs).
Definition valid_constraints_bp cf ϕ cstrs : @valid_constraints_b cf ϕ cstrs = true -> @valid_constraints cf ϕ cstrs := bp_of_dec.
Definition valid_constraints_pb cf ϕ cstrs : @valid_constraints cf ϕ cstrs -> @valid_constraints_b cf ϕ cstrs = true := pb_of_dec.
#[export] Instance quote_valid_constraints {cf ϕ cstrs} : ground_quotable (@valid_constraints cf ϕ cstrs)
  := ground_quotable_of_bp (@valid_constraints_bp cf ϕ cstrs) (@valid_constraints_pb cf ϕ cstrs).
#[export] Instance quote_consistent_instance {H lvls ϕ uctx u} : ground_quotable (@consistent_instance H lvls ϕ uctx u) := ltac:(cbv [consistent_instance]; destruct uctx; try exact _).
#[export] Instance quote_consistent_instance_ext {H Σ u i} : ground_quotable (@consistent_instance_ext H Σ u i) := _.

Definition eq_levelalg_dec {cf ϕ u u'} : {@eq_levelalg cf ϕ u u'} + {~@eq_levelalg cf ϕ u u'}.
Proof.
  destruct (gc_eq_levelalg_iff ϕ u u') as [f1 f2].
  cbv [on_Some_or_None] in *.
  destruct gc_of_constraints; auto.
  cbv [gc_eq_levelalg] in *.
  cbv [gc_eq0_levelalg] in *.
  break_innermost_match_hyps; try solve [ left; auto ].
Admitted.
Definition eq_levelalg_b cf ϕ u u' : bool := b_of_dec (@eq_levelalg_dec cf ϕ u u').
Definition eq_levelalg_bp cf ϕ u u' : @eq_levelalg_b cf ϕ u u' = true -> @eq_levelalg cf ϕ u u' := bp_of_dec.
Definition eq_levelalg_pb cf ϕ u u' : @eq_levelalg cf ϕ u u' -> @eq_levelalg_b cf ϕ u u' = true := pb_of_dec.
#[export] Instance quote_eq_levelalg {cf ϕ u u'} : ground_quotable (@eq_levelalg cf ϕ u u')
  := ground_quotable_of_bp (@eq_levelalg_bp cf ϕ u u') (@eq_levelalg_pb cf ϕ u u').
Definition leq_levelalg_n_dec {cf n ϕ u u'} : {@leq_levelalg_n cf n ϕ u u'} + {~@leq_levelalg_n cf n ϕ u u'}.
Proof.
  destruct (@gc_leq_levelalg_n_iff cf n ϕ u u') as [f1 f2].
  cbv [on_Some_or_None] in *.
  destruct gc_of_constraints; auto.
  cbv [gc_leq_levelalg_n] in *.
  cbv [gc_leq0_levelalg_n] in *.
  break_innermost_match_hyps; try solve [ left; auto ].
Admitted.
Definition leq_levelalg_n_b cf n ϕ u u' : bool := b_of_dec (@leq_levelalg_n_dec cf n ϕ u u').
Definition leq_levelalg_n_bp cf n ϕ u u' : @leq_levelalg_n_b cf n ϕ u u' = true -> @leq_levelalg_n cf n ϕ u u' := bp_of_dec.
Definition leq_levelalg_n_pb cf n ϕ u u' : @leq_levelalg_n cf n ϕ u u' -> @leq_levelalg_n_b cf n ϕ u u' = true := pb_of_dec.
#[export] Instance quote_leq_levelalg_n {cf n ϕ u u'} : ground_quotable (@leq_levelalg_n cf n ϕ u u')
  := ground_quotable_of_bp (@leq_levelalg_n_bp cf n ϕ u u') (@leq_levelalg_n_pb cf n ϕ u u').
#[export] Instance quote_eq_universe_ {CS eq_levelalg ϕ s s'} {qeq_levelalg : forall u u', ground_quotable (eq_levelalg ϕ u u':Prop)} : ground_quotable (@eq_universe_ CS eq_levelalg ϕ s s') := ltac:(cbv [eq_universe_]; exact _).
#[export] Instance quote_eq_universe {cf ϕ s s'} : ground_quotable (@eq_universe cf ϕ s s') := _.
#[export] Instance quote_leq_universe_n_ {cf CS leq_levelalg_n n ϕ s s'} {qleq_levelalg_n : forall n u u', ground_quotable (leq_levelalg_n n ϕ u u':Prop)} : ground_quotable (@leq_universe_n_ cf CS leq_levelalg_n n ϕ s s') := ltac:(cbv [leq_universe_n_]; exact _).
#[export] Instance quote_leq_universe {cf ϕ s s'} : ground_quotable (@leq_universe cf ϕ s s') := _.
#[export] Instance quote_is_lSet {cf ϕ s} : ground_quotable (@is_lSet cf ϕ s) := _.
#[export] Instance quote_is_allowed_elimination {cf ϕ allowed u} : ground_quotable (@is_allowed_elimination cf ϕ allowed u) := ltac:(destruct allowed; exact _).
#[export] Instance quote_conv_pb : ground_quotable conv_pb := ltac:(destruct 1; exact _).

#[export] Instance quote_compare_universe {cf pb ϕ s s'} : ground_quotable (@compare_universe cf pb ϕ s s') := ltac:(destruct pb; exact _).

Module Import TermEquality.
  #[export] Instance quote_R_universe_variance {Re Rle v u u'} {qRe : quotation_of Re} {qRle : quotation_of Rle} {quote_Re : forall x y, ground_quotable (Re x y:Prop)} {quote_Rle : forall x y, ground_quotable (Rle x y:Prop)} : ground_quotable (@TermEquality.R_universe_variance Re Rle v u u') := ltac:(cbv [TermEquality.R_universe_variance]; exact _).
  #[export] Instance quote_R_universe_instance_variance {Re Rle v u u'} {qRe : quotation_of Re} {qRle : quotation_of Rle} {quote_Re : forall x y, ground_quotable (Re x y:Prop)} {quote_Rle : forall x y, ground_quotable (Rle x y:Prop)} : ground_quotable (@TermEquality.R_universe_instance_variance Re Rle v u u')
    := ltac:(revert u' v; induction u, u', v; cbn [TermEquality.R_universe_instance_variance]; exact _).
  #[export] Instance quote_R_opt_variance {Re Rle v l1 l2} {qRe : quotation_of Re} {qRle : quotation_of Rle} {quote_Re : forall x y, ground_quotable (Re x y:Prop)} {quote_Rle : forall x y, ground_quotable (Rle x y:Prop)} : ground_quotable (@TermEquality.R_opt_variance Re Rle v l1 l2) := ltac:(destruct v; exact _).
  #[export] Instance quote_eq_term_upto_univ_napp {H Re Rle napp t u} {qRe : quotation_of Re} {qRle : quotation_of Rle} {quote_Re : forall x y, ground_quotable (Re x y:Prop)} {quote_Rle : forall x y, ground_quotable (Rle x y:Prop)} : ground_quotable (@TermEquality.eq_term_upto_univ_napp H Re Rle napp t u).
  Proof.
    intro v; revert v.
    cbv [ground_quotable]; revert Re Rle napp t u qRe qRle quote_Re quote_Rle.
    fix quote_eq_term_upto_univ_napp 10.
    change (forall Re Rle napp t u, quotation_of Re -> quotation_of Rle -> (forall x y, ground_quotable (Re x y:Prop)) -> (forall x y, ground_quotable (Rle x y:Prop)) -> ground_quotable (@TermEquality.eq_term_upto_univ_napp H Re Rle napp t u)) in quote_eq_term_upto_univ_napp.
    intros; destruct v; exact _.
  Defined.
  #[export] Instance quote_compare_term {H pb Σ ϕ t u} : ground_quotable (@TermEquality.compare_term H pb Σ ϕ t u) := _.
End TermEquality.

#[export] Instance quote_red1 {Σ Γ t1 t2} : ground_quotable (@red1 Σ Γ t1 t2).
Proof.
  cbv [ground_quotable]; intro pf; revert Γ t1 t2 pf.
  fix quote_red1 4; change (forall Γ t1 t2, ground_quotable (@red1 Σ Γ t1 t2)) in quote_red1; intros.
  destruct pf; exact _.
Defined.

#[export] Instance quote_cumul_gen {H Σ Γ pb t u} : ground_quotable (@cumul_gen H Σ Γ pb t u) := ltac:(induction 1; exact _).
#[export] Instance quote_declared_cstr_levels {levels c} : ground_quotable (@declared_cstr_levels levels c) := ltac:(cbv [declared_cstr_levels]; exact _).

Module Import TemplateConversion.
  #[export] Instance quote_All_decls_alpha_pb {pb P d d'} {qP : quotation_of P} {quoteP : forall t t', ground_quotable (P pb t t')} {quotePc : forall t t', ground_quotable (P Conv t t')} : ground_quotable (@TemplateConversion.All_decls_alpha_pb pb P d d') := ltac:(induction 1; exact _).
  #[export] Instance quote_cumul_ctx_rel {cumul_gen Σ Γ Δ Δ'} {qcumul_gen : quotation_of cumul_gen} {quote_cumul_gen : forall x pb t t', ground_quotable (cumul_gen Σ (app_context Γ x) pb t t')} : ground_quotable (@TemplateConversion.cumul_ctx_rel cumul_gen Σ Γ Δ Δ') := _.
End TemplateConversion.

Module Import Typing.
  #[export] Instance quote_ctx_inst {Σ Γ} {typing} {qtyping : quotation_of typing} {quote_typing : forall t T, ground_quotable (typing Σ Γ t T)} {inst Δ} : ground_quotable (@ctx_inst typing Σ Γ inst Δ) := (ltac:(induction 1; exact _)).
  #[export] Instance quote_All_local_env {typing} {qtyping : quotation_of typing} {quote_typing : forall Γ t T, ground_quotable (typing Γ t T)} {Γ} : ground_quotable (@All_local_env typing Γ) := (ltac:(induction 1; exact _)).
  #[local] Hint Extern 1 (_ = _) => reflexivity : typeclass_instances.
  #[export] Instance quote_lift_judgment {check infer_sort}
   {Σ Γ t T}
   {quote_check : forall T', Typ T' = T -> ground_quotable (check Σ Γ t T')}
   {quote_infer_sort : T = Sort -> ground_quotable (infer_sort Σ Γ t)}
    : ground_quotable (@lift_judgment check infer_sort Σ Γ t T)
    := (ltac:(cbv [lift_judgment]; exact _)).
  #[export] Instance quote_infer_sort {sorting} {Σ Γ T} {qsorting : quotation_of (sorting Σ Γ T)} {quote_sorting : forall U, quotation_of U -> ground_quotable (sorting Σ Γ T U)} : ground_quotable (@infer_sort sorting Σ Γ T) := @quote_sigT _ (sorting Σ Γ T) _ _ _ _.
  #[local] Instance quotation_of_compose_tSort {A} (f : _ -> A) {qf : quotation_of f} : quotation_of (fun s => f (tSort s)) := _.
  #[local] Hint Extern 1 => progress (intros; subst) : typeclass_instances.
  #[local] Hint Extern 1 => progress cbv beta zeta : typeclass_instances.
  #[export] Instance quote_lift_typing {typing} {Σ Γ t T}
   {quote_typing : forall T', Typ T' = T -> ground_quotable (typing Σ Γ t T')}
   {quote_typing' : forall U, T = Sort -> quotation_of U -> ground_quotable (typing Σ Γ t (tSort U))}
   {qtyping : T = Sort -> quotation_of (typing Σ Γ t)}
    : ground_quotable (@lift_typing typing Σ Γ t T)
    := ltac:(cbv [lift_typing]; exact _).

  Fixpoint quote_typing' {H Σ Γ t1 t2} (t : @typing H Σ Γ t1 t2) : quotation_of t
  with quote_typing_spine' {H Σ Γ t1 s t2} (t : @typing_spine H Σ Γ t1 s t2) : quotation_of t.
  Proof.
    all: change (forall H Σ Γ t1 t2, ground_quotable (@typing H Σ Γ t1 t2)) in quote_typing'.
    all: change (forall H Σ Γ t1 s t2, ground_quotable (@typing_spine H Σ Γ t1 s t2)) in quote_typing_spine'.
    all: destruct t; exact _.
  Defined.

  #[export] Instance quote_typing {H Σ Γ t1 t2} : ground_quotable (@typing H Σ Γ t1 t2) := quote_typing'.
  #[export] Instance quote_typing_spine {H Σ Γ t1 s t2} : ground_quotable (@typing_spine H Σ Γ t1 s t2) := quote_typing_spine'.

  #[export] Instance quote_on_global_univs {c} : ground_quotable (@on_global_univs c) := _.
  #[export] Instance quote_on_constant_decl {P Σ d} {quote_P : forall trm, cst_body d = Some trm -> ground_quotable (P Σ [] trm (Typ (cst_type d)))} {quote_P' : cst_body d = None -> ground_quotable (P Σ [] (cst_type d) Sort)} : ground_quotable (@on_constant_decl P Σ d).
  Proof.
    cbv [on_constant_decl].
    destruct (cst_body d); exact _.
  Defined.
  #[export] Instance quote_on_variance {cf Σ univs variances} : ground_quotable (@on_variance cf Σ univs variances) := ltac:(cbv [on_variance]; exact _).
  #[export] Instance quote_on_context {P Σ ctx} {qP : quotation_of P} {quote_P : forall Γ t T, ground_quotable (P Σ Γ t T)} : ground_quotable (@on_context P Σ ctx) := _.
  #[local]
   Hint Extern 1 (ground_quotable match ?t with _ => _ end) => destruct t : typeclass_instances.
  Print on_constructor.
  #[export] Instance quote_on_constructor {cf Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs} : ground_quotable (@on_constructor cf Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs). destruct 1; try exact _.
    repeat match goal with
           | [ H : quotation_of ?x |- _ ] => revert x H
           | [ x : _ |- _ ] => generalize (_ : quotation_of x); revert x
           end.
  #[export] Instance quote_on_constructors {cf Pcmp P Σ mdecl idecl ind_indices} : ground_quotable (@on_constructors cf Pcmp P Σ mdecl idecl ind_indices) := ltac:(cbv [on_constructors]; exact _).
  Print on_projections.
  #[export] Instance quote_ind_respects_variance {Pcmp Σ mdecl v indices} {qPcmp : quotation_of Pcmp} {quote_Pcmp : forall u l0 Γ pb t t', ground_quotable (Pcmp (Σ, u) (app_context (subst_instance l0 (smash_context [] (ind_params mdecl))) Γ) pb t t')} : ground_quotable (@ind_respects_variance Pcmp Σ mdecl v indices) := ltac:(cbv [ind_respects_variance]; destruct variance_universes; exact _).
  #[export] Instance quote_on_ind_body {cf Pcmp P Σ mind mdecl i idecl} {qPcmp : quotation_of Pcmp} {qP : quotation_of P} {quote_Pcmp : forall u l0 Γ pb t t', ground_quotable (Pcmp (fst_ctx Σ, u) (app_context (subst_instance l0 (smash_context [] (ind_params mdecl))) Γ) pb t t')} : ground_quotable (@on_ind_body cf Pcmp P Σ mind mdecl i idecl).
  Proof.
    destruct 1; try exact _.
    repeat match goal with
           | [ H : quotation_of ?x |- _ ] => revert x H
           | [ x : _ |- _ ] => generalize (_ : quotation_of x); revert x
           end.
    Print ch
    assert (quotation_of onIndices).
    apply @quote_ground.
    apply @quote_forall_eq_some.
    exact _.
    { break_innermost_match; try exact _.
      eapply @quote_ind_respects_variance; try exact _; intros.
      Set Printing All.
      assert ().
    cbv [ground_quotable] in f.
    Set Printing Implicit.
    eapply f.
    Print ind_respects_variance.
    Locate on_ind_body.
  #[export] Instance quote_on_inductive {cf Pcmp P Σ mind mdecl} {qPcmp : quotation_of Pcmp} {qP : quotation_of P} {quote_P : forall Γ t T, ground_quotable (P Σ Γ t T)} : ground_quotable (@on_inductive cf Pcmp P Σ mind mdecl).
  Proof.
    destruct 1; try exact _.
    repeat match goal with
           | [ H : quotation_of ?x |- _ ] => revert x H
           | [ x : _ |- _ ] => generalize (_ : quotation_of x); revert x
           end.
    assert (quotation_of onInductives).
    { apply @quote_Alli.
      all: try exact _.
    cbv [on_inductive]; try exact _.
  #[export] Instance quote_on_global_decl {cf Pcmp P Σ kn decl} {qPcmp : quotation_of Pcmp} {qP : quotation_of P} : ground_quotable (@on_global_decl cf Pcmp P Σ kn decl).
  Proof.
    cbv [on_global_decl]; try exact _.
    destruct decl; try exact _.
    repeat match goal with
           | [ H : quotation_of ?x |- _ ] => revert x H
           | [ x : _ |- _ ] => generalize (_ : quotation_of x); revert x
           end.
  #[export] Instance quote_on_global_decls_data {cf Pcmp P univs retro Σ kn d} {qPcmp : quotation_of Pcmp} {qP : quotation_of P} : ground_quotable (@on_global_decls_data cf Pcmp P univs retro Σ kn d).
  Proof.
    destruct 1; try exact _.
    repeat match goal with
           | [ H : quotation_of ?x |- _ ] => revert x H
           | [ x : _ |- _ ] => generalize (_ : quotation_of x); revert x
           end.

  Print on_global_decls.
  #[export] Instance quote_on_global_decls {cf Pcmp P univs retro decls} {qPcmp : quotation_of Pcmp} {qP : quotation_of P} : ground_quotable (@on_global_decls cf Pcmp P univs retro decls).
  Proof.
    induction 1; try exact _.
    repeat match goal with
           | [ H : quotation_of ?x |- _ ] => revert x H
           | [ x : _ |- _ ] => generalize (_ : quotation_of x); revert x
           end.

    pose (_ : quotation_of ).
    cbv [on_global_univs]; try exact _.
    apply @quote_and; try exact _.
    eapply @QuoteConstraintSet.quote_For_all; try exact _.
  Defined.
  Print on_global_env.
  #[export] Instance quote_on_global_env {cf Pcmp P g} : ground_quotable (@wf H Σ).
  cbv [wf].

  #[export] Instance quote_wf {H Σ} : ground_quotable (@wf H Σ).
  cbv [wf].
  Locate on_global_env.
    := _.
  #[export] Instance quote_typing_spine {H Σ Γ t1 s t2} : ground_quotable (@typing_spine H Σ Γ t1 s t2) := quote_typing_spine'.
End Typing.
