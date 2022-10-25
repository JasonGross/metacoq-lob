From MetaCoq.Template Require Import utils All.
From MetaCoq.PCUIC Require Import PCUICAst PCUICTyping Loader.
From MetaCoq.PCUIC.PCUICTemplateMonad Require Import Core.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope bs.
Import MCMonadNotation.

Class quotation_of {T} (t : T) := quoted_term_of : PCUICAst.term.
Class ground_quotable T := quote_ground : forall t : T, quotation_of t.
#[export] Existing Instance quote_ground.

Definition make_quotation_of {T} (t : T) : TemplateMonad (quotation_of t).
Proof.
  simple
    refine
    (qt <- tmQuote t;;
     let tmInferQuotation t
       := (t <- tmUnquote t;;
           v <- (let '(existT_typed_term _ t) := t in tmInferInstance None (quotation_of t));;
           match v with
           | my_Some v => tmReturn v
           | my_None => tmFail "No typeclass instance"
           end) in
     match qt return TemplateMonad PCUICAst.term with
     | tSort _
     | tConst _ _
     | tConstruct _ _ _
     | tPrim _
     | tInd _ _
       => tmReturn qt
     | tApp f x
       => qf <- tmInferQuotation f;;
          qx <- tmInferQuotation x;;
          tmReturn (tApp qf qx)
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
#[export] Instance quote_bool : ground_quotable bool := (ltac:(induction 1; exact _)).
#[export] Instance quote_byte : ground_quotable Byte.byte := (ltac:(induction 1; exact _)).
#[export] Instance quote_string : ground_quotable string := (ltac:(induction 1; exact _)).
#[export] Instance quote_list {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (list A) := (ltac:(induction 1; exact _)).
#[export] Instance quote_option {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (option A) := (ltac:(induction 1; exact _)).
#[export] Instance quote_sigT {A P} {qA : quotation_of A} {qP : quotation_of P} {quoteA : ground_quotable A} {quoteP : forall x, quotation_of x -> ground_quotable (P x)} : ground_quotable (@sigT A P) := (ltac:(induction 1; exact _)).
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
#[export] Instance quote_PrimInt63_int : ground_quotable PrimInt63.int := fun x => tPrim (_; primIntModel x).
#[export] Instance quote_PrimFloat_float : ground_quotable PrimFloat.float := fun x => tPrim (_; primFloatModel x).
Module Import BasicAst.
  #[export] Instance quote_context_decl {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (BasicAst.context_decl A) := (ltac:(induction 1; exact _)).
  #[export] Instance quote_typ_or_sort_ {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (BasicAst.typ_or_sort_ A) := (ltac:(induction 1; exact _)).
End BasicAst.
#[export] Instance quote_predicate {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (predicate A) := (ltac:(induction 1; exact _)).
#[export] Instance quote_branch {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (branch A) := (ltac:(induction 1; exact _)).
#[export] Instance quote_def {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (def A) := (ltac:(induction 1; exact _)).
#[export] Instance quote_mfixpoint {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (mfixpoint A) := _.
Module Import Primitive.
  #[export] Instance quote_prim_tag : ground_quotable Primitive.prim_tag := (ltac:(induction 1; exact _)).
End Primitive.
Module Import PCUICPrimitive.
  #[export] Instance quote_prim_model {A} {qA : quotation_of A} {quoteA : ground_quotable A} {t} : ground_quotable (PCUICPrimitive.prim_model A t) := (ltac:(induction 1; exact _)).
  #[export] Instance quote_context_decl {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (BasicAst.context_decl A) := (ltac:(induction 1; exact _)).
  #[export] Instance quote_prim_val {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (PCUICPrimitive.prim_val A) := @quote_sigT _ (PCUICPrimitive.prim_model A) _ _ _ _.
End PCUICPrimitive.
#[export] Instance quote_term : ground_quotable term.
Proof.
  hnf. fix quote_term 1; change (ground_quotable term) in quote_term; destruct 1.
  all: make_quotation_of_goal ().
Defined.
(*
Module Export PCUICEnvironment.
  #[export] Instance quote_context : ground_quotable PCUICAst.PCUICEnvironment.context := _.
End PCUICEnvironment.

Module Import PCUICTyping.
  #[export] Instance quote_All_local_env {typing} {qtyping : quotation_of typing} {quote_typing : forall Γ t T, ground_quotable (typing Γ t T)} {Γ} {qΓ : quotation_of Γ} : ground_quotable (@PCUICTyping.All_local_env typing Γ) := (ltac:(induction 1; exact _)).
  #[local] Hint Extern 1 (_ = _) => reflexivity : typeclass_instances.
  #[export] Instance quote_lift_judgment {check infer_sort}
   {Σ Γ t T}
   {quote_check : forall T', Typ T' = T -> ground_quotable (check Σ Γ t T')}
   {quote_infer_sort : T = Sort -> ground_quotable (infer_sort Σ Γ t)}
    : ground_quotable (@PCUICTyping.lift_judgment check infer_sort Σ Γ t T)
    := (ltac:(cbv [PCUICTyping.lift_judgment]; exact _)).
  #[export] Instance quote_infer_sort {sorting} {Σ Γ T} {qsorting : quotation_of (sorting Σ Γ T)} {quote_sorting : forall U, quotation_of U -> ground_quotable (sorting Σ Γ T U)} : ground_quotable (@PCUICTyping.infer_sort sorting Σ Γ T) := @quote_sigT _ (sorting Σ Γ T) _ _ _ _.
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
    : ground_quotable (@PCUICTyping.lift_typing typing Σ Γ t T)
    := ltac:(cbv [PCUICTyping.lift_typing]; exact _).
  #[export] Instance quote_typing {checker_flags Σ Γ x T} : ground_quotable (@PCUICTyping.typing checker_flags Σ Γ x T).
  Proof.
    hnf. fix quote_typing 1; change (ground_quotable (@PCUICTyping.typing checker_flags Σ Γ x T)) in quote_typing; destruct 1.
    Typeclasses eauto := debug.
    all: try make_quotation_of_goal ().
    pose (_ : quotation_of Σ).
    pose (_ : quotation_of n).
    pose (_ : quotation_of decl).
    pose (_ : quotation_of e).
    assert (quotation_of a).
    { eapply @quote_All_local_env; try exact _.

      eapply @quote_lift_typing.
    pose (_ : quotation_of a).
  Defined.
Inductive typing `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
*)
