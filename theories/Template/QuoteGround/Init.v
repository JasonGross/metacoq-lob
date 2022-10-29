From MetaCoq.Template Require Import MonadBasicAst MonadAst All utils.
Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope bs.
Import MCMonadNotation.

Class quotation_of {T} (t : T) := quoted_term_of : Ast.term.
Class ground_quotable T := quote_ground : forall t : T, quotation_of t.
Class debug_opt := debug : bool.

(* returns true if a modpath is suitable for quotation, i.e., does not mention functor-bound arguments *)
Fixpoint modpath_is_absolute (mp : modpath) : bool
  := match mp with
     | MPfile _ => true
     | MPbound _ _ _ => false
     | MPdot mp _ => modpath_is_absolute mp
     end.
(* returns false iff a term is suitable for quotation at the top-level, i.e., returns true iff it mentions functor-bound arguments or is a local variable *)
Definition head_term_is_bound (t : term) : bool
  := match t with
     | tConst (kn, _) _ => negb (modpath_is_absolute kn)
     | tVar _ => true
     | _ => false
     end.

Fixpoint replace_quotation_of' {debug : debug_opt} (qt : term) : TemplateMonad term.
Proof.
  specialize (replace_quotation_of' debug).
  simple
    refine
    (let tmInferQuotation t
       := (t <- tmUnquote t;;
           let '(existT_typed_term _ t) := t in
           v <- (tmInferInstance None (quotation_of t));;
           match v with
           | my_Some v => tmReturn v
           | my_None => (if debug then tmPrint (quotation_of t) else tmReturn tt);; tmFail "No typeclass instance"
           end) in
     if head_term_is_bound qt
     then tmInferQuotation qt
     else
       match qt return TemplateMonad Ast.term with
       | tRel _
       | tSort _
       | tConstruct _ _ _
       | tInt _
       | tFloat _
       | tConst _ _
       | tInd _ _
         => ret qt
       | tVar _
         => tmInferQuotation qt
       | tEvar ev args => args <- monad_map replace_quotation_of' args;; ret (tEvar ev args)
       | tLambda na T M => T <- replace_quotation_of' T;; M <- replace_quotation_of' M;; ret (tLambda na T M)
       | tApp u v => u <- replace_quotation_of' u;; v <- monad_map replace_quotation_of' v;; ret (mkApps u v)
       | tProd na A B => A <- replace_quotation_of' A;; B <- replace_quotation_of' B;; ret (tProd na A B)
       | tCast c kind ty => c <- replace_quotation_of' c;; ty <- replace_quotation_of' ty;; ret (tCast c kind ty)
       | tLetIn na b ty b' => b <- replace_quotation_of' b;; ty <- replace_quotation_of' ty;; b' <- replace_quotation_of' b';; ret (tLetIn na b ty b')
       | tProj p c => replace_quotation_of' c;; ret (tProj p c)
       | tFix mfix idx =>
           mfix' <- monad_map (monad_map_def (TM:=TypeInstance) replace_quotation_of' replace_quotation_of') mfix;;
           ret (tFix mfix' idx)
       | tCoFix mfix idx =>
           mfix' <- monad_map (monad_map_def (TM:=TypeInstance) replace_quotation_of' replace_quotation_of') mfix;;
           ret (tCoFix mfix' idx)
       | tCase ind p c brs =>
           p' <- monad_map_predicate (TM:=TypeInstance) ret replace_quotation_of' replace_quotation_of' p;;
           brs' <- monad_map_branches (TM:=TypeInstance) replace_quotation_of' brs;;
           c <- replace_quotation_of' c;;
           ret (tCase ind p' c brs')
       end); exact _.
Defined.

Definition replace_quotation_of {debug : debug_opt} {T} (t : T) : TemplateMonad term
  := qt <- tmQuote t;;
     if head_term_is_bound qt
     then tmFail "Avoiding loops"
     else replace_quotation_of' qt.

(** for fancier goals when we have [ground_quotable] for some subterms but not for subterms of those subterms *)
Definition make_quotation_of {debug : debug_opt} {T} (t : T) : TemplateMonad (quotation_of t).
Proof.
  simple
    refine
    (qt <- tmQuote t;;
     let tmInferQuotation t
       := (t <- tmUnquote t;;
           let '(existT_typed_term _ t) := t in
           v <- tmInferInstance None (quotation_of t);;
           match v with
           | my_Some v => tmReturn v
           | my_None => (if debug then tmPrint (quotation_of t) else tmReturn tt);; tmFail "No typeclass instance"
           end) in
     if head_term_is_bound qt
     then tmFail "bound argument is not ground"
     else
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

Ltac replace_quotation_of_goal _ :=
  let t := match goal with |- quotation_of ?t => t end in
  run_template_program (replace_quotation_of t) (fun v => exact v).

Ltac make_quotation_of_goal _ :=
  let t := match goal with |- quotation_of ?t => t end in
  run_template_program (make_quotation_of t) (fun v => exact v).

Ltac adjust_quotation_of_by_econstructor_then tac1 tac2 :=
  let f := match goal with |- ?f _ => f end in
  unshelve (let g := open_constr:(f _) in
            change g);
  [ unshelve econstructor
  | ];
  [ ..
  | repeat match goal with |- context[?ev] => is_evar ev; generalize ev; intro end ];
  [ tac1 () ..
  | tac2 () ].

Ltac adjust_ground_quotable_by_econstructor_inversion _ :=
  let pf := fresh "pf" in
  intro pf;
  adjust_quotation_of_by_econstructor_then ltac:(fun _ => inversion pf; try assumption) ltac:(fun _ => try exact _).

Module Export Instances.
  #[export] Instance default_debug : debug_opt | 1000 := false.
  #[export] Existing Instance quote_ground.
  #[export] Typeclasses Opaque quotation_of.
  #[export]
   Hint Extern 1 (quotation_of match ?t with _ => _ end) => is_var t; destruct t : typeclass_instances.
  #[export]
   Hint Extern 1 (ground_quotable match ?t with _ => _ end) => is_var t; destruct t : typeclass_instances.
  #[export]
   Hint Extern 1 (quotation_of _) => replace_quotation_of_goal () : typeclass_instances.
  #[export]
   Hint Extern 2 (quotation_of ?t) => make_quotation_of_goal () : typeclass_instances.
End Instances.

Module StrongerInstances.
  #[export]
   Hint Extern 1 (quotation_of match ?t with _ => _ end) => destruct t : typeclass_instances.
  #[export]
   Hint Extern 1 (ground_quotable match ?t with _ => _ end) => destruct t : typeclass_instances.
End StrongerInstances.
