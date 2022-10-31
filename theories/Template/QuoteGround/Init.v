From MetaCoq.Template Require Import MonadBasicAst MonadAst All utils.
Require Import Coq.Lists.List.
Import ListNotations.

Local Set Primitive Projections.
Local Open Scope bs.
Import MCMonadNotation.

Class quotation_of {T} (t : T) := quoted_term_of : Ast.term.
Class ground_quotable T := quote_ground : forall t : T, quotation_of t.
Class inductive_quotation_of {T} (t : T)
  := { qinductive : inductive
     ; qinst : Instance.t
     ; qquotation : quotation_of t := tInd qinductive qinst }.
Class debug_opt := debug : bool.
Class cls_is_true (b : bool) := is_truev : is_true b.
Definition default_inductive_quotation_of {T} {t : T} (qt : quotation_of t) (pf : cls_is_true match qt with tInd _ _ => true | _ => false end)
  : inductive_quotation_of t
  := match qt return cls_is_true match qt with tInd _ _ => true | _ => false end -> _ with
     | tInd ind u => fun _ => @Build_inductive_quotation_of T t ind u
     | _ => fun pf : false = true => match diff_false_true pf with end
     end pf.

(* returns true if a modpath is suitable for quotation, i.e., does not mention functor-bound arguments *)
Fixpoint modpath_is_absolute (mp : modpath) : bool
  := match mp with
     | MPfile _ => true
     | MPbound _ _ _ => false
     | MPdot mp _ => modpath_is_absolute mp
     end.
Definition kername_is_absolute (kn : kername) : bool
  := modpath_is_absolute (fst kn).

(* returns false iff a term is suitable for quotation at the top-level, i.e., returns true iff it mentions functor-bound arguments or is a local variable or evar *)
Definition head_term_is_bound (t : term) : bool
  := match t with
     | tConst kn _
     | tInd {| inductive_mind := kn |} _
     | tConstruct {| inductive_mind := kn |} _ _
     | tProj {| proj_ind := {| inductive_mind := kn |} |} _
     | tCase {| ci_ind := {| inductive_mind := kn |} |} _ _ _
       => negb (kername_is_absolute kn)
     | tVar _
     | tEvar _ _
       => true
     | _ => false
     end.

Definition replace_inductive_kn (t : inductive) (i : term) : option inductive
  := match i with
     | tInd ind _
       => Some {| inductive_mind := ind.(inductive_mind) ; inductive_ind := t.(inductive_ind) |}
     | _ => None
     end.

Definition replace_head_ind (t : term) (i : term) : option term
  := match t with
     | tInd ind u
       => option_map (fun ind => tInd ind u) (replace_inductive_kn ind i)
     | tConstruct ind idx u
       => option_map (fun ind => tConstruct ind idx u) (replace_inductive_kn ind i)
     | tProj (mkProjection ind npars arg) t
       => option_map (fun ind => tProj (mkProjection ind npars arg) t) (replace_inductive_kn ind i)
     | tCase (mk_case_info ind npar rel) ti discr branches
       => option_map (fun ind => tCase (mk_case_info ind npar rel) ti discr branches ) (replace_inductive_kn ind i)
     | _ => None
     end.

Fixpoint head (t : term) : term
  := match t with
     | tCast t _ _
     | tApp t _
       => head t
     | _ => t
     end.

Definition infer_replace_head_ind {debug : debug_opt} (qt : term) : TemplateMonad (option term).
Proof.
  simple
    refine (let try_replace_head_ind qt v :=
              (* make sure it's not just a context variable *)
              (qv <- tmQuote v;;
               match qv with
               | tVar _ => ((if debug then tmPrint ("context variable:", v, "for", qt) else tmReturn tt);; tmReturn None)
               | _ => tmReturn (replace_head_ind qt v)
               end) in
            match qt with
            | tConstruct ind _ u
            | tCase {| ci_ind := ind |} {| puinst := u |} _ _
              => (ind <- tmUnquote (tInd ind u);;
                  let '(existT_typed_term _ ind) := ind in
                  v <- (tmInferInstance None (quotation_of ind));;
                  match v with
                  | my_Some v => try_replace_head_ind qt v
                  | my_None => (if debug then tmPrint (quotation_of ind) else tmReturn tt);; tmReturn None
                  end)
            | tProj proj t
              => (t <- tmUnquote t;;
                  let '(existT_typed_term ty _) := t in
                  ty <- tmEval hnf ty;;
                  ty <- tmQuote ty;;
                  let ind := head ty in
                  ind <- tmUnquote ind;;
                  let '(existT_typed_term _ ind) := ind in
                  v <- (tmInferInstance None (quotation_of ind));;
                  match v with
                  | my_Some v => try_replace_head_ind qt v
                  | my_None => (if debug then tmPrint (qt, quotation_of ind) else tmReturn tt);; tmReturn None
                  end)
            | _ => tmReturn None
            end);
    exact _.
Defined.

Definition try_infer_replace_head_ind {debug : debug_opt} (qt : term) : TemplateMonad term
  := if head_term_is_bound qt
     then (qt' <- infer_replace_head_ind qt;;
           match qt' with
           | Some qt => tmReturn qt
           | None => tmReturn qt
           end)
     else tmReturn qt.
Export bytestring.
Fixpoint replace_quotation_of' {debug : debug_opt} (do_top_inference : bool) (qt : term) : TemplateMonad term.
Proof.
  specialize (replace_quotation_of' debug).
  simple
    refine
    (let replace_quotation_of' := replace_quotation_of' true in
     tmPrint (do_top_inference, qt);;
     let tmTryInferQuotation t
       := (t <- tmUnquote t;;
           let '(existT_typed_term _ t) := t in
           v <- tmInferInstance None (quotation_of t);;
           match v return TemplateMonad (option_instance Ast.term) with
           | my_Some v => tmReturn (@my_Some _ v)
           | my_None => (if debug then tmPrint (quotation_of t) else tmReturn tt);; tmReturn (@my_None _)
           end) in
     let tmInferQuotation t
       := (v <- tmTryInferQuotation t;;
           match v return TemplateMonad Ast.term with
           | my_Some v => tmReturn v
           | my_None => tmFail "No typeclass instance"
           end) in
     let replaced
       := match qt return TemplateMonad Ast.term with
          | tRel _
          | tSort _
          | tConstruct _ _ _
          | tInt _
          | tFloat _
          | tConst _ _
          | tInd _ _
            => ret qt
          | tVar _
            => if do_top_inference then tmInferQuotation qt else tmFail "Avoiding loops"
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
          end in
     if head_term_is_bound qt
     then
       v <- (if do_top_inference then tmTryInferQuotation qt else tmReturn (@my_None _));;
       match v with
       | my_Some v => tmReturn v
       | my_None
         => qt' <- replaced;;
            qt' <- infer_replace_head_ind qt';;
            match qt' with
            | Some v => tmReturn v
            | None => tmFail "No typeclass instance nor replacement"
            end
       end
     else
       replaced);
    try exact _.
Defined.

Definition replace_quotation_of {debug : debug_opt} {T} (t : T) : TemplateMonad term
  := qt <- tmQuote t;;
     replace_quotation_of' false qt.

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
  #[export] Hint Mode cls_is_true + : typeclass_instances.
  #[export] Existing Instances qquotation | 10.
  (* Hack around COQBUG(https://github.com/coq/coq/issues/16760) *)
  #[export] Hint Extern 10 (@inductive_quotation_of ?T ?t) => simple notypeclasses refine (@default_inductive_quotation_of T t _ _) : typeclass_instances.
  #[export] Hint Extern 10 (cls_is_true ?b)
  => tryif is_evar b then refine (eq_refl true) else tryif has_evar b then fail else vm_compute; reflexivity
       : typeclass_instances.
  #[export] Hint Cut [
      ( _ * )
        qquotation
        ( _ * )
        qquotation
    ] : typeclass_instances.
End Instances.

Module StrongerInstances.
  #[export]
   Hint Extern 1 (quotation_of match ?t with _ => _ end) => destruct t : typeclass_instances.
  #[export]
   Hint Extern 1 (ground_quotable match ?t with _ => _ end) => destruct t : typeclass_instances.
End StrongerInstances.
