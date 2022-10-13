From MetaCoq.Template Require Import utils All.
Require Import List.
Import ListNotations.

Open Scope bs.
Import MCMonadNotation.

Class quotation_of {T} (t : T) := quoted_term_of : Ast.term.
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

#[export]
 Hint Extern 1 (quotation_of ?t) => run_template_program (make_quotation_of t) (fun v => exact v) : typeclass_instances.

#[export] Typeclasses Opaque quotation_of.

#[export] Instance quote_nat : ground_quotable nat := (ltac:(induction 1; exact _)).
#[export] Instance quote_byte : ground_quotable Byte.byte := (ltac:(induction 1; exact _)).
#[export] Instance quote_string : ground_quotable string := (ltac:(induction 1; exact _)).
#[export] Instance quote_Level_t : ground_quotable Level.t := (ltac:(induction 1; exact _)).
#[export] Instance quote_LevelExprSet_Raw_elt : ground_quotable LevelExprSet.Raw.elt := (ltac:(induction 1; exact _)).
#[export] Instance quote_LevelExprSet_Raw_t : ground_quotable LevelExprSet.Raw.t := (ltac:(induction 1; exact _)).
Print Universe.lType.
Print LevelAlgExpr.t.
Print nonEmptyLevelExprSet.
Print LevelExprSet.Raw.t.
Print LevelExprSet.t_.
Print LevelExprSet.Raw.isok.
#[export] Instance quote_LevelExprSet_Raw_Ok : ground_quotable LevelExprSet.Raw.Ok := (ltac:(induction 1; exact _)).
#[export] Instance quote_LevelExprSet_t : ground_quotable LevelExprSet.t := (ltac:(induction 1; exact _)).
#[export] Instance quote_LevelAlgExpr_t : ground_quotable LevelAlgExpr.t := (ltac:(induction 1; exact _)).
#[export] Instance quote_Universe : ground_quotable Universe.t := (ltac:(induction 1; exact _)).
Print term.
  := match n with
     | 0 => <% 0 %>
     | S n => Ast.tApp <% S %> [ quote_nat n ]
     end.

Print ident.
Print term.



Check _ : quotation_of O.
  Print option_instance.
  refine match qt with
         | tRel n => _
         | tVar id => _
         | tEvar ev args => _
         | tSort s => _
         | tCast t kind v => _
         | tProd na ty body => _
         | tLambda na ty body => _
         | tLetIn na def def_ty body => _
         | tApp f args => _
         | tConst c u => _
         | tInd ind u => _
         | tConstruct ind idx u => _
         | tCase ci type_info discr branches => _
         | tProj proj t => _
         | tFix mfix idx => _
         | tCoFix mfix idx => _
         | tInt i => _
         | tFloat f => _
         end

#[export] Hint Extern 0 (quotation_of ?x) => is_constructor x; exact <% x %> : typeclass_instances.


Check _ : quotation_of (S 0).

Check (t <- tmQuote true ;; tmPrint t).
MetaCoq Run (t <- tmQuote true ;; tmPrint t).

Ltac make_quoter_quote_term t :=


Definition quote_bool (b : bool) : Ast.term.

  Ltac make_quoter x :=
    let xv := fresh "v" in
    pose x as xv;
    induction x;
    (*let v := (eval cbv [xv] in xv); clear xv*) idtac.
  make_quoter b.
