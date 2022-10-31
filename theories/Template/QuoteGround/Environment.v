From MetaCoq.Lob.Template.QuoteGround Require Export Coq.Init Coq.ssr utils BasicAst Primitive Universes.
From MetaCoq.Template Require Import Environment.

Module Retroknowledge.
  #[export] Instance quote_t : ground_quotable Retroknowledge.t := ltac:(destruct 1; exact _).
  #[export] Instance quote_extends {x y} : ground_quotable (@Retroknowledge.extends x y) := ltac:(cbv [Retroknowledge.extends]; exact _).

  Module Instances.
    #[export] Existing Instances
     quote_t
     quote_extends
    .
  End Instances.
End Retroknowledge.
Export Retroknowledge.Instances.

Module Type QuoteTerm (T : Term).
  Parameter qterm : quotation_of T.term.
  Parameter qtSort : quotation_of T.tSort.
  Parameter quote_term : ground_quotable T.term.

  #[export] Existing Instances
   qterm
   qtSort
   quote_term
  .
End QuoteTerm.

Module QuoteEnvironment (T : Term) (Import E : EnvironmentSig T) (Import QT : QuoteTerm T).
  #[export] Instance quote_constructor_body : ground_quotable constructor_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_projection_body : ground_quotable projection_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_one_inductive_body : ground_quotable one_inductive_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_mutual_inductive_body : ground_quotable mutual_inductive_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_constant_body : ground_quotable constant_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_global_decl : ground_quotable global_decl := ltac:(destruct 1; exact _).
  #[export] Instance quote_global_env : ground_quotable global_env := ltac:(destruct 1; exact _).

  Section with_quote.
    Context {qglobal_decl : quotation_of global_decl}
            {qdeclarations : quotation_of declarations}
            {qcst_type : quotation_of cst_type} {qcst_body : quotation_of cst_body} {qcst_universes : quotation_of cst_universes}.

    #[export] Instance qglobal_declarations : quotation_of global_declarations := ltac:(cbv [global_declarations]; exact _).
    #[export] Instance quote_extends {Σ Σ'} : ground_quotable (@extends Σ Σ') := ltac:(cbv [extends]; exact _).
    #[export] Instance quote_extends_decls {Σ Σ'} : ground_quotable (@extends_decls Σ Σ') := ltac:(cbv [extends_decls]; exact _).
    #[export] Instance quote_primitive_invariants {cdecl} : ground_quotable (primitive_invariants cdecl) := _.
  End with_quote.

  #[export] Instance quote_All_decls {P t t'} {qP : quotation_of P} {quoteP : forall t t', ground_quotable (P t t')} : ground_quotable (All_decls P t t') := ltac:(induction 1; exact _).
  #[export] Instance quote_All_decls_alpha {P t t'} {qP : quotation_of P} {quoteP : forall t t', ground_quotable (P t t')} : ground_quotable (All_decls_alpha P t t') := ltac:(induction 1; exact _).
End QuoteEnvironment.
