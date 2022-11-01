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

Module Type QuotationOfEnvironment (T : Term) (Import E : EnvironmentSig T).
  #[export] Declare Instance qconstructor_body : inductive_quotation_of constructor_body.
  #[export] Declare Instance qprojection_body : inductive_quotation_of projection_body.
  #[export] Declare Instance qone_inductive_body : inductive_quotation_of one_inductive_body.
  #[export] Declare Instance qmutual_inductive_body : inductive_quotation_of mutual_inductive_body.
  #[export] Declare Instance qconstant_body : inductive_quotation_of constant_body.
  #[export] Declare Instance qglobal_decl : inductive_quotation_of global_decl.
  #[export] Declare Instance qglobal_env : inductive_quotation_of global_env.
  #[export] Declare Instance qAll_decls : inductive_quotation_of All_decls.
  #[export] Declare Instance qAll_decls_alpha : inductive_quotation_of All_decls_alpha.
End QuotationOfEnvironment.

Module QuoteEnvironment (T : Term) (Import E : EnvironmentSig T) (Import QT : QuoteTerm T) (Import QoE : QuotationOfEnvironment T E).

  #[export] Instance quote_constructor_body : ground_quotable constructor_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_projection_body : ground_quotable projection_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_one_inductive_body : ground_quotable one_inductive_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_mutual_inductive_body : ground_quotable mutual_inductive_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_constant_body : ground_quotable constant_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_global_decl : ground_quotable global_decl := ltac:(destruct 1; exact _).

  #[export] Instance quote_global_env : ground_quotable global_env := ltac:(destruct 1; exact _).

  #[export] Instance qcst_type : quotation_of cst_type := ltac:(cbv -[quotation_of]; exact _).
  #[export] Instance qcst_body : quotation_of cst_body := ltac:(cbv -[quotation_of]; exact _).
  #[export] Instance qcst_universes : quotation_of cst_universes := ltac:(cbv -[quotation_of]; exact _).
  #[export] Instance quniverses : quotation_of universes := ltac:(cbv -[quotation_of]; exact _).
  #[export] Instance qdeclarations : quotation_of declarations := ltac:(cbv -[quotation_of]; exact _).
  #[export] Instance qglobal_declarations : quotation_of global_declarations := ltac:(cbv [global_declarations]; exact _).

  #[export] Instance quote_extends {Σ Σ'} : ground_quotable (@extends Σ Σ') := ltac:(cbv [extends]; exact _).
  #[export] Instance quote_extends_decls {Σ Σ'} : ground_quotable (@extends_decls Σ Σ') := ltac:(cbv [extends_decls]; exact _).
  #[export] Instance quote_primitive_invariants {cdecl} : ground_quotable (primitive_invariants cdecl) := _.

  #[export] Instance quote_All_decls {P t t'} {qP : quotation_of P} {quoteP : forall t t', ground_quotable (P t t')} : ground_quotable (All_decls P t t') := ltac:(induction 1; exact _).
  #[export] Instance quote_All_decls_alpha {P t t'} {qP : quotation_of P} {quoteP : forall t t', ground_quotable (P t t')} : ground_quotable (All_decls_alpha P t t') := ltac:(induction 1; exact _).

  Module Instances.
    #[export] Existing Instances
     quote_constructor_body
     quote_projection_body
     quote_one_inductive_body
     quote_mutual_inductive_body
     quote_constant_body
     quote_global_decl
     quote_global_env
     qcst_type
     qcst_body
     qcst_universes
     quniverses
     qdeclarations
     qglobal_declarations
     quote_extends
     quote_extends_decls
     quote_primitive_invariants
     quote_All_decls
     quote_All_decls_alpha
    .
  End Instances.
End QuoteEnvironment.
