From MetaCoq.Lob.Template.QuoteGround Require Export utils Environment EnvironmentTyping Universes BasicAst.
From MetaCoq.Template Require Import Ast Induction.

#[export] Instance quote_predicate {term} {qterm : quotation_of term} {quote_term : ground_quotable term} : ground_quotable (predicate term) := ltac:(destruct 1; exact _).
#[export] Instance quote_branch {term} {qterm : quotation_of term} {quote_term : ground_quotable term} : ground_quotable (branch term) := ltac:(destruct 1; exact _).
#[local] Hint Extern 1 => assumption : typeclass_instances.
#[export] Instance quote_term : ground_quotable term := ltac:(induction 1 using term_forall_list_rect; exact _).

Module QuoteTemplateTerm <: QuoteTerm TemplateTerm.
  #[export] Instance qterm : quotation_of TemplateTerm.term := _.
  #[export] Instance quote_term : ground_quotable TemplateTerm.term := _.

  #[export] Instance qtRel : quotation_of TemplateTerm.tRel := _.
  #[export] Instance qtSort : quotation_of TemplateTerm.tSort := _.
  #[export] Instance qtProd : quotation_of TemplateTerm.tProd := _.
  #[export] Instance qtLambda : quotation_of TemplateTerm.tLambda := _.
  #[export] Instance qtLetIn : quotation_of TemplateTerm.tLetIn := _.
  #[export] Instance qtInd : quotation_of TemplateTerm.tInd := _.
  #[export] Instance qtProj : quotation_of TemplateTerm.tProj := _.
  #[export] Instance qmkApps : quotation_of TemplateTerm.mkApps := _.

  #[export] Instance qlift : quotation_of TemplateTerm.lift := _.
  #[export] Instance qsubst : quotation_of TemplateTerm.subst := _.
  #[export] Instance qclosedn : quotation_of TemplateTerm.closedn := _.
  #[export] Instance qnoccur_between : quotation_of TemplateTerm.noccur_between := _.
  #[export] Instance qsubst_instance_constr : quotation_of TemplateTerm.subst_instance_constr := _.
  Module Instances.
    #[export] Existing Instances
     qterm
     quote_term

     qtRel
     qtSort
     qtProd
     qtLambda
     qtLetIn
     qtInd
     qtProj
     qmkApps

     qlift
     qsubst
     qclosedn
     qnoccur_between
     qsubst_instance_constr
    .
  End Instances.
End QuoteTemplateTerm.
Export QuoteTemplateTerm.Instances.

Module QuotationOfEnv <: QuotationOfEnvironment TemplateTerm Env.
  #[export] Instance qconstructor_body : inductive_quotation_of constructor_body := _.
  #[export] Instance qprojection_body : inductive_quotation_of projection_body := _.
  #[export] Instance qone_inductive_body : inductive_quotation_of one_inductive_body := _.
  #[export] Instance qmutual_inductive_body : inductive_quotation_of mutual_inductive_body := _.
  #[export] Instance qconstant_body : inductive_quotation_of constant_body := _.
  #[export] Instance qglobal_decl : inductive_quotation_of global_decl := _.
  #[export] Instance qglobal_env : inductive_quotation_of global_env := _.
  #[export] Instance qAll_decls : inductive_quotation_of All_decls := _.
  #[export] Instance qAll_decls_alpha : inductive_quotation_of All_decls_alpha := _.
  Module Instances.
    #[export] Existing Instances
     qconstructor_body
     qprojection_body
     qone_inductive_body
     qmutual_inductive_body
     qconstant_body
     qglobal_decl
     qglobal_env
     qAll_decls
     qAll_decls_alpha
    .
  End Instances.
End QuotationOfEnv.
Export QuotationOfEnv.Instances.

Module QuoteEnv := QuoteEnvironment TemplateTerm Env QuoteTemplateTerm QuotationOfEnv.
Export QuoteEnv.Instances.

Module QuoteTemplateLookup := QuoteLookup TemplateTerm Env TemplateLookup QuoteTemplateTerm QuotationOfEnv.
Export QuoteTemplateLookup.Instances.

#[export] Instance quote_parameter_entry : ground_quotable parameter_entry := ltac:(destruct 1; exact _).
#[export] Instance quote_definition_entry : ground_quotable definition_entry := ltac:(destruct 1; exact _).
#[export] Instance quote_constant_entry : ground_quotable constant_entry := ltac:(destruct 1; exact _).
#[export] Instance quote_one_inductive_entry : ground_quotable one_inductive_entry := ltac:(destruct 1; exact _).
#[export] Instance quote_mutual_inductive_entry : ground_quotable mutual_inductive_entry := ltac:(destruct 1; exact _).
