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
  #[export] Declare Instance qterm : quotation_of T.term.
  #[export] Declare Instance quote_term : ground_quotable T.term.

  #[export] Declare Instance qtRel : quotation_of T.tRel.
  #[export] Declare Instance qtSort : quotation_of T.tSort.
  #[export] Declare Instance qtProd : quotation_of T.tProd.
  #[export] Declare Instance qtLambda : quotation_of T.tLambda.
  #[export] Declare Instance qtLetIn : quotation_of T.tLetIn.
  #[export] Declare Instance qtInd : quotation_of T.tInd.
  #[export] Declare Instance qtProj : quotation_of T.tProj.
  #[export] Declare Instance qmkApps : quotation_of T.mkApps.

  #[export] Declare Instance qlift : quotation_of T.lift.
  #[export] Declare Instance qsubst : quotation_of T.subst.
  #[export] Declare Instance qclosedn : quotation_of T.closedn.
  #[export] Declare Instance qnoccur_between : quotation_of T.noccur_between.
  #[export] Declare Instance qsubst_instance_constr : quotation_of T.subst_instance_constr.
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
  #[export] Instance qglobal_env_ext : quotation_of global_env_ext := ltac:(cbv -[quotation_of]; exact _).
  #[export] Instance qtyp_or_sort : quotation_of typ_or_sort := ltac:(cbv -[quotation_of]; exact _).

  #[export] Instance quote_extends {Σ Σ'} : ground_quotable (@extends Σ Σ') := ltac:(cbv [extends]; exact _).
  #[export] Instance quote_extends_decls {Σ Σ'} : ground_quotable (@extends_decls Σ Σ') := ltac:(cbv [extends_decls]; exact _).
  #[export] Instance quote_primitive_invariants {cdecl} : ground_quotable (primitive_invariants cdecl) := _.

  #[export] Instance quote_All_decls {P t t'} {qP : quotation_of P} {quoteP : forall t t', ground_quotable (P t t')} : ground_quotable (All_decls P t t') := ltac:(induction 1; exact _).
  #[export] Instance quote_All_decls_alpha {P t t'} {qP : quotation_of P} {quoteP : forall t t', ground_quotable (P t t')} : ground_quotable (All_decls_alpha P t t') := ltac:(induction 1; exact _).
  #[export] Instance qcontext : quotation_of context := ltac:(cbv [context]; exact _).
  #[export] Instance qsubst_context : quotation_of subst_context := ltac:(cbv [subst_context]; exact _).
  #[export] Instance qsmash_context : quotation_of smash_context := ltac:(cbv [smash_context]; exact _).

  #[export] Instance qind_finite : quotation_of ind_finite := ltac:(cbv [ind_finite]; exact _).
  #[export] Instance qind_npars : quotation_of ind_npars := ltac:(cbv [ind_npars]; exact _).
  #[export] Instance qind_params : quotation_of ind_params := ltac:(cbv [ind_params]; exact _).
  #[export] Instance qind_bodies : quotation_of ind_bodies := ltac:(cbv [ind_bodies]; exact _).
  #[export] Instance qind_universes : quotation_of ind_universes := ltac:(cbv [ind_universes]; exact _).
  #[export] Instance qind_variance : quotation_of ind_variance := ltac:(cbv [ind_variance]; exact _).

  #[export] Instance qcontext_assumptions : quotation_of context_assumptions := ltac:(cbv [context_assumptions]; exact _).
  #[export] Instance qextended_subst : quotation_of extended_subst := ltac:(cbv [extended_subst]; exact _).
  #[export] Instance qlift_context : quotation_of lift_context := ltac:(cbv [lift_context]; exact _).
  #[export] Instance qexpand_lets_k_ctx : quotation_of expand_lets_k_ctx := ltac:(cbv [expand_lets_k_ctx]; exact _).
  #[export] Instance qexpand_lets_ctx : quotation_of expand_lets_ctx := ltac:(cbv [expand_lets_ctx]; exact _).

  #[export] Instance qcstr_name : quotation_of cstr_name := ltac:(cbv [cstr_name]; exact _).
  #[export] Instance qcstr_args : quotation_of cstr_args := ltac:(cbv [cstr_args]; exact _).
  #[export] Instance qcstr_indices : quotation_of cstr_indices := ltac:(cbv [cstr_indices]; exact _).
  #[export] Instance qcstr_type : quotation_of cstr_type := ltac:(cbv [cstr_type]; exact _).
  #[export] Instance qcstr_arity : quotation_of cstr_arity := ltac:(cbv [cstr_arity]; exact _).

  #[export] Instance qexpand_lets_k : quotation_of expand_lets_k := ltac:(cbv [expand_lets_k]; exact _).
  #[export] Instance qexpand_lets : quotation_of expand_lets := ltac:(cbv [expand_lets]; exact _).

  #[export] Instance qfst_ctx : quotation_of fst_ctx := ltac:(cbv [fst_ctx]; exact _).

  #[export] Instance qlookup_global : quotation_of lookup_global := ltac:(cbv [lookup_global]; exact _).
  #[export] Instance qlookup_env : quotation_of lookup_env := ltac:(cbv [lookup_env]; exact _).

  #[export] Instance qind_name : quotation_of ind_name := ltac:(cbv [ind_name]; exact _).
  #[export] Instance qind_indices : quotation_of ind_indices := ltac:(cbv [ind_indices]; exact _).
  #[export] Instance qind_sort : quotation_of ind_sort := ltac:(cbv [ind_sort]; exact _).
  #[export] Instance qind_type : quotation_of ind_type := ltac:(cbv [ind_type]; exact _).
  #[export] Instance qind_kelim : quotation_of ind_kelim := ltac:(cbv [ind_kelim]; exact _).
  #[export] Instance qind_ctors : quotation_of ind_ctors := ltac:(cbv [ind_ctors]; exact _).
  #[export] Instance qind_projs : quotation_of ind_projs := ltac:(cbv [ind_projs]; exact _).
  #[export] Instance qind_relevance : quotation_of ind_relevance := ltac:(cbv [ind_relevance]; exact _).

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
     qglobal_env_ext
     qtyp_or_sort
     qcontext
     qsubst_context
     qsmash_context
     qind_params
     qcontext_assumptions
     qextended_subst
     qlift_context
     qexpand_lets_k_ctx
     qexpand_lets_ctx
     qcstr_name
     qcstr_args
     qcstr_indices
     qcstr_type
     qcstr_arity
     qexpand_lets_k
     qexpand_lets
     qind_finite
     qind_npars
     qind_params
     qind_bodies
     qind_universes
     qind_variance
     qfst_ctx
     qlookup_global
     qlookup_env
     qind_name
     qind_indices
     qind_sort
     qind_type
     qind_kelim
     qind_ctors
     qind_projs
     qind_relevance
     quote_extends
     quote_extends_decls
     quote_primitive_invariants
     quote_All_decls
     quote_All_decls_alpha
    .
  End Instances.
End QuoteEnvironment.
