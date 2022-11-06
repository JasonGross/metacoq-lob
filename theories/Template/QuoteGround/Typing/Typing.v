From MetaCoq.Lob.Template Require Import QuoteGround.Typing.
From MetaCoq.Lob.Template.QuoteGround Require Export Ast.Typing.
(*
From MetaCoq.Lob.Template.QuoteGround Require Export config utils Ast AstUtils Environment Primitive
     LiftSubst UnivSubst EnvironmentTyping Reflect ReflectAst TermEquality WfAst.
*)
From MetaCoq.Template Require Import Ast Typing.

(*
#[export] Instance quote_isSort {T} : ground_quotable (isSort T) := ltac:(cbv [isSort]; exact _).
#[export] Instance quote_isArity {T} : ground_quotable (isArity T) := ltac:(induction T; exact _).
#[export] Instance quote_instantiate_params_subst_spec {params pars s pty s' pty'} : ground_quotable (@instantiate_params_subst_spec params pars s pty s' pty').
Proof.
  revert params pars s pty s' pty'; induction params as [|a params]; intros; [ | destruct a as [? [] ?], pty ]; destruct pars.
  all: try solve [ intro H; exfalso; inversion H ].
  { intro pf.
    assert (s' = s) by now inversion pf.
    assert (pty' = pty) by now inversion pf.
    subst.
    revert pf.
    adjust_ground_quotable_by_econstructor_inversion (). }
  adjust_ground_quotable_by_econstructor_inversion ().
  adjust_ground_quotable_by_econstructor_inversion ().
  adjust_ground_quotable_by_econstructor_inversion ().
Defined.
#[export] Instance quote_red1 {Σ Γ x y} : ground_quotable (@red1 Σ Γ x y).
Proof.
  revert Γ x y; cbv [ground_quotable].
  fix quote_red1 4; change (forall Γ x y, ground_quotable (@red1 Σ Γ x y)) in quote_red1.
  intros Γ x y.
  destruct 1; exact _.
Defined.
#[export] Instance quote_red {Σ Γ x y} : ground_quotable (@red Σ Γ x y) := ltac:(induction 1; exact _).
#[export] Instance quote_eq_term_nocast {cf Σ ϕ t u} : ground_quotable (@eq_term_nocast cf Σ ϕ t u) := _.
#[export] Instance quote_leq_term_nocast {cf Σ ϕ t u} : ground_quotable (@leq_term_nocast cf Σ ϕ t u) := _.
#[export] Instance quote_cumul_gen {cf Σ Γ pb t u} : ground_quotable (@cumul_gen cf Σ Γ pb t u) := ltac:(induction 1; exact _).
#[export] Instance quote_eq_opt_term {cf Σ ϕ t u} : ground_quotable (@eq_opt_term cf Σ ϕ t u) := _.
#[export] Instance quote_eq_decl {cf Σ ϕ d d'} : ground_quotable (@eq_decl cf Σ ϕ d d') := _.
#[export] Instance quote_eq_context {cf Σ ϕ d d'} : ground_quotable (@eq_context cf Σ ϕ d d') := _.

Module QuotationOfTemplateEnvTyping <: QuotationOfEnvTyping TemplateTerm Env TemplateTermUtils TemplateEnvTyping.
  #[export] Instance qAll_local_env : inductive_quotation_of All_local_env := _.
  #[export] Instance qAll_local_env_over_gen : inductive_quotation_of All_local_env_over_gen := _.
  #[export] Instance qctx_inst : inductive_quotation_of ctx_inst := _.

  Module Instances.
    #[export] Existing Instances
     qAll_local_env
     qAll_local_env_over_gen
     qctx_inst
    .
  End Instances.
End QuotationOfTemplateEnvTyping.
Export QuotationOfTemplateEnvTyping.Instances.

Module QuoteTemplateEnvTyping := QuoteEnvTyping TemplateTerm Env TemplateTermUtils TemplateEnvTyping QuoteTemplateTerm QuotationOfEnv QuotationOfTemplateEnvTyping.
Export QuoteTemplateEnvTyping.Instances.

Module QuotationOfTemplateConversion <: QuotationOfConversion TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversion.
  #[export] Instance qAll_decls_alpha_pb : inductive_quotation_of All_decls_alpha_pb := _.

  Module Instances.
    #[export] Existing Instances
     qAll_decls_alpha_pb
    .
  End Instances.
End QuotationOfTemplateConversion.
Export QuotationOfTemplateConversion.Instances.

Module QuoteTemplateConversion := QuoteConversion TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversion QuoteTemplateTerm QuotationOfEnv QuotationOfTemplateConversion.
Export QuoteTemplateConversion.Instances.

Module QuotationOfTemplateGlobalMaps <: QuotationOfGlobalMaps TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversion TemplateLookup TemplateGlobalMaps.
  #[export] Instance qpositive_cstr_arg : inductive_quotation_of positive_cstr_arg := _.
  #[export] Instance qpositive_cstr : inductive_quotation_of positive_cstr := _.
  #[export] Instance qon_constructor : inductive_quotation_of (@on_constructor) := _.
  #[export] Instance qon_proj : inductive_quotation_of on_proj := _.
  #[export] Instance qon_projections : inductive_quotation_of on_projections := _.
  #[export] Instance qon_ind_body : inductive_quotation_of (@on_ind_body) := _.
  #[export] Instance qon_inductive : inductive_quotation_of (@on_inductive) := _.
  #[export] Instance qon_global_decls_data : inductive_quotation_of (@on_global_decls_data) := _.
  #[export] Instance qon_global_decls : inductive_quotation_of (@on_global_decls) := _.

  Module Instances.
    #[export] Existing Instances
     qpositive_cstr_arg
     qpositive_cstr
     qon_constructor
     qon_proj
     qon_projections
     qon_ind_body
     qon_inductive
     qon_global_decls_data
     qon_global_decls
    .
  End Instances.
End QuotationOfTemplateGlobalMaps.
Export QuotationOfTemplateGlobalMaps.Instances.

Module QuoteTemplateGlobalMaps := QuoteGlobalMaps TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversion TemplateLookup TemplateGlobalMaps QuoteTemplateTerm QuotationOfEnv QuotationOfTemplateEnvTyping QuotationOfTemplateConversion QuotationOfTemplateGlobalMaps.
Export QuoteTemplateGlobalMaps.Instances.

Module QuoteTemplateConversionPar <: QuoteConversionPar TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversionPar.
  #[export] Instance qcumul_gen : quotation_of (@TemplateConversionPar.cumul_gen) := _.
  #[export] Instance quote_cumul_gen {cf Σ Γ pb t t'} : ground_quotable (@TemplateConversionPar.cumul_gen cf Σ Γ pb t t') := _.
  Module Instances.
    #[export] Existing Instances
     qcumul_gen
     quote_cumul_gen
    .
  End Instances.
End QuoteTemplateConversionPar.
Export QuoteTemplateConversionPar.Instances.
 *)
(*
Section quote_typing.
  Context {cf : config.checker_flags} {Σ : global_env_ext}.

  #[local] Hint Extern 1 => progress cbv zeta : typeclass_instances.

  Fixpoint quote_typing' {Γ t T} (pf : @typing cf Σ Γ t T) : quotation_of pf
  with quote_typing_spine' {Γ t s T} (pf : @typing_spine cf Σ Γ t s T) : quotation_of pf.
  Proof.
    all: change (forall Γ t T, ground_quotable (@typing cf Σ Γ t T)) in quote_typing'.
    all: change (forall Γ t s T, ground_quotable (@typing_spine cf Σ Γ t s T)) in quote_typing_spine'.
    all: destruct pf.
    Time all: [ > time exact _ .. ].
  Defined.
End quote_typing.
*)
#[export] Instance quote_typing_well_typed {cf Σ Γ t T} : ground_quotable_well_typed_using [@typing] (@typing cf Σ Γ t T).
Proof.
Admitted.
(*
#[export] Instance quote_typing_spine {cf Σ Γ t s T} : ground_quotable (@typing_spine cf Σ Γ t s T) := quote_typing_spine'.

#[export] Instance quote_has_nparams {npars ty} : ground_quotable (@has_nparams npars ty) := _.
#[export] Instance quote_infer_sorting {cf Σ Γ T} : ground_quotable (@infer_sorting cf Σ Γ T) := _.

Module QuoteTemplateTyping <: QuoteTyping TemplateTerm Env TemplateTermUtils TemplateEnvTyping
                                          TemplateConversion TemplateConversionPar TemplateTyping.
  #[export] Instance qtyping : quotation_of (@TemplateTyping.typing) := _.
  #[export] Instance quote_typing {cf Σ Γ t T} : ground_quotable (@TemplateTyping.typing cf Σ Γ t T) := _.

  Module Instances.
    #[export] Existing Instances
     qtyping
     quote_typing
    .
  End Instances.
End QuoteTemplateTyping.
Export QuoteTemplateTyping.Instances.

Module QuoteTemplateDeclarationTyping
  := QuoteDeclarationTyping
       TemplateTerm
       Env
       TemplateTermUtils
       TemplateEnvTyping
       TemplateConversion
       TemplateConversionPar
       TemplateTyping
       TemplateLookup
       TemplateGlobalMaps
       TemplateDeclarationTyping
       QuoteTemplateTerm QuotationOfEnv QuotationOfTemplateEnvTyping QuotationOfTemplateConversion QuotationOfTemplateGlobalMaps QuoteTemplateTyping.
Export QuoteTemplateDeclarationTyping.Instances.
 *)
#[export] Instance quote_wf_well_typed {cf Σ} : ground_quotable_well_typed_using [@typing] (@wf cf Σ).
Proof. Admitted.
#[export] Instance quote_wf_ext_well_typed {cf Σ} : ground_quotable_well_typed_using [@typing] (@wf_ext cf Σ).
Proof. Admitted.
(*
#[export] Instance quote_Forall_typing_spine {cf Σ Γ P T t U tls} {qP : quotation_of P} {quoteP : forall x y, ground_quotable (P x y)} : ground_quotable (@Forall_typing_spine cf Σ Γ P T t U tls) := ltac:(induction 1; exact _).
*)
