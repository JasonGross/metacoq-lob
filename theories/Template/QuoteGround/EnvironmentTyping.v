From MetaCoq.Lob.Template.QuoteGround Require Export Coq.Init Coq.Misc Coq.ssr config utils BasicAst Universes Environment Primitive.
From MetaCoq.Lob.Template.Decidable Require Import EnvironmentTyping.
From MetaCoq.Template Require Import BasicAst Environment EnvironmentTyping.

Module QuoteLookup (Import T : Term) (Import E : EnvironmentSig T) (Import L : LookupSig T E) (Import QT : QuoteTerm T) (Import QoE : QuotationOfEnvironment T E).
  Module Import LDecide := LookupDecide T E L.
  Module Import QE := QuoteEnvironment T E QT QoE.

  Section with_refl.
    #[local] Hint Extern 2 => reflexivity : typeclass_instances.
    #[export] Polymorphic Instance quote_udecl_decl {F d} {quoteF1 : forall cb, d = ConstantDecl cb -> ground_quotable (F cb.(cst_universes))} {quoteF2 : forall mb, d = InductiveDecl mb -> ground_quotable (F mb.(ind_universes))} : ground_quotable (@on_udecl_decl _ F d) := ltac:(cbv [on_udecl_decl]; exact _).
  End with_refl.

  #[export] Instance quote_consistent_instance {cf lvs ϕ uctx u} : ground_quotable (@consistent_instance cf lvs ϕ uctx u) := ltac:(cbv [consistent_instance]; exact _).

  #[export] Instance qglobal_levels : quotation_of global_levels := ltac:(cbv [global_levels]; exact _).
  #[export] Instance qglobal_ext_levels : quotation_of global_ext_levels := ltac:(cbv [global_ext_levels]; exact _).
  #[export] Instance qwf_universe : quotation_of wf_universe
    := ltac:(cbv [wf_universe]; exact _).

  #[export] Instance quote_wf_universe {Σ s} : ground_quotable (@wf_universe Σ s)
    := ground_quotable_of_dec (@wf_universe_dec Σ s).


  #[export] Instance qdeclared_constant : quotation_of declared_constant := ltac:(cbv [declared_constant]; exact _).
  #[export] Instance qdeclared_minductive : quotation_of declared_minductive := ltac:(cbv [declared_minductive]; exact _).
  #[export] Instance qdeclared_inductive : quotation_of declared_inductive := ltac:(cbv [declared_inductive]; exact _).
  #[export] Instance qdeclared_constructor : quotation_of declared_constructor := ltac:(cbv [declared_constructor]; exact _).
  #[export] Instance qdeclared_projection : quotation_of declared_projection := ltac:(cbv [declared_projection]; exact _).

  #[export] Instance quote_declared_constant {Σ id decl} : ground_quotable (@declared_constant Σ id decl) := _.
  #[export] Instance quote_declared_minductive {Σ mind decl} : ground_quotable (@declared_minductive Σ mind decl) := _.
  #[export] Instance quote_declared_inductive {Σ ind mdecl decl} : ground_quotable (@declared_inductive Σ ind mdecl decl) := _.
  #[export] Instance quote_declared_constructor {Σ cstr mdecl idecl cdecl} : ground_quotable (@declared_constructor Σ cstr mdecl idecl cdecl) := _.
  #[export] Instance quote_declared_projection {Σ proj mdecl idecl cdecl pdecl} : ground_quotable (@declared_projection Σ proj mdecl idecl cdecl pdecl) := _.

  Module Instances.
    #[export] Existing Instances
     quote_udecl_decl
     quote_consistent_instance
     qwf_universe
     quote_wf_universe
     qglobal_levels
     qglobal_ext_levels
     qdeclared_constant
     qdeclared_minductive
     qdeclared_inductive
     qdeclared_constructor
     qdeclared_projection
     quote_declared_constant
     quote_declared_minductive
     quote_declared_inductive
     quote_declared_constructor
     quote_declared_projection
    .
  End Instances.
End QuoteLookup.

Module Type QuotationOfEnvTyping (Import T : Term) (Import E : EnvironmentSig T) (Import TU : TermUtils T E) (Import ET : EnvTypingSig T E TU).
  #[export] Declare Instance qAll_local_env : inductive_quotation_of All_local_env.
  #[export] Declare Instance qAll_local_env_over_gen : inductive_quotation_of All_local_env_over_gen.
  #[export] Declare Instance qctx_inst : inductive_quotation_of ctx_inst.
End QuotationOfEnvTyping.

Module QuoteEnvTyping (Import T : Term) (Import E : EnvironmentSig T) (Import TU : TermUtils T E) (Import ET : EnvTypingSig T E TU) (Import QT : QuoteTerm T) (Import QoE : QuotationOfEnvironment T E) (Import QoET : QuotationOfEnvTyping T E TU ET).
  Module Import QE := QuoteEnvironment T E QT QoE.

  #[export] Instance quote_All_local_env {typing Γ} {qtyping : quotation_of typing} {quote_typing : forall Γ t T, ground_quotable (typing Γ t T)} : ground_quotable (@All_local_env typing Γ) := ltac:(induction 1; exact _).
  #[export] Instance quote_on_local_decl {P Γ d} {quoteP1 : forall b, d.(decl_body) = Some b -> ground_quotable (P Γ b (Typ d.(decl_type)))} {quoteP2 : d.(decl_body) = None -> ground_quotable (P Γ d.(decl_type) Sort)} : ground_quotable (@on_local_decl P Γ d) := ltac:(cbv [on_local_decl]; exact _).
  #[local] Hint Extern 2 (_ = _) => reflexivity : typeclass_instances.
  #[export] Instance quote_lift_judgment {check infer_sort Σ Γ t T} {quote_check : forall T', T = Typ T' -> ground_quotable (check Σ Γ t T')} {quote_infer_sort : T = Sort -> ground_quotable (infer_sort Σ Γ t)} : ground_quotable (@lift_judgment check infer_sort Σ Γ t T) := ltac:(cbv [lift_judgment]; exact _).

  #[export] Instance qlift_judgment : quotation_of lift_judgment := ltac:(cbv -[quotation_of]; exact _).
  #[export] Instance qlift_typing : quotation_of lift_typing := ltac:(cbv -[quotation_of]; exact _).

  #[export] Instance quote_All_local_env_over_gen
   {checking sorting cproperty sproperty Σ Γ H}
   {qchecking : quotation_of checking} {qsorting : quotation_of sorting} {qcproperty : quotation_of cproperty} {qsproperty : quotation_of sproperty}
   {quote_checking : forall Γ t T, ground_quotable (checking Σ Γ t T)} {quote_sorting : forall Γ T, ground_quotable (sorting Σ Γ T)} {quote_sproperty : forall Γ all t tu, ground_quotable (sproperty Σ Γ all t tu)} {quote_cproperty : forall Γ all b t tb, ground_quotable (cproperty Σ Γ all b t tb)}
    : ground_quotable (@All_local_env_over_gen checking sorting cproperty sproperty Σ Γ H)
    := ltac:(induction 1; exact _).

  #[export] Instance qinfer_sort : quotation_of infer_sort := ltac:(cbv -[quotation_of]; exact _).
  #[export] Instance qcontext : quotation_of context := ltac:(cbv -[quotation_of]; exact _).

  #[export] Instance quote_All_local_env_over {typing property Σ Γ H}
   {qtyping : quotation_of typing} {qproperty : quotation_of property}
   {quote_typing : forall Γ t T, ground_quotable (typing Σ Γ t T)} {quote_property : forall Γ all b t tb, ground_quotable (property Σ Γ all b t tb)}
    : ground_quotable (@All_local_env_over typing property Σ Γ H)
    := _.

  #[export] Instance quote_All_local_env_over_sorting
   {checking sorting cproperty sproperty Σ Γ H}
   {qchecking : quotation_of checking} {qsorting : quotation_of sorting} {qcproperty : quotation_of cproperty} {qsproperty : quotation_of sproperty}
   {quote_checking : forall Γ t T, ground_quotable (checking Σ Γ t T)} {quote_sorting : forall Γ T U, ground_quotable (sorting Σ Γ T U)} {quote_sproperty : forall Γ all t tu U, ground_quotable (sproperty Σ Γ all t tu U)} {quote_cproperty : forall Γ all b t tb, ground_quotable (cproperty Σ Γ all b t tb)}
    : ground_quotable (@All_local_env_over_sorting checking sorting cproperty sproperty Σ Γ H)
    := _.

  #[export] Instance quote_ctx_inst {typing Σ Γ ctx inst}
   {qtyping : quotation_of typing}
   {quote_typing : forall i t, ground_quotable (typing Σ Γ i t)}
    : ground_quotable (@ctx_inst typing Σ Γ ctx inst)
    := ltac:(induction 1; exact _).

  Module Instances.
    #[export] Existing Instances
     quote_All_local_env
     quote_on_local_decl
     quote_lift_judgment
     qlift_judgment
     qlift_typing
     quote_All_local_env_over_gen
     qinfer_sort
     qglobal_env_ext
     qcontext
     quote_All_local_env_over
     quote_All_local_env_over_sorting
     quote_ctx_inst
    .
  End Instances.
End QuoteEnvTyping.

Module Type QuotationOfConversion (Import T : Term) (Import E : EnvironmentSig T) (Import TU : TermUtils T E) (Import ET : EnvTypingSig T E TU) (Import C : ConversionSig T E TU ET).
  #[export] Declare Instance qAll_decls_alpha_pb : inductive_quotation_of All_decls_alpha_pb.
End QuotationOfConversion.

Module QuoteConversion (Import T : Term) (Import E : EnvironmentSig T) (Import TU : TermUtils T E) (Import ET : EnvTypingSig T E TU) (Import C : ConversionSig T E TU ET) (Import QT : QuoteTerm T) (Import QoE : QuotationOfEnvironment T E) (Import QoC : QuotationOfConversion T E TU ET C).
  Module Import QE := QuoteEnvironment T E QT QoE.

  #[export] Instance quote_All_decls_alpha_pb {pb P b b'} {qP : quotation_of P} {quoteP : forall pb t t', ground_quotable (P pb t t')}
    : ground_quotable (@All_decls_alpha_pb pb P b b') := ltac:(induction 1; exact _).

  #[export] Instance qcumul_pb_decls : quotation_of cumul_pb_decls := ltac:(cbv -[quotation_of]; exact _).
  #[export] Instance qapp_context : quotation_of app_context := ltac:(cbv [app_context context]; exact _).
  #[export] Instance qcumul_ctx_rel : quotation_of cumul_ctx_rel := ltac:(cbv -[quotation_of]; exact _).

  #[export] Instance quote_cumul_pb_decls {cumul_gen pb Σ Γ Γ' x y}
   {qcumul_gen : quotation_of cumul_gen}
   {quote_cumul_gen : forall pb t t', ground_quotable (cumul_gen Σ Γ pb t t')}
    : ground_quotable (@cumul_pb_decls cumul_gen pb Σ Γ Γ' x y)
    := _.

  #[export] Instance quote_cumul_pb_context {cumul_gen pb Σ Γ Γ'}
   {qcumul_gen : quotation_of cumul_gen}
   {quote_cumul_gen : forall Γ pb t t', ground_quotable (cumul_gen Σ Γ pb t t')}
    : ground_quotable (@cumul_pb_context cumul_gen pb Σ Γ Γ')
    := _.

  #[export] Instance quote_cumul_ctx_rel {cumul_gen Σ Γ Δ Δ'}
   {qcumul_gen : quotation_of cumul_gen}
   {quote_cumul_gen : forall Γ pb t t', ground_quotable (cumul_gen Σ Γ pb t t')}
    : ground_quotable (@cumul_ctx_rel cumul_gen Σ Γ Δ Δ')
    := _.

  Module Instances.
    #[export] Existing Instances
     quote_All_decls_alpha_pb
     qcumul_pb_decls
     qapp_context
     quote_cumul_pb_decls
     quote_cumul_pb_context
     quote_cumul_ctx_rel
     qcumul_ctx_rel
    .
  End Instances.
End QuoteConversion.

Module Type QuotationOfGlobalMaps (Import T: Term) (Import E: EnvironmentSig T) (Import TU : TermUtils T E) (Import ET: EnvTypingSig T E TU) (Import C: ConversionSig T E TU ET) (Import L: LookupSig T E) (Import GM : GlobalMapsSig T E TU ET C L).
  #[export] Declare Instance qpositive_cstr_arg : inductive_quotation_of positive_cstr_arg.
  #[export] Declare Instance qpositive_cstr : inductive_quotation_of positive_cstr.
  #[export] Declare Instance qon_constructor : inductive_quotation_of (@on_constructor).
  #[export] Declare Instance qon_proj : inductive_quotation_of on_proj.
  #[export] Declare Instance qon_projections : inductive_quotation_of on_projections.
  #[export] Declare Instance qon_ind_body : inductive_quotation_of (@on_ind_body).
  #[export] Declare Instance qon_inductive : inductive_quotation_of (@on_inductive).
  #[export] Declare Instance qon_global_decls_data : inductive_quotation_of (@on_global_decls_data).
  #[export] Declare Instance qon_global_decls : inductive_quotation_of (@on_global_decls).
End QuotationOfGlobalMaps.

Module QuoteGlobalMaps (Import T: Term) (Import E: EnvironmentSig T) (Import TU : TermUtils T E) (Import ET: EnvTypingSig T E TU) (Import C: ConversionSig T E TU ET) (Import L: LookupSig T E) (Import GM : GlobalMapsSig T E TU ET C L) (Import QT : QuoteTerm T) (Import QoE : QuotationOfEnvironment T E) (Import QoET : QuotationOfEnvTyping T E TU ET) (Import QoC : QuotationOfConversion T E TU ET C) (Import QoGM :  QuotationOfGlobalMaps T E TU ET C L GM).
  Module Import QE := QuoteEnvironment T E QT QoE.
  Module Import QET := QuoteEnvTyping T E TU ET QT QoE QoET.
  Module Import QC := QuoteConversion T E TU ET C QT QoE QoC.
  Module Import QL := QuoteLookup T E L QT QoE.

  Section GlobalMaps.
    Context {cf : config.checker_flags}
            {Pcmp: global_env_ext -> context -> conv_pb -> term -> term -> Type}
            {P : global_env_ext -> context -> term -> typ_or_sort -> Type}
            {qPcmp : quotation_of Pcmp} {qP : quotation_of P}
            {quotePcmp : forall Σ Γ pb t T, ground_quotable (Pcmp Σ Γ pb t T)}
            {quoteP : forall Σ Γ t T, ground_quotable (P Σ Γ t T)}.

    #[export] Instance quote_on_context {Σ ctx} : ground_quotable (@on_context P Σ ctx)
      := _.

    #[export] Instance qtype_local_ctx : quotation_of type_local_ctx := ltac:(cbv [type_local_ctx]; exact _).
    #[export] Instance qsorts_local_ctx : quotation_of sorts_local_ctx := ltac:(cbv [sorts_local_ctx]; exact _).
    #[export] Instance qunivs_ext_constraints : quotation_of univs_ext_constraints := ltac:(cbv [univs_ext_constraints]; exact _).
    #[export] Instance qsatisfiable_udecl : quotation_of satisfiable_udecl := ltac:(cbv [satisfiable_udecl]; exact _).
    #[export] Instance qvalid_on_mono_udecl : quotation_of valid_on_mono_udecl := ltac:(cbv [valid_on_mono_udecl]; exact _).
    #[export] Instance qsubst_instance_context : quotation_of subst_instance_context := ltac:(cbv [subst_instance_context]; exact _).
    #[export] Instance qarities_context : quotation_of arities_context := ltac:(cbv -[quotation_of]; exact _).
    #[export] Instance qind_arities : quotation_of ind_arities := ltac:(cbv -[quotation_of]; exact _).
    #[export] Instance qlift_level : quotation_of lift_level := ltac:(cbv [lift_level]; exact _).
    #[export] Instance qlift_constraint : quotation_of lift_constraint := ltac:(cbv [lift_constraint]; exact _).
    #[export] Instance qlift_constraints : quotation_of lift_constraints := ltac:(cbv [lift_constraints]; exact _).
    #[export] Instance qlift_instance : quotation_of lift_instance := ltac:(cbv [lift_instance]; exact _).
    #[export] Instance qvariance_cstrs : quotation_of variance_cstrs := ltac:(cbv [variance_cstrs]; exact _).
    #[export] Instance qlevel_var_instance : quotation_of level_var_instance := ltac:(cbv [level_var_instance]; exact _).
    #[export] Instance qvariance_universes : quotation_of variance_universes := ltac:(cbv [variance_universes]; exact _).
    #[export] Instance qcstr_respects_variance : quotation_of cstr_respects_variance := ltac:(cbv [cstr_respects_variance]; exact _).
    #[export] Instance qconstructor_univs : quotation_of constructor_univs := ltac:(cbv [constructor_univs]; exact _).
    #[export] Instance qind_respects_variance : quotation_of ind_respects_variance := ltac:(cbv [ind_respects_variance]; exact _).
    #[export] Instance qon_global_univs : quotation_of on_global_univs := ltac:(cbv [on_global_univs]; exact _).
    #[export] Instance qon_udecl : quotation_of on_udecl := ltac:(cbv [on_udecl]; exact _).
    #[export] Instance qon_global_env : quotation_of (@on_global_env) := ltac:(cbv [on_global_env retroknowledge]; exact _).

    #[export] Instance quote_constructor_univs : ground_quotable constructor_univs := _.

    #[export] Instance quote_type_local_ctx {Σ Γ Δ u} : ground_quotable (@type_local_ctx P Σ Γ Δ u)
      := ltac:(induction Δ; cbn [type_local_ctx]; exact _).

    #[export] Instance quote_sorts_local_ctx {Σ Γ Δ us} : ground_quotable (@sorts_local_ctx P Σ Γ Δ us)
      := ltac:(revert us; induction Δ, us; cbn [sorts_local_ctx]; exact _).

    #[export] Instance quote_on_type {Σ Γ T} : ground_quotable (@on_type P Σ Γ T) := _.

    #[export] Instance quote_on_udecl {univs udecl} : ground_quotable (@on_udecl univs udecl)
      := ltac:(cbv [on_udecl]; exact _).
    #[export] Instance quote_satisfiable_udecl {univs ϕ} : ground_quotable (@satisfiable_udecl univs ϕ) := _.
    #[export] Instance quote_valid_on_mono_udecl {univs ϕ} : ground_quotable (@valid_on_mono_udecl univs ϕ) := _.

    #[export] Instance quote_positive_cstr_arg {mdecl ctx t} : ground_quotable (@positive_cstr_arg mdecl ctx t) := ltac:(induction 1; exact _).
    #[export] Instance quote_positive_cstr {mdecl i ctx t} : ground_quotable (@positive_cstr mdecl i ctx t) := ltac:(induction 1; exact _).

    Import StrongerInstances.
    #[export] Instance quote_ind_respects_variance {Σ mdecl v indices} : ground_quotable (@ind_respects_variance Pcmp Σ mdecl v indices) := ltac:(cbv [ind_respects_variance]; exact _).
    #[export] Instance quote_cstr_respects_variance {Σ mdecl v cs} : ground_quotable (@cstr_respects_variance Pcmp Σ mdecl v cs) := ltac:(cbv [cstr_respects_variance]; exact _).
    #[export] Instance quote_on_constructor {Σ mdecl i idecl ind_indices cdecl cunivs} : ground_quotable (@on_constructor cf Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs) := ltac:(destruct 1; exact _).
    #[export] Instance quote_on_proj {mdecl mind i k p decl} : ground_quotable (@on_proj mdecl mind i k p decl) := ltac:(destruct 1; cbv [proj_type] in *; exact _).
    #[export] Instance quote_on_projection {mdecl mind i cdecl k p} : ground_quotable (@on_projection mdecl mind i cdecl k p) := ltac:(cbv [on_projection]; exact _).
    #[export] Instance quote_on_projections {mdecl mind i idecl ind_indices cdecl} : ground_quotable (@on_projections mdecl mind i idecl ind_indices cdecl) := ltac:(destruct 1; cbv [on_projection] in *; exact _).
    #[export] Instance quote_check_ind_sorts {Σ params kelim ind_indices cdecls ind_sort} : ground_quotable (@check_ind_sorts cf P Σ params kelim ind_indices cdecls ind_sort) := ltac:(cbv [check_ind_sorts check_constructors_smaller global_ext_constraints global_constraints] in *; exact _).
    #[export] Instance quote_on_ind_body {Σ mind mdecl i idecl} : ground_quotable (@on_ind_body cf Pcmp P Σ mind mdecl i idecl) := ltac:(destruct 1; cbv [it_mkProd_or_LetIn mkProd_or_LetIn ind_indices ind_sort] in *; exact _).
    #[export] Instance quote_on_variance {Σ univs variances} : ground_quotable (@on_variance cf Σ univs variances) := ltac:(cbv [on_variance consistent_instance_ext consistent_instance global_ext_constraints global_constraints]; exact _).
    #[export] Instance quote_on_inductive {Σ mind mdecl} : ground_quotable (@on_inductive cf Pcmp P Σ mind mdecl) := ltac:(destruct 1; exact _).
    #[export] Instance quote_on_constant_decl {Σ d} : ground_quotable (@on_constant_decl P Σ d) := ltac:(cbv [on_constant_decl]; exact _).
    #[export] Instance quote_on_global_decl {Σ kn d} : ground_quotable (@on_global_decl cf Pcmp P Σ kn d) := ltac:(cbv [on_global_decl]; exact _).
    #[export] Instance quote_on_global_decls_data {univs retro Σ kn d} : ground_quotable (@on_global_decls_data cf Pcmp P univs retro Σ kn d) := ltac:(destruct 1; exact _).
    #[export] Instance quote_on_global_decls {univs retro Σ} : ground_quotable (@on_global_decls cf Pcmp P univs retro Σ) := ltac:(induction 1; exact _).
    #[export] Instance quote_on_global_univs {univs} : ground_quotable (@on_global_univs univs) := ltac:(cbv [on_global_univs]; exact _).
    #[export] Instance quote_on_global_env {g} : ground_quotable (@on_global_env cf Pcmp P g) := ltac:(cbv [on_global_env]; exact _).
    #[export] Instance quote_on_global_env_ext {Σ} : ground_quotable (@on_global_env_ext cf Pcmp P Σ) := ltac:(cbv [on_global_env_ext]; exact _).
  End GlobalMaps.

  Module Instances.
    #[export] Existing Instances
     quote_on_context
     qtype_local_ctx
     qsorts_local_ctx
     qunivs_ext_constraints
     qsatisfiable_udecl
     qvalid_on_mono_udecl
     qsubst_instance_context
     qarities_context
     qind_arities
     qlift_level
     qlift_constraint
     qlift_constraints
     qlift_instance
     qvariance_cstrs
     qlevel_var_instance
     qvariance_universes
     qcstr_respects_variance
     qconstructor_univs
     qind_respects_variance
     qon_global_univs
     qon_udecl
     qon_global_env
     quote_constructor_univs
     quote_type_local_ctx
     quote_sorts_local_ctx
     quote_on_type
     quote_on_udecl
     quote_satisfiable_udecl
     quote_valid_on_mono_udecl
     quote_positive_cstr_arg
     quote_positive_cstr
     quote_ind_respects_variance
     quote_cstr_respects_variance
     quote_on_constructor
     quote_on_proj
     quote_on_projection
     quote_on_projections
     quote_check_ind_sorts
     quote_on_ind_body
     quote_on_variance
     quote_on_inductive
     quote_on_constant_decl
     quote_on_global_decl
     quote_on_global_decls_data
     quote_on_global_decls
     quote_on_global_univs
     quote_on_global_env
     quote_on_global_env_ext
    .
  End Instances.
End QuoteGlobalMaps.

Module Type QuoteConversionPar (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU) (Import CS : ConversionParSig T E TU ET).
  #[export] Declare Instance qcumul_gen : quotation_of (@cumul_gen).
  #[export] Declare Instance quote_cumul_gen {cf Σ Γ pb t t'} : ground_quotable (@cumul_gen cf Σ Γ pb t t').
End QuoteConversionPar.

Module Type QuoteTyping (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU)
       (CT : ConversionSig T E TU ET) (CS : ConversionParSig T E TU ET) (Import Ty : Typing T E TU ET CT CS).

  #[export] Declare Instance qtyping : quotation_of (@typing).
  #[export] Declare Instance quote_typing {cf Σ Γ t T} : ground_quotable (@typing cf Σ Γ t T).
End QuoteTyping.

Fail Module Type DeclarationTypingSig := DeclarationTypingSig.
Module Type DeclarationTypingSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E)
       (ET : EnvTypingSig T E TU) (CT : ConversionSig T E TU ET)
       (CS : ConversionParSig T E TU ET) (Ty : Typing T E TU ET CT CS)
       (L : LookupSig T E) (GM : GlobalMapsSig T E TU ET CT L).
  Include DeclarationTyping T E TU ET CT CS Ty L GM.
End DeclarationTypingSig.

Module QuoteDeclarationTyping (Import T : Term) (Import E : EnvironmentSig T) (Import TU : TermUtils T E)
       (Import ET : EnvTypingSig T E TU) (Import CT : ConversionSig T E TU ET)
       (Import CS : ConversionParSig T E TU ET) (Import Ty : Typing T E TU ET CT CS)
       (Import L : LookupSig T E) (Import GM : GlobalMapsSig T E TU ET CT L)
       (Import DT : DeclarationTypingSig T E TU ET CT CS Ty L GM)
       (Import QT : QuoteTerm T) (Import QoE : QuotationOfEnvironment T E) (Import QoET : QuotationOfEnvTyping T E TU ET) (Import QoC : QuotationOfConversion T E TU ET CT) (Import QoGM :  QuotationOfGlobalMaps T E TU ET CT L GM) (Import QTy : QuoteTyping T E TU ET CT CS Ty).
  Module Import QE := QuoteEnvironment T E QT QoE.
  Module Import QET := QuoteEnvTyping T E TU ET QT QoE QoET.
  Module Import QC := QuoteConversion T E TU ET CT QT QoE QoC.
  Module Import QL := QuoteLookup T E L QT QoE.
  Module Import QGM := QuoteGlobalMaps T E TU ET CT L GM QT QoE QoET QoC QoGM.

  Import StrongerInstances.
  #[export] Instance quote_type_local_decl {cf Σ Γ d} : ground_quotable (@type_local_decl cf Σ Γ d) := ltac:(cbv [type_local_decl isType]; exact _).
  #[export] Instance quote_wf_local_rel {cf Σ Γ Γ'} : ground_quotable (@wf_local_rel cf Σ Γ Γ') := _.
  Module Instances.
    #[export] Existing Instances
     quote_type_local_decl
     quote_wf_local_rel
    .
  End Instances.
End QuoteDeclarationTyping.
