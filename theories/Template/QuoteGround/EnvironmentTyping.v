From MetaCoq.Lob.Template.QuoteGround Require Export Coq.Init Coq.ssr config utils BasicAst Universes Environment Primitive.
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

  Module Instances.
    #[export] Existing Instances
     quote_udecl_decl
     quote_consistent_instance
     qwf_universe
     quote_wf_universe
     qglobal_levels
     qglobal_ext_levels
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

    #[export] Instance quote_type_local_ctx {Σ Γ Δ u} : ground_quotable (@type_local_ctx P Σ Γ Δ u)
      := ltac:(induction Δ; cbn [type_local_ctx]; exact _).

    #[export] Instance quote_sorts_local_ctx {Σ Γ Δ us} : ground_quotable (@sorts_local_ctx P Σ Γ Δ us)
      := ltac:(revert us; induction Δ, us; cbn [sorts_local_ctx]; exact _).

    #[export] Instance quote_on_type {Σ Γ T} : ground_quotable (@on_type P Σ Γ T) := _.

    #[local] Hint Extern 1 (ground_quotable (Universes.LevelSet.For_all _ _)) => simple eapply @QuoteLevelSet.quote_For_all : typeclass_instances.
    #[local] Hint Extern 1 (ground_quotable (Universes.ConstraintSet.For_all _ _)) => simple eapply @QuoteConstraintSet.quote_For_all : typeclass_instances.

    #[export] Instance quote_on_udecl {univs udecl} : ground_quotable (@on_udecl univs udecl)
      := ltac:(cbv [on_udecl]; exact _).
    #[export] Instance quote_satisfiable_udecl {univs ϕ} : ground_quotable (@satisfiable_udecl univs ϕ) := _.
    #[export] Instance quote_valid_on_mono_udecl {univs ϕ} : ground_quotable (@valid_on_mono_udecl univs ϕ) := _.

    #[export] Instance quote_positive_cstr_arg {mdecl ctx t} : ground_quotable (@positive_cstr_arg mdecl ctx t) := ltac:(induction 1; exact _).
    #[export] Instance quote_positive_cstr {mdecl i ctx t} : ground_quotable (@positive_cstr mdecl i ctx t) := ltac:(induction 1; exact _).

    Import StrongerInstances.
    #[export] Instance quote_ind_respects_variance {Σ mdecl v indices} : ground_quotable (@ind_respects_variance Pcmp Σ mdecl v indices) := ltac:(cbv [ind_respects_variance]; exact _).
    #[export] Instance quote_cstr_respects_variance {Σ mdecl v cs} : ground_quotable (@cstr_respects_variance Pcmp Σ mdecl v cs) := ltac:(cbv [cstr_respects_variance]; exact _).
    #[export] Instance quote_on_constructor {Σ mdecl i idecl ind_indices cdecl cunivs} : ground_quotable (@on_constructor cf Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs).

    destruct 1; try exact _.
    repeat match goal with H : _ |- _ => generalize (_ : quotation_of H); revert H end.

         Record on_constructor Σ mdecl i idecl ind_indices cdecl cunivs := {


    repeat match goal with H : _ |- _ => generalize (_ : quotation_of H); revert H end.
      := ltac:(induction 1; exact _).

    Inductive positive_cstr mdecl i (ctx : context) : term -> Type :=
    Record on_constructor Σ mdecl i idecl ind_indices cdecl cunivs := {
    Record on_proj mdecl mind i k (p : projection_body) decl :=
    Record on_projections mdecl mind i idecl (ind_indices : context) cdecl :=
    Record on_ind_body Σ mind mdecl i idecl :=
    Record on_inductive Σ mind mdecl :=
    Record on_global_decls_data (univs : ContextSet.t) retro (Σ : global_declarations) (kn : kername) (d : global_decl) :=
    Inductive on_global_decls (univs : ContextSet.t) (retro : Retroknowledge.t): global_declarations -> Type :=


    Open Scope type_scope.



    Record on_constructor Σ mdecl i idecl ind_indices cdecl cunivs := {
      (* cdecl.1 fresh ?? *)
      cstr_args_length : context_assumptions (cstr_args cdecl) = cstr_arity cdecl;

      cstr_eq : cstr_type cdecl =
       it_mkProd_or_LetIn mdecl.(ind_params)
        (it_mkProd_or_LetIn (cstr_args cdecl)
          (cstr_concl mdecl i cdecl));
      (* The type of the constructor canonically has this shape: parameters, real
        arguments ending with a reference to the inductive applied to the
        (non-lets) parameters and arguments *)

      on_ctype : on_type Σ (arities_context mdecl.(ind_bodies)) (cstr_type cdecl);
      on_cargs :
        sorts_local_ctx Σ (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params))
                      cdecl.(cstr_args) cunivs;
      on_cindices :
        ctx_inst (fun Σ Γ t T => P Σ Γ t (Typ T)) Σ (arities_context mdecl.(ind_bodies) ,,, mdecl.(ind_params) ,,, cdecl.(cstr_args))
                      cdecl.(cstr_indices)
                      (List.rev (lift_context #|cdecl.(cstr_args)| 0 ind_indices));

      on_ctype_positive : (* The constructor type is positive *)
        positive_cstr mdecl i [] (cstr_type cdecl);

      on_ctype_variance : (* The constructor type respect the variance annotation
        on polymorphic universes, if any. *)
        forall v, ind_variance mdecl = Some v ->
        cstr_respects_variance Σ mdecl v cdecl;

      on_lets_in_type : if lets_in_constructor_types
                        then True else is_true (is_assumption_context (cstr_args cdecl))
    }.

    Arguments on_ctype {Σ mdecl i idecl ind_indices cdecl cunivs}.
    Arguments on_cargs {Σ mdecl i idecl ind_indices cdecl cunivs}.
    Arguments on_cindices {Σ mdecl i idecl ind_indices cdecl cunivs}.
    Arguments cstr_args_length {Σ mdecl i idecl ind_indices cdecl cunivs}.
    Arguments cstr_eq {Σ mdecl i idecl ind_indices cdecl cunivs}.

    Definition on_constructors Σ mdecl i idecl ind_indices :=
      All2 (on_constructor Σ mdecl i idecl ind_indices).

    (** Each projection type corresponds to a non-let argument of the
        corresponding constructor. It is parameterized over the
        parameters of the inductive type and all the preceding arguments
        of the constructor. When computing the type of a projection for argument
        [n] at a given instance of the parameters and a given term [t] in the inductive
        type, we instantiate the argument context by corresponsping projections
        [t.π1 ... t.πn-1]. This is essential for subject reduction to hold: each
        projections type can only refer to the record object through projections.

      Projection types have their parameter and argument contexts smashed to avoid
      costly computations during type-checking and reduction: we can just substitute
      the instances of parameters and the inductive value without considering the
      presence of let bindings. *)

    Record on_proj mdecl mind i k (p : projection_body) decl :=
      { on_proj_name : (* All projections are be named after a constructor argument. *)
          binder_name (decl_name decl) = nNamed p.(proj_name);
        on_proj_type :
          (** The stored projection type already has the references to the inductive
              type substituted along with the previous arguments replaced by projections. *)
          let u := abstract_instance mdecl.(ind_universes) in
          let ind := {| inductive_mind := mind; inductive_ind := i |} in
          p.(proj_type) = subst (inds mind u mdecl.(ind_bodies)) (S (ind_npars mdecl))
            (subst (projs ind mdecl.(ind_npars) k) 0
              (lift 1 k (decl_type decl)));
        on_proj_relevance : p.(proj_relevance) = decl.(decl_name).(binder_relevance) }.

    Definition on_projection mdecl mind i cdecl (k : nat) (p : projection_body) :=
      let Γ := smash_context [] (cdecl.(cstr_args) ++ mdecl.(ind_params)) in
      match nth_error Γ (context_assumptions cdecl.(cstr_args) - S k) with
      | None => False
      | Some decl => on_proj mdecl mind i k p decl
      end.

    Record on_projections mdecl mind i idecl (ind_indices : context) cdecl :=
      { on_projs_record : #|idecl.(ind_ctors)| = 1;
        (** The inductive must be a record *)

        on_projs_noidx : #|ind_indices| = 0;
        (** The inductive cannot have indices *)

        on_projs_elim : idecl.(ind_kelim) = IntoAny;
        (** This ensures that all projections are definable *)

        on_projs_all : #|idecl.(ind_projs)| = context_assumptions (cstr_args cdecl);
        (** There are as many projections as (non-let) constructor arguments *)

        on_projs : Alli (on_projection mdecl mind i cdecl) 0 idecl.(ind_projs) }.

    Definition check_constructors_smaller φ cunivss ind_sort :=
      Forall (fun cunivs =>
        Forall (fun argsort => leq_universe φ argsort ind_sort) cunivs) cunivss.

    (** This ensures that all sorts in kelim are lower
        or equal to the top elimination sort, if set.
        For inductives in Type we do not check [kelim] currently. *)

    Definition constructor_univs := list Universe.t.
    (* The sorts of the arguments context (without lets) *)

    Definition elim_sort_prop_ind (ind_ctors_sort : list constructor_univs) :=
      match ind_ctors_sort with
      | [] => (* Empty inductive proposition: *) IntoAny
      | [ s ] =>
        if forallb Universes.is_propositional s then
          IntoAny (* Singleton elimination *)
        else
          IntoPropSProp (* Squashed: some arguments are higher than Prop, restrict to Prop *)
      | _ => (* Squashed: at least 2 constructors *) IntoPropSProp
      end.

    Definition elim_sort_sprop_ind (ind_ctors_sort : list constructor_univs) :=
      match ind_ctors_sort with
      | [] => (* Empty inductive strict proposition: *) IntoAny
      | _ => (* All other inductives in SProp are squashed *) IntoSProp
      end.

    Definition check_ind_sorts (Σ : global_env_ext)
              params kelim ind_indices cdecls ind_sort : Type :=
      if Universe.is_prop ind_sort then
        (** The inductive is declared in the impredicative sort Prop *)
        (** No universe-checking to do: any size of constructor argument is allowed,
            however elimination restrictions apply. *)
        (allowed_eliminations_subset kelim (elim_sort_prop_ind cdecls) : Type)
      else if Universe.is_sprop ind_sort then
        (** The inductive is declared in the impredicative sort SProp *)
        (** No universe-checking to do: any size of constructor argument is allowed,
            however elimination restrictions apply. *)
        (allowed_eliminations_subset kelim (elim_sort_sprop_ind cdecls) : Type)
      else
        (** The inductive is predicative: check that all constructors arguments are
            smaller than the declared universe. *)
        check_constructors_smaller Σ cdecls ind_sort
        × if indices_matter then
            type_local_ctx Σ params ind_indices ind_sort
          else True.

    Record on_ind_body Σ mind mdecl i idecl :=
      { (** The type of the inductive must be an arity, sharing the same params
            as the rest of the block, and maybe having a context of indices. *)
        ind_arity_eq : idecl.(ind_type)
                      = it_mkProd_or_LetIn mdecl.(ind_params)
                                (it_mkProd_or_LetIn idecl.(ind_indices) (tSort idecl.(ind_sort)));

        (** It must be well-typed in the empty context. *)
        onArity : on_type Σ [] idecl.(ind_type);

        (** The sorts of the arguments contexts of each constructor *)
        ind_cunivs : list constructor_univs;

        (** Constructors are well-typed *)
        onConstructors :
          on_constructors Σ mdecl i idecl idecl.(ind_indices) idecl.(ind_ctors) ind_cunivs;

        (** Projections, if any, are well-typed *)
        onProjections :
          match idecl.(ind_projs), idecl.(ind_ctors) return Type with
          | [], _ => True
          | _, [ o ] =>
              on_projections mdecl mind i idecl idecl.(ind_indices) o
          | _, _ => False
          end;

        (** The universes and elimination sorts must be correct w.r.t.
            the universe of the inductive and the universes in its constructors, which
            are declared in [on_constructors]. *)
        ind_sorts :
          check_ind_sorts Σ mdecl.(ind_params) idecl.(ind_kelim)
                          idecl.(ind_indices) ind_cunivs idecl.(ind_sort);

        onIndices :
          (* The inductive type respect the variance annotation on polymorphic universes, if any. *)
          match ind_variance mdecl with
          | Some v => ind_respects_variance Σ mdecl v idecl.(ind_indices)
          | None => True
          end
      }.

    Definition on_variance Σ univs (variances : option (list Variance.t)) :=
      match univs return Type with
      | Monomorphic_ctx => variances = None
      | Polymorphic_ctx auctx =>
        match variances with
        | None => unit
        | Some v =>
          ∑ univs' i i',
            [× (variance_universes univs v = Some (univs', i, i')),
              consistent_instance_ext (Σ, univs') univs i,
              consistent_instance_ext (Σ, univs') univs i' &
              List.length v = #|UContext.instance (AUContext.repr auctx)|]
        end
      end.

    (** We allow empty blocks for simplicity
        (no well-typed reference to them can be made). *)

    Record on_inductive Σ mind mdecl :=
      { onInductives : Alli (on_ind_body Σ mind mdecl) 0 mdecl.(ind_bodies);
        (** We check that the context of parameters is well-formed and that
            the size annotation counts assumptions only (no let-ins). *)
        onParams : on_context Σ mdecl.(ind_params);
        onNpars : context_assumptions mdecl.(ind_params) = mdecl.(ind_npars);
        (** We check that the variance annotations are well-formed: i.e. they
          form a valid universe context. *)
        onVariance : on_variance Σ mdecl.(ind_universes) mdecl.(ind_variance);
      }.

    (** *** Typing of constant declarations *)

    Definition on_constant_decl Σ d :=
      match d.(cst_body) with
      | Some trm => P Σ [] trm (Typ d.(cst_type))
      | None => on_type Σ [] d.(cst_type)
      end.

    Definition on_global_decl Σ kn decl :=
      match decl with
      | ConstantDecl d => on_constant_decl Σ d
      | InductiveDecl inds => on_inductive Σ kn inds
      end.

    (** *** Typing of global environment

        All declarations should be typeable and the global
        set of universe constraints should be consistent. *)

    (** Well-formed global environments have no name clash. *)

    Definition fresh_global (s : kername) (g : global_declarations) : Prop :=
      Forall (fun g => g.1 <> s) g.

    Record on_global_decls_data (univs : ContextSet.t) retro (Σ : global_declarations) (kn : kername) (d : global_decl) :=
        {
          kn_fresh :  fresh_global kn Σ ;
          udecl := universes_decl_of_decl d ;
          on_udecl_udecl : on_udecl univs udecl ;
          on_global_decl_d : on_global_decl (mk_global_env univs Σ retro, udecl) kn d
        }.

    Inductive on_global_decls (univs : ContextSet.t) (retro : Retroknowledge.t): global_declarations -> Type :=
    | globenv_nil : on_global_decls univs retro []
    | globenv_decl Σ kn d :
        on_global_decls univs retro Σ ->
        on_global_decls_data univs retro Σ kn d ->
        on_global_decls univs retro (Σ ,, (kn, d)).

    Derive Signature for on_global_decls.

    Definition on_global_univs (c : ContextSet.t) :=
      let levels := global_levels c in
      let cstrs := ContextSet.constraints c in
      ConstraintSet.For_all (declared_cstr_levels levels) cstrs /\
      LS.For_all (negb ∘ Level.is_var) levels /\
      consistent cstrs.

    Definition on_global_env (g : global_env) : Type :=
      on_global_univs g.(universes) × on_global_decls g.(universes) g.(retroknowledge) g.(declarations).

    Definition on_global_env_ext (Σ : global_env_ext) :=
      on_global_env Σ.1 × on_udecl Σ.(universes) Σ.2.

  End GlobalMaps.

  Arguments cstr_args_length {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments cstr_eq {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_ctype {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_cargs {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_cindices {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_ctype_positive {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.
  Arguments on_ctype_variance {_ Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs}.

  Arguments ind_arity_eq {_ Pcmp P Σ mind mdecl i idecl}.
  Arguments ind_cunivs {_ Pcmp P Σ mind mdecl i idecl}.
  Arguments onArity {_ Pcmp P Σ mind mdecl i idecl}.
  Arguments onConstructors {_ Pcmp P Σ mind mdecl i idecl}.
  Arguments onProjections {_ Pcmp P Σ mind mdecl i idecl}.
  Arguments ind_sorts {_ Pcmp P Σ mind mdecl i idecl}.
  Arguments onIndices {_ Pcmp P Σ mind mdecl i idecl}.

  Arguments onInductives {_ Pcmp P Σ mind mdecl}.
  Arguments onParams {_ Pcmp P Σ mind mdecl}.
  Arguments onNpars {_ Pcmp P Σ mind mdecl}.
  Arguments onVariance {_ Pcmp P Σ mind mdecl}.


  Lemma type_local_ctx_impl (P Q : global_env_ext -> context -> term -> typ_or_sort -> Type) Σ Γ Δ u :
    type_local_ctx P Σ Γ Δ u ->
    (forall Γ t T, P Σ Γ t T -> Q Σ Γ t T) ->
    type_local_ctx Q Σ Γ Δ u.
  Proof.
    intros HP HPQ. revert HP; induction Δ in Γ, HPQ |- *; simpl; auto.
    destruct a as [na [b|] ty]; simpl; auto.
    intros. intuition auto. intuition auto.
  Qed.

  Lemma sorts_local_ctx_impl (P Q : global_env_ext -> context -> term -> typ_or_sort -> Type) Σ Γ Δ u :
    sorts_local_ctx P Σ Γ Δ u ->
    (forall Γ t T, P Σ Γ t T -> Q Σ Γ t T) ->
    sorts_local_ctx Q Σ Γ Δ u.
  Proof.
    intros HP HPQ. revert HP; induction Δ in Γ, HPQ, u |- *; simpl; auto.
    destruct a as [na [b|] ty]; simpl; auto.
    intros. intuition auto. intuition auto.
    destruct u; auto. intuition eauto.
  Qed.

  Lemma on_global_env_impl {cf : checker_flags} Pcmp P Q :
    (forall Σ Γ t T,
        on_global_env Pcmp P Σ.1 ->
        on_global_env Pcmp Q Σ.1 ->
        P Σ Γ t T -> Q Σ Γ t T) ->
    forall Σ, on_global_env Pcmp P Σ -> on_global_env Pcmp Q Σ.
  Proof.
    intros X Σ [cu IH]. split; auto.
    revert cu IH; generalize (universes Σ) as univs, (retroknowledge Σ) as retro, (declarations Σ). clear Σ.
    induction g; intros; auto. constructor; auto.
    depelim IH. specialize (IHg cu IH). constructor; auto.
    pose proof (globenv_decl _ _ _ _ _ _ _ IH o).
    destruct o. constructor; auto.
    assert (X' := fun Γ t T => X ({| universes := univs; declarations := _ |}, udecl0) Γ t T
      (cu, IH) (cu, IHg)); clear X.
    rename X' into X.
    clear IH IHg. destruct d; simpl.
    - destruct c; simpl. destruct cst_body0; cbn in *; now eapply X.
    - destruct on_global_decl_d0 as [onI onP onNP].
      constructor; auto.
      -- eapply Alli_impl; tea. intros.
        refine {| ind_arity_eq := X1.(ind_arity_eq);
                  ind_cunivs := X1.(ind_cunivs) |}.
        --- apply onArity in X1. unfold on_type in *; simpl in *.
            now eapply X.
        --- pose proof X1.(onConstructors) as X11. red in X11.
            eapply All2_impl; eauto.
            simpl. intros. destruct X2 as [? ? ? ?]; unshelve econstructor; eauto.
            * apply X; eauto.
            * clear -X0 X on_cargs0. revert on_cargs0.
              generalize (cstr_args x0).
              induction c in y |- *; destruct y; simpl; auto;
                destruct a as [na [b|] ty]; simpl in *; auto;
            split; intuition eauto.
            * clear -X0 X on_cindices0.
              revert on_cindices0.
              generalize (List.rev (lift_context #|cstr_args x0| 0 (ind_indices x))).
              generalize (cstr_indices x0).
              induction 1; simpl; constructor; auto.
        --- simpl; intros. pose (onProjections X1) as X2. simpl in *; auto.
        --- destruct X1. simpl. unfold check_ind_sorts in *.
            destruct Universe.is_prop; auto.
            destruct Universe.is_sprop; auto.
            split.
            * apply ind_sorts0.
            * destruct indices_matter; auto.
              eapply type_local_ctx_impl; eauto.
              eapply ind_sorts0.
        --- eapply X1.(onIndices).
      -- red in onP. red.
        eapply All_local_env_impl; tea.
  Qed.

End GlobalMaps.






  #[export] Instance declared_inductive {Σ ind mdecl decl} : ground_quotable (declared_inductive Σ ind mdecl decl) := _.
  try exact _.

(* Distributed under the terms of the MIT license. *)
From Coq Require Import ssreflect ssrbool.
From MetaCoq.Template Require Import config utils BasicAst Universes Environment Primitive.
From Equations Require Import Equations.

Module Lookup (T : Term) (E : EnvironmentSig T).

  Import T E.

  (** ** Environment lookup *)

  Definition declared_constant (Σ : global_env) (id : kername) decl : Prop :=
    lookup_env Σ id = Some (ConstantDecl decl).

  Definition declared_minductive Σ mind decl :=
    lookup_env Σ mind = Some (InductiveDecl decl).

  Definition declared_inductive Σ ind mdecl decl :=
    declared_minductive Σ (inductive_mind ind) mdecl /\
    List.nth_error mdecl.(ind_bodies) (inductive_ind ind) = Some decl.

  Definition declared_constructor Σ cstr mdecl idecl cdecl : Prop :=
    declared_inductive Σ (fst cstr) mdecl idecl /\
    List.nth_error idecl.(ind_ctors) (snd cstr) = Some cdecl.

  Definition declared_projection Σ (proj : projection) mdecl idecl cdecl pdecl
  : Prop :=
    declared_constructor Σ (proj.(proj_ind), 0) mdecl idecl cdecl /\
    List.nth_error idecl.(ind_projs) proj.(proj_arg) = Some pdecl /\
    mdecl.(ind_npars) = proj.(proj_npars).


End Lookup.



Module Type GlobalMapsSig (T: Term) (E: EnvironmentSig T) (TU : TermUtils T E) (ET: EnvTypingSig T E TU) (C: ConversionSig T E TU ET) (L: LookupSig T E).
  Include GlobalMaps T E TU ET C L.
End GlobalMapsSig.

Module Type ConversionParSig (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU).

  Import T E TU ET.

  Parameter Inline cumul_gen : forall {cf : checker_flags}, global_env_ext -> context -> conv_pb -> term -> term -> Type.

End ConversionParSig.

Module Type Typing (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E) (ET : EnvTypingSig T E TU)
  (CT : ConversionSig T E TU ET) (CS : ConversionParSig T E TU ET).

  Import T E TU ET CT CS.

  Parameter Inline typing : forall `{checker_flags}, global_env_ext -> context -> term -> term -> Type.

  Notation " Σ ;;; Γ |- t : T " :=
    (typing Σ Γ t T) (at level 50, Γ, t, T at next level) : type_scope.

  Notation wf_local Σ Γ := (All_local_env (lift_typing Σ) Γ).

End Typing.

Module DeclarationTyping (T : Term) (E : EnvironmentSig T) (TU : TermUtils T E)
  (ET : EnvTypingSig T E TU) (CT : ConversionSig T E TU ET)
  (CS : ConversionParSig T E TU ET) (Ty : Typing T E TU ET CT CS)
  (L : LookupSig T E) (GM : GlobalMapsSig T E TU ET CT L).

  Import T E L TU ET CT GM CS Ty.

  Definition isType `{checker_flags} (Σ : global_env_ext) (Γ : context) (t : term) :=
    infer_sort (typing_sort typing) Σ Γ t.

  (** This predicate enforces that there exists typing derivations for every typable term in env. *)

  Definition Forall_decls_typing `{checker_flags}
            (P : global_env_ext -> context -> term -> term -> Type)
    := on_global_env cumul_gen (lift_typing P).

  (** *** Typing of local environments *)

  Definition type_local_decl `{checker_flags} Σ Γ d :=
    match d.(decl_body) with
    | None => isType Σ Γ d.(decl_type)
    | Some body => Σ ;;; Γ |- body : d.(decl_type)
    end.

  (** ** Induction principle for typing up-to a global environment *)

  Lemma refine_type `{checker_flags} Σ Γ t T U : Σ ;;; Γ |- t : T -> T = U -> Σ ;;; Γ |- t : U.
  Proof. now intros Ht ->. Qed.

  Definition wf_local_rel `{checker_flags} Σ := All_local_rel (lift_typing typing Σ).

  (** Functoriality of global environment typing derivations + folding of the well-formed
    environment assumption. *)
  Lemma on_wf_global_env_impl `{checker_flags} {Σ : global_env} {wfΣ : on_global_env cumul_gen (lift_typing typing) Σ} P Q :
    (forall Σ Γ t T, on_global_env cumul_gen (lift_typing typing) Σ.1 ->
        on_global_env cumul_gen P Σ.1 ->
        on_global_env cumul_gen Q Σ.1 ->
        P Σ Γ t T -> Q Σ Γ t T) ->
    on_global_env cumul_gen P Σ -> on_global_env cumul_gen Q Σ.
  Proof.
    unfold on_global_env in *.
    intros X [hu X0]. split; auto.
    simpl in *. destruct wfΣ as [cu wfΣ]. revert cu wfΣ.
    revert X0. generalize (universes Σ) as univs, (retroknowledge Σ) as retro, (declarations Σ). clear hu Σ.
    induction 1; constructor; try destruct o; try constructor; auto.
    { depelim wfΣ. eauto. }
    depelim wfΣ. specialize (IHX0 cu wfΣ). destruct o.
    assert (X' := fun Γ t T => X ({| universes := univs; declarations := Σ |}, udecl0) Γ t T
      (cu, wfΣ) (cu, X0) (cu, IHX0)); clear X.
    rename X' into X.
    clear IHX0. destruct d; simpl.
    - destruct c; simpl. destruct cst_body0; simpl in *; now eapply X.
    - simpl in *. destruct on_global_decl_d0 as [onI onP onNP].
      constructor; auto.
      -- eapply Alli_impl; tea. intros.
        refine {| ind_arity_eq := X1.(ind_arity_eq);
                  ind_cunivs := X1.(ind_cunivs) |}.
        --- apply onArity in X1. unfold on_type in *; simpl in *.
            now eapply X.
        --- pose proof X1.(onConstructors) as X11. red in X11.
            eapply All2_impl; eauto.
            simpl. intros. destruct X2 as [? ? ? ?]; unshelve econstructor; eauto.
            * apply X; eauto.
            * clear -X0 X on_cargs0. revert on_cargs0.
              generalize (cstr_args x0).
              induction c in y |- *; destruct y; simpl; auto;
                destruct a as [na [b|] ty]; simpl in *; auto;
            split; intuition eauto.
            * clear -X0 X on_cindices0.
              revert on_cindices0.
              generalize (List.rev (lift_context #|cstr_args x0| 0 (ind_indices x))).
              generalize (cstr_indices x0).
              induction 1; simpl; constructor; auto.
        --- simpl; intros. pose (onProjections X1). simpl in *; auto.
        --- destruct X1. simpl. unfold check_ind_sorts in *.
            destruct Universe.is_prop; auto.
            destruct Universe.is_sprop; auto.
            split.
            * apply ind_sorts0.
            * destruct indices_matter; auto.
              eapply type_local_ctx_impl; eauto.
              eapply ind_sorts0.
        --- eapply X1.(onIndices).
      -- red in onP. red.
        eapply All_local_env_impl; tea.
  Qed.

End DeclarationTyping.
