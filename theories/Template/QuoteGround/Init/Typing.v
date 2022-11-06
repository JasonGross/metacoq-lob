From MetaCoq.Template Require Import MonadBasicAst MonadAst All utils.
From MetaCoq.Template Require Import Typing utils.bytestring TermEquality ReflectAst Ast Reflect.
From MetaCoq.Lob.Template Require Export QuoteGround.Init.
Export utils.bytestring.
Require Import Coq.Lists.List.
Import ListNotations.

Local Set Primitive Projections.
Local Open Scope bs.
Import MCMonadNotation.

Module config.
  Class typing_restriction
    := { checker_flags_constraint : config.checker_flags -> bool
       ; global_env_ext_constraint : global_env_ext -> bool }.
End config.

Polymorphic Class quotation_of_well_typed {Pcf : config.typing_restriction} {T} (t : T) {qT : quotation_of T} {qt : quotation_of t} := typing_quoted_term_of : forall cf Σ Γ, config.checker_flags_constraint cf -> config.global_env_ext_constraint Σ -> wf_local Σ Γ -> Σ ;;; Γ |- qt : qT.
Polymorphic Class ground_quotable_well_typed {Pcf : config.typing_restriction} T {qT : quotation_of T} {quoteT : ground_quotable T} := typing_quote_ground : forall t : T, quotation_of_well_typed t.

Inductive dynlist := dnil | dcons {T} (t : T) (tl : dynlist).
Declare Scope dynlist_scope.
Delimit Scope dynlist_scope with dynlist.
Bind Scope dynlist_scope with dynlist.
Infix "::" := dcons : dynlist_scope.
Notation "[ ]" := dnil : dynlist_scope.
Notation "[ x ]" := (dcons x dnil) : dynlist_scope.
Notation "[ x ; y ; .. ; z ]" :=  (dcons x (dcons y .. (dcons z dnil) ..)) : dynlist_scope.

Fixpoint quote_dynlist (d : dynlist) : TemplateMonad (list term)
  := match d with
     | dnil => ret []
     | dcons _ t rest => qt <- tmQuote t;; qts <- quote_dynlist rest;; ret (qt :: qts)
     end.

Definition constraint_for_globals (globals : dynlist) : TemplateMonad (global_env_ext -> bool)
  := qts <- quote_dynlist globals;;
     inds <- monad_map (fun qt => match qt with
                                  | tInd {| inductive_mind := mind |} _
                                    => ind <- tmQuoteInductive mind;;
                                       (*tmPrint ind;;*)
                                       ret (mind, ind)
                                  | _ => tmPrint ("ensure present not inductive"%bs, qt);; tmFail "ensure present not inductive"%bs
                                  end) qts;;
     ret (fun Σ : global_env_ext
          => List.fold_right andb true (List.map (fun '(mind, ind) => lookup_env Σ.1 mind == Some (InductiveDecl ind)) inds)).

Notation ground_quotable_well_typed_using ls T
  := (match ls%dynlist, T return _ with
      | globals, T'
        => ltac:(let T' := (eval cbv delta [T'] in T') in
                 run_template_program
                   (constraint_for_globals globals)
                   (fun c => refine (@ground_quotable_well_typed
                                       {| config.checker_flags_constraint := _.(config.checker_flags_constraint)
                                       ; config.global_env_ext_constraint := c |}
                                       T' _ _)))
      end)
       (only parsing).
Notation quotation_of_well_typed_using ls t
  := (match ls%dynlist, t return _ with
      | globals, t'
        => ltac:(let t' := (eval cbv delta [t'] in t') in
                 run_template_program
                   (constraint_for_globals globals)
                   (fun c => refine (@quotation_of_well_typed
                                       {| config.checker_flags_constraint := _.(config.checker_flags_constraint)
                                       ; config.global_env_ext_constraint := c |}
                                       _ t' _ _)))
      end)
       (only parsing).

Module Export Instances.
  #[export] Instance default_typing_restriction : config.typing_restriction | 1000
    := {| config.checker_flags_constraint cf := true
       ; config.global_env_ext_constraint Σ := true |}.
  #[export] Existing Instance typing_quote_ground.
End Instances.
