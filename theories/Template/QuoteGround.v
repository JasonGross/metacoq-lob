From MetaCoq.Template Require Import Ast utils All.
From MetaCoq.Lob.Template Require Import
     QuoteGround.Init QuoteGround.Init.Typing
     QuoteGround.Ast QuoteGround.Typing
     QuoteGround.Ast.Typing QuoteGround.Typing.Typing
     QuoteGround.Typed
.
From MetaCoq.Lob Require Import Template.Typed.

(* Does the env contain everything necessary for quoting? *)
Axiom env_can_quote : Typed.env -> bool.
Record env := { env_ :> Typed.env ; env_good : env_can_quote env_ }.
Existing Class env.
#[export] Existing Instance env_.

Local Ltac use_well_typed _ :=
  let qwt := lazymatch goal with
             | [ |- _ ;;; _ |- @quote_ground ?T ?quoteT ?t : _ ]
               => constr:(ltac:(notypeclasses refine (_ : @ground_quotable_well_typed _ T _ quoteT); typeclasses eauto))
             | [ |- _ ;;; _ |- ?q : _ ]
               => constr:(ltac:(notypeclasses refine (_ : @quotation_of_well_typed _ _ _ _ q); typeclasses eauto))
             end in
  first [ eapply qwt
        | eapply type_Conv; [ eapply qwt | repeat exactly_once constructor .. ] ];
  try apply context_wf_local; auto; try exact eq_refl;
  cbv [config.global_env_ext_constraint]; cbn [fold_right map].

(* For now, let's assume a rigid environment tiled at all levels.  TODO: Think about weakening *)
(*
Axiom env_subset : env -> env -> bool.
(* copy ⊂_cs level *)
Infix "⊂_e" := env_subset (at level 30).
 *)
Axiom proof_admitted : False.
Section in_env.
  Context {Σ : env}.
  (* the universe that can contain all the quoted things *)
  Definition u : sort.
  Proof using Σ.
    unshelve econstructor.
    { refine (Universe.lType _).
      abstract case proof_admitted. }
    { abstract (case proof_admitted) using wf_u. }
  Defined.

  #[local] Hint Resolve wf_u : core.

  (* We assume we're quoting to a fixed context *)
  Section in_context.
    Context {Γ : context}.
    Local Ltac do_admit _ :=
      let G := lazymatch goal with |- ?G => G end in
      try (assert_fails has_evar G;
           lazymatch G with context[Σ] => idtac end;
           lazymatch G with
           | is_true _ => idtac
           | compare_universe _ _ _ _ => idtac
           end;
           abstract case proof_admitted).
    Local Ltac use_well_typed_then_admit _ :=
      use_well_typed ();
      do_admit ().
    Local Ltac misc _ :=
      lazymatch goal with
      | [ |- _ = false ] => vm_compute; reflexivity
      | [ |- _ <> _ ] => congruence
      | _ => idtac
      end.

    #[local] Obligation Tactic := intros; try use_well_typed_then_admit ().

    #[program] Definition qenv : type Γ u
      := {| type_ := Typed.qenv |}.
    #[program] Definition qΣ : term (Γ:=Γ) qenv
      := {| term_ := quote_ground Σ.(env_) |}.
    #[program] Definition qcontext : type Γ u
      := {| type_ := _ : quotation_of (@Typed.context Σ) |}.
    Next Obligation.
      econstructor; try use_well_typed_then_admit (); misc ().
      repeat exactly_once econstructor; try use_well_typed_then_admit (); misc ().
      econstructor.
      try use_well_typed_then_admit ().
      2: econstructor.
      all: repeat repeat exactly_once econstructor; do_admit ().
      econstructor.
      all: repeat repeat exactly_once constructor; try apply context_wf_local; auto.
      hnf; econstructor.
      use_well_typed_then_admit ().
      abstract case proof_admitted.
    Qed.
    #[program] Definition qsort : type Γ u
      := {| type_ := _ : quotation_of (@Typed.sort Σ) |}.
    Next Obligation.
      econstructor; try use_well_typed_then_admit (); misc ().
      repeat exactly_once econstructor; try use_well_typed_then_admit (); misc ().
      econstructor.
      try use_well_typed_then_admit ().
      2: econstructor.
      all: repeat repeat exactly_once econstructor; do_admit ().
      econstructor.
      all: repeat repeat exactly_once constructor; try apply context_wf_local; auto.
      hnf; econstructor.
      use_well_typed_then_admit ().
      abstract case proof_admitted.
    Admitted.
    #[program] Definition qtype (qΓ' : term qcontext) (qs : term qsort) : type Γ u
      := {| type_ := tApp <% @Typed.type %> [qΣ:Ast.term; qΓ':Ast.term; qs:Ast.term] |}.
    Next Obligation.
      econstructor; try use_well_typed_then_admit (); misc ().
      econstructor; try apply qΣ.
      all: econstructor.
      all: do 4 lazymatch goal with
                | [ |- _ ;;; _ |- (@type_ _ _ _ ?q) : _ ] => apply q
                | [ |- _ ;;; _ |- (@term_ _ _ _ _ ?q) : _ ] => apply q
                | [ |- _ ;;; _ |- tProd _ _ _ : tSort _ ] => econstructor
                | [ |- _ ;;; _ |- tApp _ _ : tSort _ ] => econstructor
                | [ |- _ ;;; _ |- tProd _ _ _ <= tProd _ _ _ ] => econstructor
                | _ => try exactly_once econstructor; cbn [subst1 subst0]
                end.
      all: try misc ().
      all: try exactly_once econstructor.
      all: try exactly_once econstructor.
      all: try exactly_once econstructor.
      all: try exactly_once econstructor.
      all: try exactly_once econstructor.
      all: try exactly_once econstructor.
      all: try exactly_once econstructor.
    Abort.
    (*
      all: try exactly_once econstructor.
      all: try exactly_once econstructor.
      all: match goal with
      end.
goal 7 (ID 796) is:
 Σ;;; Γ |- tProd ?na' (subst0 [qΣ] ?a') (subst [qΣ] 1 ?b') <= tProd ?na qcontext ?B
goal 8 (ID 807) is:
 Σ;;; Γ |- tProd ?na0 qsort ?B0 : tSort ?s0
goal 9 (ID 813) is:
 Σ;;; Γ |- ?B {0 := qΓ'} <= tProd ?na0 qsort ?B0

      7: { cbn [subst1 subst0]. Set Printing All. constructor.
      all:
      all: lazymatch goal with
           | [ |- _ ;;; _ |- (@type_ _ _ _ ?q) : _ ] => apply q
           | [ |- _ ;;; _ |- (@term_ _ _ _ _ ?q) : _ ] => apply q
           | _ => idtac
           end.

      all: lazymatch goal with
           | [ |- _ ;;; _ |- (@type_ _ _ _ ?q) : _ ] => apply q
           | [ |- _ ;;; _ |- (@term_ _ _ _ _ ?q) : _ ] => apply q
           | [ |- _ ;;; _ |- (@sort_ _ _ _ _ ?q) : _ ] => apply q
           | _ => idtac
           end.
      eapply qenv.

      all: repeat exactly_once econstructor.
      econstructor.
      try use_well_typed_then_admit ().
      2: econstructor.
      all: repeat repeat exactly_once econstructor; do_admit ().
      econstructor.
      all: repeat repeat exactly_once constructor; try apply context_wf_local; auto.
      hnf; econstructor.
      use_well_typed_then_admit ().
      abstract case proof_admitted.
    Admitted.
    #[program] Definition qterm {qΓ' : term qcontext} {qs : term qsort} {qT : term (qtype qΓ' qs)} : type Γ u
      := {| type_ := tApp <% @Typed.term %> [qΣ:Ast.term; qΓ':Ast.term; qs:Ast.term; qT:Ast.term] |}.
    Next Obligation.
    Admitted.

    Definition quote_context (Γ' : context) : term qcontext.

               Definition quote_term {s : sort} {T : type Γ s} (t : term T) : Type.
  refine (@term Σ _ _ _).
  :=

Definition quote_env : env
Local Set Primitive Projections.
Record env := { env_ :> global_env_ext ; checker_flags_ :> config.checker_flags  }.
Existing Class env.
#[export] Existing Instance checker_flags_.
Record context {Σ : env} := { context_ :> Ast.Env.context }.
Record sort {Σ : env} := { sort_ :> Universe.t }.
Record type {Σ : env} (Γ : context) (s : sort) :=
  { type_ :> Ast.term ; type_well_typed : Σ ;;; Γ |- type_ : tSort s }.
Record term {s : sort} (T : type Γ s) :=
  { term_ :> Ast.term ; term_well_typed : Σ ;;; Γ |- term_ : T }.

Definition quote
*)
