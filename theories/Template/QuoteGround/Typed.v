From MetaCoq.Template Require Import Ast utils All.
From MetaCoq.Lob.Template Require Import
     QuoteGround.Init QuoteGround.Init.Typing
     QuoteGround.Ast QuoteGround.Typing
     QuoteGround.Ast.Typing QuoteGround.Typing.Typing
     Typed
.

#[export] Instance qenv : quotation_of env := _.
#[export] Instance qcontext : quotation_of (@context) := _.
#[export] Instance qsort : quotation_of (@sort) := _.
#[export] Instance qtype : quotation_of (@type) := _.
#[export] Instance qterm : quotation_of (@term) := _.

#[export] Instance quote_env : ground_quotable env := ltac:(destruct 1; exact _).
#[export] Instance quote_context {Σ} : ground_quotable (@context Σ) := ltac:(destruct 1; exact _).
#[export] Instance quote_sort {Σ} : ground_quotable (@sort Σ) := ltac:(destruct 1; exact _).
#[export] Instance quote_type {Σ Γ s} : ground_quotable (@type Σ Γ s) := ltac:(destruct 1; exact _).
#[export] Instance quote_term {Σ Γ s T} : ground_quotable (@term Σ Γ s T) := ltac:(destruct 1; exact _).

#[export] Instance qenv_well_typed : quotation_of_well_typed_using [env] env.
Proof. Admitted.
#[export] Instance qcontext_well_typed : quotation_of_well_typed_using [@context] (@context).
Proof. Admitted.
#[export] Instance qsort_well_typed : quotation_of_well_typed_using [@sort] (@sort).
Proof. Admitted.
#[export] Instance qtype_well_typed : quotation_of_well_typed_using [@type] (@type).
Proof. Admitted.
#[export] Instance qterm_well_typed : quotation_of_well_typed_using [@term] (@term).
Proof. Admitted.

#[export] Instance quote_env_well_typed : ground_quotable_well_typed_using [env] env.
Admitted.
#[export] Instance quote_context_well_typed {Σ} : ground_quotable_well_typed_using [@context] (@context Σ).
Proof. Admitted.
#[export] Instance quote_sort_well_typed {Σ} : ground_quotable_well_typed_using [@sort] (@sort Σ).
Proof. Admitted.
#[export] Instance quote_type_well_typed {Σ Γ s} : ground_quotable_well_typed_using [@type] (@type Σ Γ s).
Proof. Admitted.
#[export] Instance quote_term_well_typed {Σ Γ s T} : ground_quotable_well_typed_using [@term] (@term Σ Γ s T).
Proof. Admitted.
