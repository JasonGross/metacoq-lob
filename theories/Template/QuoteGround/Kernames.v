From MetaCoq.Lob.Template.QuoteGround Require Export Coq.Init Coq.MSets Coq.FSets bytestring.
From MetaCoq.Template Require Import Kernames.

#[export] Instance quote_modpath : ground_quotable modpath := ltac:(induction 1; exact _).

Module QuoteKernameSet := QuoteMSetAVL Kername KernameSet.
Export QuoteKernameSet.Instances.
Module QuoteKernameMap := QuoteFMapAVL Kername.OT KernameMap.
Export QuoteKernameMap.Instances.

#[export] Instance quote_inductive : ground_quotable inductive := ltac:(destruct 1; exact _).
#[export] Instance quote_projection : ground_quotable projection := ltac:(destruct 1; exact _).
#[export] Instance quote_global_reference : ground_quotable global_reference := ltac:(destruct 1; exact _).
