From MetaCoq.Lob.Util Require Import Structures.Orders.
From MetaCoq.Template.utils Require Import ReflectEq.

Module Type HasReflectEq (T : Typ).
  #[export] Declare Instance reflectEq : ReflectEq T.t.
End HasReflectEq.

Module HasEqDec2Reflect (E:UsualEq)(F:HasEqDec E) <: HasReflectEq E.
  #[export,program] Instance reflectEq : ReflectEq E.t := {
    eqb x y := if F.eq_dec x y then true else false
  }.
  Next Obligation.
    destruct F.eq_dec; constructor; assumption.
  Defined.
End HasEqDec2Reflect.
