Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.
Require Coq.Structures.OrderedType.
Import Coq.Structures.OrderedType.
Export Coq.Structures.Orders.

Module Type MiniOrderedType := OrderedType.MiniOrderedType.
Module Type OrderedTypeOrig := OrderedType.OrderedType.
