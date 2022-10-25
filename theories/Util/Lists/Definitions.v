Require Import Coq.Lists.List.

Module List.
  Definition enumerate {A} (ls : list A) : list (nat * A)
    := combine (seq 0 (length ls)) ls.

  Definition find_index {A} (f : A -> bool) (xs : list A) : option nat
    := option_map (@fst _ _) (find (fun v => f (snd v)) (enumerate xs)).
End List.
