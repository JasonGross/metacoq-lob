Reserved Notation "'subst_let' x := y 'in' z"
         (at level 200, z at level 200, format "'subst_let'  x  :=  y  'in' '//' z").

Notation "'subst_let' x := y 'in' z" := (match y return _ with x => z end) (only parsing).
