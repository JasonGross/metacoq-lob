From MetaCoq.Lob Require Import Util.Lists.Definitions.
From MetaCoq.Template Require Import Ast utils.

(** [closenl [x₁;...;xₙ] k c] abstracts over variables [x₁;...;xₙ] and replaces them with
    [Rel(k); ...; Rel(k+n-1)] in [c]. If two names are identical, the one of least index is kept. *)
Definition closenl (ids : list ident) : forall (k : nat) (t : term), term
  := fix closenl (k : nat) (t : term) : term
    := match t with
       | tRel _
       | tSort _
       | tConstruct _ _ _
       | tInt _
       | tFloat _
       | tConst _ _
       | tInd _ _
         => t
       | tVar id
         => match List.find_index (String.eqb id) ids with
            | Some n => tRel (n + k)
            | None => t
            end
       | tEvar ev args => tEvar ev (List.map (closenl k) args)
       | tLambda na T M => tLambda na (closenl k T) (closenl (S k) M)
       | tApp u v => mkApps (closenl k u) (List.map (closenl k) v)
       | tProd na A B => tProd na (closenl k A) (closenl (S k) B)
       | tCast c kind ty => tCast (closenl k c) kind (closenl k ty)
       | tLetIn na b ty b' => tLetIn na (closenl k b) (closenl k ty) (closenl (S k) b')
       | tProj p c => tProj p (closenl k c)
       | tFix mfix idx =>
           let k' := List.length mfix + k in
           let mfix' := List.map (map_def (closenl k) (closenl k')) mfix in
           tFix mfix' idx
       | tCoFix mfix idx =>
           let k' := List.length mfix + k in
           let mfix' := List.map (map_def (closenl k) (closenl k')) mfix in
           tCoFix mfix' idx
       | tCase ind p c brs =>
           let k' := List.length (pcontext p) + k in
           let p' := map_predicate id (closenl k) (closenl k') p in
           let brs' := map_branches_k (closenl) k brs in
           tCase ind p' (closenl k c) brs'
       end.
