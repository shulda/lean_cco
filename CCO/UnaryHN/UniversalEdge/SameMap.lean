import CCO.UnaryHN.UniversalEdge.Basic

/-! Completed-map rigidity embeds the OLD reduct of each actual expanded
irreducible member. Its old reduct need not itself be irreducible. -/

universe u v
namespace CCO.UnaryHN.Native

open StructuralRamsey
open StructuralRamsey.Structure

variable {L : Language.{u}} {K : Class.{u,v} L}
variable {V W : Type v} {C : Structure (edgeLanguage L) V}
variable {H : Structure L W} {f : V → W}

/-- C05/C06: use rigidity on the WHOLE actual completed old reduct. -/
theorem completed_piece_embedding
    (hRig : CompletedMapRigidity K)
    (hLocal : IrreduciblesIn (ExpandedClass K) C) (hH : K H)
    (hf : HE (edgeReduct C) H f)
    {X : Type v} (E : Structure (edgeLanguage L) X)
    (hE : E.Irreducible) (e : Embedding E C) :
    ∃ g : Embedding E (expandEdge H), ∀ x, g x = f (e x) := by
  have hMember : ExpandedClass K E := hLocal E hE e
  have hOld : HE (edgeReduct E) H (f ∘ e) :=
    hf.comp (reductEmbedding e).isEHNHomomorphismEmbedding
  obtain ⟨g, hg⟩ :=
    hRig (edgeReduct E) H hMember.reduct_mem hH (f ∘ e) hOld
  refine ⟨{ toFun := g, injective := g.injective,
             map_rel_iff := ?_, map_func := g.map_func }, hg⟩
  intro R xs
  cases R with
  | inl R => exact g.map_rel_iff R xs
  | inr r =>
    change Fin 2 → X at xs
    change g (xs 0) ≠ g (xs 1) ↔ E.rel (.inr r) xs
    cases r
    rw [hMember.edge_iff xs]
    exact g.injective.ne_iff

/-- C07: an actual loop's generated support would be a completed member
whose universal edge is irreflexive. No old map or rigidity is needed. -/
theorem displayed_edge_no_loop
    (hLocal : IrreduciblesIn (ExpandedClass K) C) (x : V) :
    ¬ C.rel (.inr ()) (fun _ => x) := by
  intro hLoop
  let xs : Fin 2 → V := fun _ => x
  let S := C.functionClosure (Set.range xs)
  have hS := C.functionClosure_isClosed (Set.range xs)
  let D := C.induce S hS
  have hD : D.Irreducible := relation_tuple_hull_irreducible C (.inr ()) xs hLoop
  have hMember : ExpandedClass K D := hLocal D hD (inclusion C S hS)
  let ys : Fin 2 → S := fun j =>
    ⟨xs j, C.subset_functionClosure (Set.range xs) ⟨j, rfl⟩⟩
  have hRel : D.rel (.inr ()) ys := hLoop
  have hNe := (hMember.edge_iff ys).mp hRel
  exact hNe (Subtype.ext rfl)

/-- C08/C09: the GIVEN vertex function is the expanded HE. There is no
replacement completion map and no global injection conclusion. -/
theorem same_map_universal_edge
    (hRig : CompletedMapRigidity K)
    (hLocal : IrreduciblesIn (ExpandedClass K) C) (hH : K H)
    (hf : HE (edgeReduct C) H f) : HE C (expandEdge H) f := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro R xs hRel
    cases R with
    | inl R => exact hf.1.1 R xs hRel
    | inr r =>
      change Fin 2 → V at xs
      let S := C.functionClosure (Set.range xs)
      have hS := C.functionClosure_isClosed (Set.range xs)
      let D := C.induce S hS
      have hD : D.Irreducible := relation_tuple_hull_irreducible C (.inr r) xs hRel
      obtain ⟨g, hg⟩ := completed_piece_embedding hRig hLocal hH hf D hD
        (inclusion C S hS)
      let ys : Fin 2 → S := fun j =>
        ⟨xs j, C.subset_functionClosure (Set.range xs) ⟨j, rfl⟩⟩
      have hRelD : D.rel (.inr r) ys := hRel
      have hImage := (g.map_rel_iff (.inr r) ys).mpr hRelD
      have hArgs : g ∘ ys = f ∘ xs := by
        funext j
        exact hg (ys j)
      exact Eq.mp (congrArg ((expandEdge H).rel (.inr r)) hArgs) hImage
  · intro F xs y hy
    exact hf.1.2 F xs y hy
  · intro X E hE e
    exact completed_piece_embedding hRig hLocal hH hf E hE e

end CCO.UnaryHN.Native
