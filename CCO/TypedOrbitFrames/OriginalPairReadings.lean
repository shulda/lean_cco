import CCO.TypedOrbitFrames.ChordCycleStrongInduction
import CCO.PairHomogeneity

/-!
# B053 C04: old typed edge readings under endpoint transport and reversal

A true old typed partial diagram contains Option old-colours, with
NONE exactly for a missing specified edge. This module only reasons
about a pair with a proof of DISTINCT formal vertices. The source
edge_reverse law gives the complete converse reading, including
the actual dependent old atom type.

This separates the exact two-short-cycle closing-chord reading
from generic graph adjacency, invented identity atoms or
a hidden quotient-age automorphism.
-/

namespace CCO.TypedOrbitFrames

universe u v w z
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z}

/-- Actual complete typed old pair-reading in a partial
source diagram, retaining both sort tags and optional
original atomic colour. -/
def originalTypedPairReading
    (D : PartialDiagram S V) {x y : V} (h : x ≠ y) :
    (Σ i : ι, Σ j : ι, Option (S.Atom i j)) :=
  ⟨D.vertexSort x,D.vertexSort y,D.edge x y h⟩

/-- Converse of an entire optional typed old pair
label: swap original sorts and use the ACTUAL
source converse operation, not a synthetic label. -/
def originalTypedPairConverse
    (q : Σ i : ι, Σ j : ι, Option (S.Atom i j)) :
    (Σ i : ι, Σ j : ι, Option (S.Atom i j)) :=
  ⟨q.2.1, q.1, q.2.2.map (fun a => S.conv a)⟩

/-- The full typed pair-reading is invariant under
equality of BOTH actual formal source endpoints.
The dependent edge proofs are transported together. -/
theorem original_typed_pair_reading_endpoint_congr
    (D : PartialDiagram S V)
    {x x' y y' : V} (hx : x = x') (hy : y = y')
    (hne : x ≠ y) (hne' : x' ≠ y') :
    originalTypedPairReading S D hne =
      originalTypedPairReading S D hne' := by
  cases hx
  cases hy
  rfl

/-- Source PartialDiagram.edge_reverse yields the actual
converse of the ENTIRE typed old pair colour. This
holds even for omitted (none) edges, not just
positive diversity atoms. -/
theorem original_typed_pair_reading_converse
    (D : PartialDiagram S V) {x y : V} (h : x ≠ y) :
    originalTypedPairReading S D h =
      originalTypedPairConverse S
        (originalTypedPairReading S D h.symm) := by
  have hc : D.edge x y h =
      (D.edge y x h.symm).map (fun a => S.conv a) := by
    cases hyx : D.edge y x h.symm with
    | none =>
        cases hxy : D.edge x y h with
        | none => simp [hyx]
        | some a =>
            have hbad := (D.edge_reverse x y h a).mp hxy
            rw [hyx] at hbad
            cases hbad
    | some a =>
        simpa only [hyx, Option.map_some] using
          (D.edge_reverse y x h.symm a).mp hyx
  change (⟨D.vertexSort x,D.vertexSort y,D.edge x y h⟩ :
      Σ i : ι, Σ j : ι, Option (S.Atom i j)) =
    ⟨D.vertexSort x,D.vertexSort y,
      (D.edge y x h.symm).map (fun a => S.conv a)⟩
  rw [hc]

/-- Converse of the full ACTUAL real pair reading,
including the true optional old diagonal. -/
theorem original_actual_tagged_colour_converse
    (x y : Sigma X) :
    taggedColour S x y =
      originalTypedPairConverse S (taggedColour S y x) := by
  cases x with
  | mk i x =>
    cases y with
    | mk j y =>
      change S.colour x y =
        (S.colour y x).map (fun a => S.conv a)
      exact S.colour_reverse y x

end CCO.TypedOrbitFrames
