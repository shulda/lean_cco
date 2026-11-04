import CCO.TypedOrbitFrames.CompleteBaseChords
import CCO.Finite

/-!
# B053 D01 / T01: the actual old typed partial-diagram specified graph

Here the specified graph is derived LITERALLY from
CCO.PartialDiagram.edge. An edge exists exactly when the partial
diagram specifies a genuine old diversity atom of the appropriate
ordered pair of named real sorts. Missing clone-clone edges are not
declared old atoms and do not force vertex inequality.

The source11 complete-base/all-spokes hypothesis is quantified
over every vertex touching the old base. The graph-level
distance-two chord theorem is instantiated on the resulting REAL
typed specified-edge graph. This does not assume that compatible
short cycles glue: old SAP and old homogeneity are required
separately for that genuine next step of the source proof.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Sparse

universe u v w z t

variable {ι : Type u} {X : ι → Type v}
variable {B : Type z} {Y : Type t}
variable (S : AtomicSource.{u,v,w} ι X)

/-- A pair of formal vertices has a specified old edge precisely
when the PARTIAL typed old diagram gives an actual diversity atom.
The original ordered sorts remain attached to that atom. -/
def OriginalSpecifiedEdge
    (D : PartialDiagram S (B ⊕ Y)) (x y : B ⊕ Y) : Prop :=
  ∃ h : x ≠ y,
    ∃ a : S.Atom (D.vertexSort x) (D.vertexSort y),
      D.edge x y h = some a

/-- The specified graph remembers precisely the old atomic edges,
not an arbitrary completion of the unspecified clone graph. -/
def originalSpecifiedGraph
    (D : PartialDiagram S (B ⊕ Y)) : SimpleGraph (B ⊕ Y) where
  Adj := OriginalSpecifiedEdge S D
  symm := by
    intro x y h
    obtain ⟨hxy,a,ha⟩ := h
    exact ⟨hxy.symm,S.conv a,(D.edge_reverse x y hxy a).mp ha⟩
  loopless := by
    intro x h
    obtain ⟨hxy,_,_⟩ := h
    exact hxy rfl

/-- An ACTUAL old complete base and a full family of literal
specified old SPOKE atoms: every pair touching an old base
point receives a diversity atom unless it is the same vertex.
This includes all pairs of distinct base points; there is no
condition on missing clone-clone edges. -/
def OriginalCompleteBaseSpokes
    (D : PartialDiagram S (B ⊕ Y)) : Prop :=
  ∀ (d : B) (z : B ⊕ Y) (hne : (Sum.inl d : B ⊕ Y) ≠ z),
    ∃ a : S.Atom (D.vertexSort (Sum.inl d)) (D.vertexSort z),
      D.edge (Sum.inl d) z hne = some a

/-- The fully typed old specification satisfies exactly the
graph's base/spoke completeness premise, without losing or
inventing any old orbital colour. -/
theorem original_specified_graph_complete_base_spokes
    (D : PartialDiagram S (B ⊕ Y))
    (hBase : OriginalCompleteBaseSpokes S D) :
    CompleteBaseSpokes (originalSpecifiedGraph S D) := by
  intro d z hne
  obtain ⟨a,ha⟩ := hBase d z hne.symm
  exact ⟨hne.symm,a,ha⟩

/-- Source11 T01's exact typed partial-old-diagram receiver:
a long no-distance-two-chord specified simple cycle cannot
pass through the complete old base. It lies entirely in clones,
whose unspecified pairs are still unspecified. -/
theorem original_typed_complete_base_chordless_clone_only
    {n : Nat} [NeZero n] (hn : 4 ≤ n)
    (D : PartialDiagram S (B ⊕ Y))
    (hBase : OriginalCompleteBaseSpokes S D)
    (f : CycleCode (B ⊕ Y) n)
    (hNo : NoTwoStepChords (originalSpecifiedGraph S D) f) :
    ∀ i : ZMod n, ∃ y : Y, f i = Sum.inr y := by
  exact complete_base_chordless_cycle_clone_only
    hn (originalSpecifiedGraph S D)
    (original_specified_graph_complete_base_spokes S D hBase)
    f hNo

end CCO.TypedOrbitFrames
