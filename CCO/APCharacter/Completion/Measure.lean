import CCO.APCharacter.Completion.Walks
import CCO.StrongExact.PairEdgeExtension
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! The second coordinate counts actual missing UNORDERED pairs. Inserting
a diversity edge strictly decreases it without changing the vertex carrier. -/
universe u v w z
namespace CCO.APCharacter.Completion
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {V : Type z} (D : PartialDiagram S V)
noncomputable def missingCount : ℕ := ((graph D)ᶜ.edgeSet).ncard

/-- An old missing pair is a concrete positive contribution to the measure. -/
theorem missingCount_pos (x y : V) (hxy : x ≠ y)
    (missing : D.edge x y hxy = none) : 0 < missingCount D := by
  classical
  letI : Finite V := D.finite_type
  have hAdj : ((graph D)ᶜ).Adj x y := by
    refine ⟨hxy,?_⟩
    rintro ⟨h,a,ha⟩
    rw [missing] at ha
    cases ha
  have he : s(x,y) ∈ (graph D)ᶜ.edgeSet := hAdj
  exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨s(x,y),he⟩

/-- The graph really gains an edge, rather than overwriting an old label. -/
theorem insertion_graph_lt (x y : V) (hxy : x ≠ y)
    (missing : D.edge x y hxy = none)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y)) :
    graph D < graph (D.withPair x y hxy a) := by
  refine lt_iff_le_and_ne.mpr ⟨?_,?_⟩
  · rintro p q ⟨hpq,b,hb⟩
    refine ⟨hpq,b,D.withPair_preserves_old x y hxy a ?_ p q hpq b hb⟩
    intro b hb
    rw [missing] at hb
    cases hb
  · intro he
    have ha : (graph (D.withPair x y hxy a)).Adj x y :=
      ⟨hxy,a,D.withPair_specified x y hxy a⟩
    rw [← he] at ha
    obtain ⟨_,b,hb⟩ := ha
    rw [missing] at hb
    cases hb

theorem insertion_missingCount_lt (x y : V) (hxy : x ≠ y)
    (missing : D.edge x y hxy = none)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y)) :
    missingCount (D.withPair x y hxy a) < missingCount D := by
  classical
  letI : Finite V := D.finite_type
  have hg : (graph (D.withPair x y hxy a))ᶜ < (graph D)ᶜ :=
    compl_lt_compl_iff_lt.mpr (insertion_graph_lt D x y hxy missing a)
  have he := SimpleGraph.edgeSet_strict_mono hg
  have hfin : (graph D)ᶜ.edgeSet.Finite := Set.toFinite _
  simpa only [missingCount] using
    Set.ncard_lt_ncard he hfin

end CCO.APCharacter.Completion
