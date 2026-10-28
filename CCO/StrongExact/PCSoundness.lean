import CCO.StrongExact.PCConverse
import CCO.StrongExact.PathSupport

/-!
# C12 local soundness: every specified triangle survives as a real triangle

When all final Boolean STRONG PC domains are nonempty, a literal old
specified edge is exactly its original atomic singleton. Combining this
with the FULL all-three-coordinate PC inclusions proves that every
specified three-cycle is a genuine three-distinct-point original-source
triangle. This is the length-three part of the source's C12
general simple-cycle criterion; longer cycles still require the
strong positive-path support proof and the global CCO argument.

No source CCO, SAP, exact Helly, NR2 or fake identity is assumed.
-/

universe u v w z

namespace CCO.StrongPC

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u, v, w} ι X} {V : Type z}
variable (D : PartialDiagram S V)

/-- On a literal old displayed fine atom, the PC fixed domain can
only retain that atom; it cannot introduce any new old colour. -/
theorem fixedNetwork_subset_specified_singleton
    {x y : V} (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : D.edge x y hxy = some a) :
    fixedNetwork D ⟨x, y, hxy⟩ ⊆ ({a} : S.Menu _ _) := by
  intro b hb
  have h := fixedNetwork_refines_initial D ⟨x, y, hxy⟩ hb
  simpa only [initial, ha, Set.mem_singleton_iff] using h

/-- Nonempty fixed domains on specified edges are exactly the old
singletons; the nonempty premise is essential. -/
theorem fixedNetwork_eq_specified_singleton_of_nonempty
    {x y : V} (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (ha : D.edge x y hxy = some a)
    (hne : (fixedNetwork D ⟨x, y, hxy⟩).Nonempty) :
    fixedNetwork D ⟨x, y, hxy⟩ = ({a} : S.Menu _ _) := by
  have hSub := fixedNetwork_subset_specified_singleton D hxy a ha
  obtain ⟨b, hb⟩ := hne
  have hEq : b = a := Set.mem_singleton_iff.mp (hSub hb)
  have haMem : a ∈ fixedNetwork D ⟨x, y, hxy⟩ := by
    simpa only [hEq] using hb
  apply Set.Subset.antisymm hSub
  intro c hc
  have hca : c = a := Set.mem_singleton_iff.mp hc
  subst c
  exact haMem

/-- A zero-free strong PC fixed network cannot retain an old
specified triangle that is illegal in the original source. The
resulting witness uses three distinct real vertices because each
specified input and output is a genuine diversity atom. -/
theorem specified_triangle_legal_of_nonempty_fixedNetwork
    (x y z : V) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y))
    (b : S.Atom (D.vertexSort y) (D.vertexSort z))
    (c : S.Atom (D.vertexSort x) (D.vertexSort z))
    (ha : D.edge x y hxy = some a)
    (hb : D.edge y z hyz = some b)
    (hc : D.edge x z hxz = some c)
    (hNonempty : ∀ p : DistinctPair V, (fixedNetwork D p).Nonempty) :
    S.Triangle a b c := by
  have hA := fixedNetwork_eq_specified_singleton_of_nonempty
    D hxy a ha (hNonempty ⟨x, y, hxy⟩)
  have hB := fixedNetwork_eq_specified_singleton_of_nonempty
    D hyz b hb (hNonempty ⟨y, z, hyz⟩)
  have hC := fixedNetwork_eq_specified_singleton_of_nonempty
    D hxz c hc (hNonempty ⟨x, z, hxz⟩)
  have hPC := fixedNetwork_PC D hxy hyz hxz
  rw [hA, hB, hC] at hPC
  have hcSupported : c ∈ S.product
      ({a} : S.Menu (D.vertexSort x) (D.vertexSort y))
      ({b} : S.Menu (D.vertexSort y) (D.vertexSort z)) :=
    hPC.1 (show c ∈ ({c} :
      S.Menu (D.vertexSort x) (D.vertexSort z)) by simp)
  obtain ⟨a', ha', b', hb', htri⟩ := hcSupported
  have hEqA : a' = a := Set.mem_singleton_iff.mp ha'
  have hEqB : b' = b := Set.mem_singleton_iff.mp hb'
  subst a'
  subst b'
  exact htri

end CCO.StrongPC
