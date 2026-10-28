import CCO.StrongExact.ExactMenus
import CCO.StabilizerSAP
import CCO.StrongGeometry

/-!
# Every original typed diversity palette is nonempty under actual SAP

B001's AtomicSource interface only requires every EXISTING atom to be
realized; it does not postulate that each pair palette has an atom.
The pinned STRONG source, however, has nonempty diversity palettes for
every ordered sort pair. Derive this genuine property from original
nonempty sorts, finite-source homogeneity, and age-SAP: a stabilizer
orbit over the empty complete base supplies a fresh point in any
prescribed sort, different from the other root, even if the sorts
coincide. Its genuine fine pair colour gives a diversity atom.

This is an explicit source-level provider rather than an axiom or a
hidden `Nonempty (S.Atom i j)` assumption.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u, v, w} ι X)
variable {G : Type*} [Group G] [∀ q : ι, MulAction G (X q)]

/-- Actual original SAP and homogeneity imply every typed diversity
palette is inhabited, even on the diagonal sort i=j. -/
theorem palette_nonempty_of_SAP
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (i j : ι) : _root_.Nonempty (S.Atom i j) := by
  obtain ⟨x⟩ := S.nonemptySort i
  obtain ⟨y⟩ := S.nonemptySort j
  let B : FiniteInduced (X := X) :=
    ⟨∅, Set.finite_empty⟩
  let F : Set (Sigma X) := {⟨i, x⟩}
  have hnotBase : (⟨j, y⟩ : Sigma X) ∉ B.vertices := by
    simp [B]
  have hfinite : F.Finite := Set.finite_singleton _
  obtain ⟨z, hzOrb, hzFresh⟩ :=
    RealAction.orbit_has_fresh_point_of_SAP S H sap
      B (⟨j, y⟩ : Sigma X) hnotBase F hfinite
  have hzSort : z.1 = j := by
    rcases hzOrb with ⟨g, _, hgz⟩
    have hh := H.preserves_sort g (⟨j, y⟩ : Sigma X)
    rw [hgz] at hh
    exact hh
  rcases z with ⟨k, y'⟩
  change k = j at hzSort
  cases hzSort
  have hDifferent : (⟨i, x⟩ : Sigma X) ≠ ⟨j, y'⟩ := by
    intro he
    apply hzFresh
    change (⟨j, y'⟩ : Sigma X) ∈ F
    exact Set.mem_singleton_iff.mpr he.symm
  obtain ⟨a, _⟩ := S.some_colour_of_ne x y' hDifferent
  exact ⟨a⟩

/-- C07/C08 empty presentation case: typed diversity Top is an
actual nonempty exact menu, with no logical identity atom. -/
theorem exact_top_of_SAP
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} :
    Exact S (Set.univ : S.Menu i j) := by
  obtain ⟨a⟩ := palette_nonempty_of_SAP S H sap i j
  exact exact_top S ⟨a, Set.mem_univ a⟩

end CCO.StrongExact
