import CCO.FiniteHelpers
import CCO.PairHomogeneity
import CCO.StrongGeometry

/-!
# From actual age-SAP to strong point gluing

The proof below uses the *real* complete two-point induced structures,
aligns their common named vertex by one old automorphism, strongly
amalgamates them over the complete singleton base, and reads the colour
of the two off-base vertices. No abstract colour-table SAP axiom is
substituted for actual age-SAP.
-/

universe u v w

namespace CCO

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X)

theorem tagged_exists_of_sort (p : Sigma X) (i : ι)
    (h : p.1 = i) : ∃ x : X i, p = ⟨i, x⟩ := by
  rcases p with ⟨j, x⟩
  cases h
  exact ⟨x, rfl⟩

theorem taggedColour_eq_iff {i j : ι}
    (x x' : X i) (y y' : X j) :
    taggedColour S (⟨i, x⟩ : Sigma X) ⟨j, y⟩ =
      taggedColour S (⟨i, x'⟩ : Sigma X) ⟨j, y'⟩ ↔
      S.colour x y = S.colour x' y' := by
  simp [taggedColour, Sigma.mk.injEq, heq_eq_eq]

namespace AtomicSource

variable (S : AtomicSource ι X)
variable {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]

/-- The elementary nonempty STRONG two-step product follows directly
from SAP of the original finite induced age and real finite homogeneity.
This discharges the local `RealPointGluing` provider, rather than
silently assuming a colour-table completion axiom. -/
theorem realPointGluing_of_SAP
    (H : HomogeneousSource S G) (sap : AgeSAP S) :
    S.RealPointGluing := by
  intro i j k a b
  obtain ⟨x, y, hxy⟩ := S.realized a
  obtain ⟨y', z, hyz'⟩ := S.realized b
  obtain ⟨g, hgy⟩ :=
    (S.original_sort_transitive_of_homogeneous H j) y' y
  have hyz : S.colour y (g • z) = some b := by
    have h := (S.colourInvariant_of_homogeneous H
      (i := j) (j := k)) g y' z
    rw [hgy] at h
    exact h.trans hyz'
  let px : Sigma X := ⟨i, x⟩
  let py : Sigma X := ⟨j, y⟩
  let pz : Sigma X := ⟨k, g • z⟩
  let Base : FiniteInduced (X := X) :=
    FiniteInduced.ofFinset ({py} : Finset (Sigma X))
  let Left : FiniteInduced (X := X) :=
    FiniteInduced.ofFinset ({px, py} : Finset (Sigma X))
  let Right : FiniteInduced (X := X) :=
    FiniteInduced.ofFinset ({py, pz} : Finset (Sigma X))
  have hyBase : py ∈ Base.vertices := by
    simp [Base, FiniteInduced.ofFinset]
  have hxLeft : px ∈ Left.vertices := by
    simp [Left, FiniteInduced.ofFinset]
  have hyLeft : py ∈ Left.vertices := by
    simp [Left, FiniteInduced.ofFinset]
  have hyRight : py ∈ Right.vertices := by
    simp [Right, FiniteInduced.ofFinset]
  have hzRight : pz ∈ Right.vertices := by
    simp [Right, FiniteInduced.ofFinset]
  have hBaseLeft : Base.vertices ⊆ Left.vertices := by
    intro t ht
    have ht' : t = py := by
      simpa [Base, FiniteInduced.ofFinset] using ht
    rw [ht']
    exact hyLeft
  have hBaseRight : Base.vertices ⊆ Right.vertices := by
    intro t ht
    have ht' : t = py := by
      simpa [Base, FiniteInduced.ofFinset] using ht
    rw [ht']
    exact hyRight
  let eBL : InducedEmbedding S Base Left :=
    inducedInclusion S Base Left hBaseLeft
  let eBR : InducedEmbedding S Base Right :=
    inducedInclusion S Base Right hBaseRight
  obtain ⟨D, eLD, eRD, hAgree, hIntersection⟩ :=
    sap.strong_amalgamate Base Left Right eBL eBR
  let xl : ↥Left.vertices := ⟨px, hxLeft⟩
  let yl : ↥Left.vertices := ⟨py, hyLeft⟩
  let yr : ↥Right.vertices := ⟨py, hyRight⟩
  let zr : ↥Right.vertices := ⟨pz, hzRight⟩
  let outX : Sigma X := (eLD.toEmbedding xl).val
  let outY : Sigma X := (eLD.toEmbedding yl).val
  let outZ : Sigma X := (eRD.toEmbedding zr).val
  have hOutSortX : outX.1 = i := by
    exact eLD.preserves_sort xl
  have hOutSortY : outY.1 = j := by
    exact eLD.preserves_sort yl
  have hOutSortZ : outZ.1 = k := by
    exact eRD.preserves_sort zr
  obtain ⟨x₁, hx₁⟩ := tagged_exists_of_sort (X := X) outX i hOutSortX
  obtain ⟨y₁, hy₁⟩ := tagged_exists_of_sort (X := X) outY j hOutSortY
  obtain ⟨z₁, hz₁⟩ := tagged_exists_of_sort (X := X) outZ k hOutSortZ
  have hyAgree : eLD.toEmbedding yl = eRD.toEmbedding yr := by
    simpa only [eBL, eBR, inducedInclusion] using
      (hAgree (⟨py, hyBase⟩ : ↥Base.vertices))
  have hOutputXY : S.colour x₁ y₁ = some a := by
    have hc := eLD.preserves_colours xl yl
    change taggedColour S px py = taggedColour S outX outY at hc
    rw [hx₁, hy₁] at hc
    have hcol : S.colour x y = S.colour x₁ y₁ := by
      exact (taggedColour_eq_iff S x x₁ y y₁).mp hc
    exact hcol.symm.trans hxy
  have hOutputYZ : S.colour y₁ z₁ = some b := by
    have hc := eRD.preserves_colours yr zr
    change taggedColour S py pz =
      taggedColour S (eRD.toEmbedding yr).val outZ at hc
    rw [← hyAgree] at hc
    change taggedColour S py pz = taggedColour S outY outZ at hc
    rw [hy₁, hz₁] at hc
    have hcol : S.colour y (g • z) = S.colour y₁ z₁ :=
      (taggedColour_eq_iff S y y₁ (g • z) z₁).mp hc
    exact hcol.symm.trans hyz
  have hDistinct : outX ≠ outZ := by
    intro heq
    have heqD : eLD.toEmbedding xl = eRD.toEmbedding zr :=
      Subtype.ext heq
    obtain ⟨c, hcx, _⟩ := hIntersection xl zr heqD
    have hcX : c.val = px := by
      have h := congrArg Subtype.val hcx
      change c.val = px at h
      exact h
    have hcY : c.val = py := by
      simpa [Base, FiniteInduced.ofFinset] using c.property
    have hneq : px ≠ py := S.atomRel_ne hxy
    exact hneq (hcX.symm.trans hcY)
  have hDistinctTyped : (⟨i, x₁⟩ : Sigma X) ≠ ⟨k, z₁⟩ := by
    simpa [hx₁, hz₁] using hDistinct
  obtain ⟨c, hxz⟩ := S.some_colour_of_ne x₁ z₁ hDistinctTyped
  exact ⟨c, x₁, y₁, z₁, hOutputXY, hOutputYZ, hxz⟩

end AtomicSource
end CCO
