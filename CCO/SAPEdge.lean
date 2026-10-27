import CCO.SAPPoint

/-!
# Actual complete-edge SAP gluing for STRONG triangle algebra

Two *actual* complete triangles with the same original colour on
their common edge are first aligned by finite pair homogeneity. Age-SAP
then amalgamates the full two-point base, keeping the off-edge
vertices distinct. This derives the RealEdgeGluing property used by
strong associativity and Set-Pasch. No RAW Helly or CCO is involved.
-/

universe u v w

namespace CCO.AtomicSource

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X)
variable {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]

theorem realEdgeGluing_of_SAP
    (H : HomogeneousSource S G) (sap : AgeSAP S) :
    S.RealEdgeGluing := by
  classical
  intro i j k l a b c d e hFirst hSecond
  obtain ⟨x, y, z, hxy, hyz, hxz⟩ := hFirst
  obtain ⟨x', z', t, hx'z', hz't, hx't⟩ := hSecond
  obtain ⟨g, hgx, hgz⟩ :=
    (S.pair_homogeneous_of_homogeneous H (i := i) (j := k))
      x' x z' z (hx'z'.trans hxz.symm)
  have hxt : S.colour x (g • t) = some d := by
    have h := (S.colourInvariant_of_homogeneous H
      (i := i) (j := l)) g x' t
    rw [hgx] at h
    exact h.trans hx't
  have hzt : S.colour z (g • t) = some e := by
    have h := (S.colourInvariant_of_homogeneous H
      (i := k) (j := l)) g z' t
    rw [hgz] at h
    exact h.trans hz't
  let px : Sigma X := ⟨i, x⟩
  let py : Sigma X := ⟨j, y⟩
  let pz : Sigma X := ⟨k, z⟩
  let pt : Sigma X := ⟨l, g • t⟩
  let Base : FiniteInduced (X := X) :=
    FiniteInduced.ofFinset ({px, pz} : Finset (Sigma X))
  let Left : FiniteInduced (X := X) :=
    FiniteInduced.ofFinset ({px, py, pz} : Finset (Sigma X))
  let Right : FiniteInduced (X := X) :=
    FiniteInduced.ofFinset ({px, pz, pt} : Finset (Sigma X))
  have hpxBase : px ∈ Base.vertices := by
    simp [Base, FiniteInduced.ofFinset]
  have hpzBase : pz ∈ Base.vertices := by
    simp [Base, FiniteInduced.ofFinset]
  have hpxLeft : px ∈ Left.vertices := by
    simp [Left, FiniteInduced.ofFinset]
  have hpyLeft : py ∈ Left.vertices := by
    simp [Left, FiniteInduced.ofFinset]
  have hpzLeft : pz ∈ Left.vertices := by
    simp [Left, FiniteInduced.ofFinset]
  have hpxRight : px ∈ Right.vertices := by
    simp [Right, FiniteInduced.ofFinset]
  have hpzRight : pz ∈ Right.vertices := by
    simp [Right, FiniteInduced.ofFinset]
  have hptRight : pt ∈ Right.vertices := by
    simp [Right, FiniteInduced.ofFinset]
  have hBaseLeft : Base.vertices ⊆ Left.vertices := by
    intro s hs
    have h : s = px ∨ s = pz := by
      simpa [Base, FiniteInduced.ofFinset] using hs
    rcases h with rfl | rfl
    · exact hpxLeft
    · exact hpzLeft
  have hBaseRight : Base.vertices ⊆ Right.vertices := by
    intro s hs
    have h : s = px ∨ s = pz := by
      simpa [Base, FiniteInduced.ofFinset] using hs
    rcases h with rfl | rfl
    · exact hpxRight
    · exact hpzRight
  let eBL : InducedEmbedding S Base Left :=
    inducedInclusion S Base Left hBaseLeft
  let eBR : InducedEmbedding S Base Right :=
    inducedInclusion S Base Right hBaseRight
  obtain ⟨D, eLD, eRD, hAgree, hIntersection⟩ :=
    sap.strong_amalgamate Base Left Right eBL eBR
  let xl : ↥Left.vertices := ⟨px, hpxLeft⟩
  let yl : ↥Left.vertices := ⟨py, hpyLeft⟩
  let zl : ↥Left.vertices := ⟨pz, hpzLeft⟩
  let xr : ↥Right.vertices := ⟨px, hpxRight⟩
  let zr : ↥Right.vertices := ⟨pz, hpzRight⟩
  let tr : ↥Right.vertices := ⟨pt, hptRight⟩
  let outX : Sigma X := (eLD.toEmbedding xl).val
  let outY : Sigma X := (eLD.toEmbedding yl).val
  let outZ : Sigma X := (eLD.toEmbedding zl).val
  let outT : Sigma X := (eRD.toEmbedding tr).val
  have hSortX : outX.1 = i := eLD.preserves_sort xl
  have hSortY : outY.1 = j := eLD.preserves_sort yl
  have hSortZ : outZ.1 = k := eLD.preserves_sort zl
  have hSortT : outT.1 = l := eRD.preserves_sort tr
  obtain ⟨x₁, hx₁⟩ := tagged_exists_of_sort (X := X) outX i hSortX
  obtain ⟨y₁, hy₁⟩ := tagged_exists_of_sort (X := X) outY j hSortY
  obtain ⟨z₁, hz₁⟩ := tagged_exists_of_sort (X := X) outZ k hSortZ
  obtain ⟨t₁, ht₁⟩ := tagged_exists_of_sort (X := X) outT l hSortT
  have hxAgree : eLD.toEmbedding xl = eRD.toEmbedding xr := by
    have h := hAgree (⟨px, hpxBase⟩ : ↥Base.vertices)
    have hEL : eBL.toEmbedding (⟨px, hpxBase⟩ : ↥Base.vertices) = xl := rfl
    have hER : eBR.toEmbedding (⟨px, hpxBase⟩ : ↥Base.vertices) = xr := rfl
    rw [hEL, hER] at h
    exact h
  have hzAgree : eLD.toEmbedding zl = eRD.toEmbedding zr := by
    have h := hAgree (⟨pz, hpzBase⟩ : ↥Base.vertices)
    have hEL : eBL.toEmbedding (⟨pz, hpzBase⟩ : ↥Base.vertices) = zl := rfl
    have hER : eBR.toEmbedding (⟨pz, hpzBase⟩ : ↥Base.vertices) = zr := rfl
    rw [hEL, hER] at h
    exact h
  have hOutputXY : S.colour x₁ y₁ = some a := by
    have hc := eLD.preserves_colours xl yl
    change taggedColour S px py = taggedColour S outX outY at hc
    rw [hx₁, hy₁] at hc
    have hcol : S.colour x y = S.colour x₁ y₁ :=
      (taggedColour_eq_iff S x x₁ y y₁).mp hc
    exact hcol.symm.trans hxy
  have hOutputYZ : S.colour y₁ z₁ = some b := by
    have hc := eLD.preserves_colours yl zl
    change taggedColour S py pz = taggedColour S outY outZ at hc
    rw [hy₁, hz₁] at hc
    have hcol : S.colour y z = S.colour y₁ z₁ :=
      (taggedColour_eq_iff S y y₁ z z₁).mp hc
    exact hcol.symm.trans hyz
  have hOutputXZ : S.colour x₁ z₁ = some c := by
    have hc := eLD.preserves_colours xl zl
    change taggedColour S px pz = taggedColour S outX outZ at hc
    rw [hx₁, hz₁] at hc
    have hcol : S.colour x z = S.colour x₁ z₁ :=
      (taggedColour_eq_iff S x x₁ z z₁).mp hc
    exact hcol.symm.trans hxz
  have hOutputXT : S.colour x₁ t₁ = some d := by
    have hc := eRD.preserves_colours xr tr
    change taggedColour S px pt =
      taggedColour S (eRD.toEmbedding xr).val outT at hc
    rw [← hxAgree] at hc
    change taggedColour S px pt = taggedColour S outX outT at hc
    rw [hx₁, ht₁] at hc
    have hcol : S.colour x (g • t) = S.colour x₁ t₁ :=
      (taggedColour_eq_iff S x x₁ (g • t) t₁).mp hc
    exact hcol.symm.trans hxt
  have hOutputZT : S.colour z₁ t₁ = some e := by
    have hc := eRD.preserves_colours zr tr
    change taggedColour S pz pt =
      taggedColour S (eRD.toEmbedding zr).val outT at hc
    rw [← hzAgree] at hc
    change taggedColour S pz pt = taggedColour S outZ outT at hc
    rw [hz₁, ht₁] at hc
    have hcol : S.colour z (g • t) = S.colour z₁ t₁ :=
      (taggedColour_eq_iff S z z₁ (g • t) t₁).mp hc
    exact hcol.symm.trans hzt
  have hDistinct : outY ≠ outT := by
    intro heq
    have heqD : eLD.toEmbedding yl = eRD.toEmbedding tr :=
      Subtype.ext heq
    obtain ⟨q, hqY, _⟩ := hIntersection yl tr heqD
    have hqYval : q.val = py := by
      have h := congrArg Subtype.val hqY
      change q.val = py at h
      exact h
    have hqBase : q.val = px ∨ q.val = pz := by
      simpa [Base, FiniteInduced.ofFinset] using q.property
    rcases hqBase with hpx | hpz
    · exact (S.atomRel_ne hxy).symm (hqYval.symm.trans hpx)
    · exact (S.atomRel_ne hyz) (hqYval.symm.trans hpz)
  have hTypedDistinct : (⟨j, y₁⟩ : Sigma X) ≠ ⟨l, t₁⟩ := by
    simpa [hy₁, ht₁] using hDistinct
  exact ⟨x₁, y₁, z₁, t₁, hOutputXY, hOutputYZ,
    hOutputXZ, hOutputXT, hOutputZT, hTypedDistinct⟩

end CCO.AtomicSource
