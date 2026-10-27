import CCO.SAPHelpers
import CCO.StabilizerHomogeneity
import CCO.FiniteHelpers
import Mathlib.Algebra.Group.Action.Sigma

/-!
# Infinite pointwise-stabilizer orbits from the *actual* age-SAP

No infinite-orbit axiom is assumed. Strongly amalgamate one further
copy of a complete one-point extension against the finite set of points
to avoid. Align the old large finite factor using homogeneity, then
the fresh image has precisely the previous complete colour type over
the original base. This is the key geometric step for B001
injectivization; CCO and NR2 play no role.
-/

universe u v w

namespace CCO.RealAction

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X)
variable {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]

theorem orbit_has_fresh_point_of_SAP
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (B : FiniteInduced (X := X))
    (x : Sigma X) (hx : x ∉ B.vertices)
    (F : Set (Sigma X)) (hF : F.Finite) :
    ∃ y : Sigma X,
      y ∈ orbitOver (G := G) B.vertices x ∧ y ∉ F := by
  let Ext : FiniteInduced (X := X) := {
    vertices := Set.insert x B.vertices
    finite_vertices := B.finite_vertices.insert x
  }
  let A : FiniteInduced (X := X) := {
    vertices := Set.insert x (B.vertices ∪ F)
    finite_vertices := (B.finite_vertices.union hF).insert x
  }
  have hBExt : B.vertices ⊆ Ext.vertices := by
    intro b hb
    exact Set.mem_insert_of_mem hb
  have hBA : B.vertices ⊆ A.vertices := by
    intro b hb
    exact Set.mem_insert_of_mem (Or.inl hb)
  have hFA : F ⊆ A.vertices := by
    intro b hb
    exact Set.mem_insert_of_mem (Or.inr hb)
  let eBExt : InducedEmbedding S B Ext :=
    inducedInclusion S B Ext hBExt
  let eBA : InducedEmbedding S B A :=
    inducedInclusion S B A hBA
  have hxExt : x ∈ Ext.vertices := Set.mem_insert x B.vertices
  let xExt : ↥Ext.vertices := ⟨x, hxExt⟩
  have hxNew : ∀ c : ↥B.vertices, eBExt.toEmbedding c ≠ xExt := by
    intro c hc
    have hv : c.val = x := by
      have hv' := congrArg Subtype.val hc
      change c.val = x at hv'
      exact hv'
    exact hx (hv ▸ c.property)
  obtain ⟨D, eExtD, eAD, hBase, hFresh⟩ :=
    AgeSAP.amalgamate_avoiding_old_point S sap B Ext A eBExt eBA xExt hxNew
  obtain ⟨g, hg⟩ :=
    HomogeneousSource.extends_partial_iso S H A D eAD
  let xOut : Sigma X := (eExtD.toEmbedding xExt).val
  let y : Sigma X := g⁻¹ • xOut
  have hMove : g • y = xOut := by
    simp [y]
  have hAvoid : y ∉ F := by
    intro hyF
    let a : ↥A.vertices := ⟨y, hFA hyF⟩
    have hga : g • y = (eAD.toEmbedding a).val := hg a
    have heq : eExtD.toEmbedding xExt = eAD.toEmbedding a :=
      Subtype.ext (hMove.symm.trans hga)
    exact hFresh a heq
  have hCommon (b : Sigma X) (hb : b ∈ B.vertices) :
      g⁻¹ • (eExtD.toEmbedding
        (⟨b, hBExt hb⟩ : ↥Ext.vertices)).val = b := by
    let bB : ↥B.vertices := ⟨b, hb⟩
    let bExt : ↥Ext.vertices := ⟨b, hBExt hb⟩
    let bA : ↥A.vertices := ⟨b, hBA hb⟩
    have hAgree : (eExtD.toEmbedding bExt).val =
        (eAD.toEmbedding bA).val := by
      have h := hBase bB
      have hE : eBExt.toEmbedding bB = bExt := rfl
      have hA : eBA.toEmbedding bB = bA := rfl
      rw [hE, hA] at h
      exact congrArg Subtype.val h
    have hgb : g • b = (eAD.toEmbedding bA).val := hg bA
    change g⁻¹ • (eExtD.toEmbedding bExt).val = b
    rw [hAgree, ← hgb]
    exact inv_smul_smul g b
  have hSelf : taggedColour S x x = taggedColour S y y := by
    have hp := eExtD.preserves_colours xExt xExt
    have ha := H.preserves_colours g⁻¹ xOut xOut
    calc
      taggedColour S x x = taggedColour S xOut xOut := hp
      _ = taggedColour S y y := ha.symm
  have hLeft : ∀ b ∈ B.vertices,
      taggedColour S x b = taggedColour S y b := by
    intro b hb
    let bExt : ↥Ext.vertices := ⟨b, hBExt hb⟩
    have hp : taggedColour S x b =
        taggedColour S xOut (eExtD.toEmbedding bExt).val :=
      eExtD.preserves_colours xExt bExt
    have ha := H.preserves_colours g⁻¹ xOut (eExtD.toEmbedding bExt).val
    have hvalue : taggedColour S y b =
        taggedColour S xOut (eExtD.toEmbedding bExt).val := by
      simpa only [y, hCommon b hb] using ha
    exact hp.trans hvalue.symm
  have hRight : ∀ b ∈ B.vertices,
      taggedColour S b x = taggedColour S b y := by
    intro b hb
    let bExt : ↥Ext.vertices := ⟨b, hBExt hb⟩
    have hp : taggedColour S b x =
        taggedColour S (eExtD.toEmbedding bExt).val xOut :=
      eExtD.preserves_colours bExt xExt
    have ha := H.preserves_colours g⁻¹ (eExtD.toEmbedding bExt).val xOut
    have hvalue : taggedColour S b y =
        taggedColour S (eExtD.toEmbedding bExt).val xOut := by
      simpa only [y, hCommon b hb] using ha
    exact hp.trans hvalue.symm
  have hType : SameTypeOver S B x y := ⟨hSelf, hLeft, hRight⟩
  exact ⟨y, sameTypeOver_orbit S H B x y hType, hAvoid⟩

/-- B001 STRONG C04: a point outside a finite complete real base has
an INFINITE orbit under the actual pointwise stabilizer of that base.
This is deduced from age-SAP plus original finite homogeneity, with no
additional orbit-infinitude premise. -/
theorem infinite_stabilizer_orbit_of_SAP
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (B : FiniteInduced (X := X))
    (x : Sigma X) (hx : x ∉ B.vertices) :
    Set.Infinite (orbitOver (G := G) B.vertices x) := by
  intro hFinite
  obtain ⟨y, hyOrb, hyNot⟩ :=
    orbit_has_fresh_point_of_SAP S H sap B x hx
      (orbitOver (G := G) B.vertices x) hFinite
  exact hyNot hyOrb

end CCO.RealAction
