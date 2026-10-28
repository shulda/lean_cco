import CCO.RealClosure.Bounds.Directions
import Mathlib.Data.Finset.Lattice.Prod

/-! B011 C04–05: finite exact bottom and the Boolean joins of minimal
infinite directions. Distributivity is used ONLY in the actual exact
sublattice. The greatest finite original packet is never declared exact. -/
noncomputable section
universe v w t
namespace CCO.RealClosure.Bounds
open ParityHasse.Original ExactCRT RealHull.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,0,w} S)

local instance : DecidableEq (Direction S) := Classical.decEq _

abbrev ExactOriginal : Type v := ExactEq S H (semanticCCO_change_universe S cco) ()

local instance : Finite (ExactOriginal S H cco) :=
  exactEqFinite S H (semanticCCO_change_universe S cco) ()
local instance : OrderBot (ExactOriginal S H cco) :=
  exactEqOrderBot S H (semanticCCO_change_universe S cco) ()

def exactAsColour (E : ExactOriginal S H cco) : ColourEq S () :=
  ⟨E.val,isExactEq_colourInvariant S H E.property⟩

noncomputable def finiteExactPacket : ExactOriginal S H cco := by
  classical
  letI : Fintype (ExactOriginal S H cco) := Fintype.ofFinite _
  exact (Finset.univ.filter (fun E => FiniteClasses S (exactAsColour S H cco E))).sup id

theorem exact_finite_sup (E F : ExactOriginal S H cco)
    (hE : FiniteClasses S (exactAsColour S H cco E))
    (hF : FiniteClasses S (exactAsColour S H cco F)) :
    FiniteClasses S (exactAsColour S H cco (E ⊔ F)) :=
  finite_classes_sup S H (exactAsColour S H cco E) (exactAsColour S H cco F) hE hF

theorem finiteExactPacket_finite :
    FiniteClasses S (exactAsColour S H cco (finiteExactPacket S H cco)) := by
  classical
  letI : Fintype (ExactOriginal S H cco) := Fintype.ofFinite _
  apply Finset.sup_induction
    (finiteClasses_bot S)
    (fun E hE F hF => exact_finite_sup S H cco E F hE hF)
  intro E hE
  exact (Finset.mem_filter.mp hE).2

theorem le_finiteExactPacket (E : ExactOriginal S H cco)
    (hE : FiniteClasses S (exactAsColour S H cco E)) : E ≤ finiteExactPacket S H cco := by
  classical
  letI : Fintype (ExactOriginal S H cco) := Fintype.ofFinite _
  exact Finset.le_sup (f := fun K : ExactOriginal S H cco => K)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hE⟩)

theorem finiteExactPacket_le_packet :
    exactAsColour S H cco (finiteExactPacket S H cco) ≤ finitePacket S H :=
  le_finitePacket S H _ (finiteExactPacket_finite S H cco)

def exactDirection (D : Direction S) : ExactOriginal S H cco :=
  ⟨D.val.val,direction_exact S H cco D⟩

theorem exactDirection_inf_le_finiteExactPacket {D E : Direction S} (hne : D ≠ E) :
    exactDirection S H cco D ⊓ exactDirection S H cco E ≤ finiteExactPacket S H cco := by
  apply le_finiteExactPacket
  exact distinct_direction_inf_finite S D.property E.property
    (fun h => hne (Subtype.ext h))

noncomputable def directionSpan (s : Finset (Direction S)) : ExactOriginal S H cco :=
  finiteExactPacket S H cco ⊔ s.sup (exactDirection S H cco)

@[simp] theorem directionSpan_empty : directionSpan S H cco ∅ = finiteExactPacket S H cco :=
  sup_bot_eq _

theorem finiteExactPacket_le_span (s : Finset (Direction S)) :
    finiteExactPacket S H cco ≤ directionSpan S H cco s := le_sup_left

theorem direction_le_span {s : Finset (Direction S)} {D : Direction S} (hD : D ∈ s) :
    exactDirection S H cco D ≤ directionSpan S H cco s :=
  le_trans (Finset.le_sup hD) le_sup_right

theorem directionSpan_mono {s t : Finset (Direction S)} (h : s ⊆ t) :
    directionSpan S H cco s ≤ directionSpan S H cco t :=
  sup_le_sup_left (Finset.sup_mono h) _

theorem directionSpan_union (s t : Finset (Direction S)) :
    directionSpan S H cco (s ∪ t) = directionSpan S H cco s ⊔ directionSpan S H cco t := by
  classical
  simp [directionSpan,Finset.sup_union,sup_assoc,sup_left_comm,sup_comm]

/-- The exact Boolean meet identity, including either empty subset. -/
theorem directionSpan_inf (s t : Finset (Direction S)) :
    directionSpan S H cco s ⊓ directionSpan S H cco t = directionSpan S H cco (s ∩ t) := by
  classical
  letI := exactDistribLattice S H (semanticCCO_change_universe S cco) ()
  apply le_antisymm
  · change (finiteExactPacket S H cco ⊔ s.sup (exactDirection S H cco)) ⊓
      (finiteExactPacket S H cco ⊔ t.sup (exactDirection S H cco)) ≤ _
    rw [← sup_inf_left,Finset.sup_inf_sup]
    apply sup_le (finiteExactPacket_le_span S H cco _)
    apply Finset.sup_le
    intro pair hp
    obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hp
    by_cases he : pair.1 = pair.2
    · rw [he,inf_idem]
      exact direction_le_span S H cco (Finset.mem_inter.mpr ⟨he ▸ h₁,h₂⟩)
    · exact le_trans (exactDirection_inf_le_finiteExactPacket S H cco he)
        (finiteExactPacket_le_span S H cco _)
  · exact le_inf (directionSpan_mono S H cco Finset.inter_subset_left)
      (directionSpan_mono S H cco Finset.inter_subset_right)

/-- For a selected direction the opposite facet meets it exactly in the
finite exact bottom; the possibly nonexact F plays no role in this identity. -/
theorem singleton_inf_deleted_facet {s : Finset (Direction S)} {D : Direction S} :
    directionSpan S H cco {D} ⊓ directionSpan S H cco (s.erase D) =
      finiteExactPacket S H cco := by
  classical
  rw [directionSpan_inf]
  have he : ({D} : Finset (Direction S)) ∩ s.erase D = ∅ := by
    ext E
    simp only [Finset.mem_inter,Finset.mem_singleton,Finset.mem_erase,Finset.notMem_empty,iff_false]
    rintro ⟨rfl,h, _⟩
    exact h rfl
  rw [he,directionSpan_empty]

end CCO.RealClosure.Bounds
