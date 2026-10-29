import CCO.FinitePackets.Normalization.SubgroupInterval
import Mathlib.Order.Hom.WithTopBot

/-! The complete lower interval of the ACTUAL minimal infinite cut is a
subgroup lattice with ONE new top.  This includes E=Top and the trivial
finite part, and does not assume distributivity or any quotient source. -/
universe v w t z
namespace CCO.FinitePackets.Normalization
open CCO.RealHull.Geometry CCO.ParityHasse.Original

section Order
variable {A : Type z} [PartialOrder A] (H E : A) (hHE : H < E)
variable (hproper : ∀ J : A, J < E → J ≤ H)

def cutTopValue : WithTop (Set.Iic H) → Set.Iic E
  | none => ⟨E,le_rfl⟩
  | some J => ⟨J.val,J.property.trans hHE.le⟩

theorem cutTopValue_injective : Function.Injective (cutTopValue H E hHE) := by
  intro p q hpq
  cases p with
  | top =>
    cases q with
    | top => rfl
    | coe J =>
      have he : E = J.val := congrArg Subtype.val hpq
      exact False.elim (hHE.not_ge (he ▸ J.property))
  | coe J =>
    cases q with
    | top =>
      have he : J.val = E := congrArg Subtype.val hpq
      exact False.elim (hHE.not_ge (he ▸ J.property))
    | coe K =>
      have hv : J.val = K.val := congrArg (fun r : Set.Iic E => r.val) hpq
      exact congrArg (fun r : Set.Iic H => (r : WithTop (Set.Iic H))) (Subtype.ext hv)

include hproper in
theorem cutTopValue_surjective : Function.Surjective (cutTopValue H E hHE) := by
  intro J
  by_cases he : J.val = E
  · exact ⟨none,Subtype.ext he.symm⟩
  · exact ⟨some ⟨J.val,hproper J.val (lt_of_le_of_ne J.property he)⟩,rfl⟩

noncomputable def cutAdjoinTopIso : WithTop (Set.Iic H) ≃o Set.Iic E where
  toEquiv := Equiv.ofBijective (cutTopValue H E hHE)
    ⟨cutTopValue_injective H E hHE,cutTopValue_surjective H E hHE hproper⟩
  map_rel_iff' := by
    intro p q
    cases p with
    | top =>
      cases q with
      | top => exact iff_of_true le_rfl le_rfl
      | coe J =>
        change E ≤ J.val ↔ (⊤ : WithTop (Set.Iic H)) ≤ ↑J
        exact iff_of_false (fun h => hHE.not_ge (h.trans J.property)) (by simp)
    | coe J =>
      cases q with
      | top => exact iff_of_true (J.property.trans hHE.le) le_top
      | coe K =>
        change J.val ≤ K.val ↔ (J : WithTop (Set.Iic H)) ≤ ↑K
        simp only [WithTop.coe_le_coe]
        rfl
end Order

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable (F : ColourEq S ()) {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G) (hthin : ThinBottom S F)
variable (E : ColourEq S ()) (hE : Geometry.MinimalInfiniteCut S E)
variable (hF : Geometry.FiniteBottomSpec S F)

noncomputable def minimalCutSubgroupIso :
    Set.Iic E ≃o WithTop (Subgroup (equivalenceTranslations S F (G := G) (E ⊓ F))) :=
  (cutAdjoinTopIso (E ⊓ F) E (Geometry.cut_finite_part_strict S hE hF)
    (fun J hJ => Geometry.cut_proper_le_finite_part S hE hF hJ)).symm.trans
    ((lowerEquivalenceSubgroupIso S F H hthin (E ⊓ F) inf_le_right).withTopCongr)

end CCO.FinitePackets.Normalization
