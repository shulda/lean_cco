import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# B062 / C34–C37: largest-lift order core

For a finite EXACT-equivalence lattice, the source C29/C30 restriction
preserves bottom and binary joins, hence all existing sups. Its right
adjoint is the join of precisely the old exact relations whose trace is
BELOW the current relation. With source C33 surjectivity this is the
largest old exact lift in the E2 fiber, and E3 is its genuine adjunction.

This is an abstract independently proved order-theoretic bridge. The
source-specific exact-equivalence lattice, restriction homomorphism,
surjectivity and original/current tower instantiation are NOT asserted
here and remain explicitly open under B062 C23–C33. In particular,
this never declares all invariant equivalences exact.
-/

universe u v

namespace CCO.ExactEPGeometry.LargestLift

variable {Old : Type u} {Current : Type v}
variable [CompleteLattice Old] [CompleteLattice Current]

/-- Candidate canonical largest old lift, using ONLY the order of the old
exact-equivalence lattice and a monotone restriction map. -/
noncomputable def largestLift (rho : Old →o Current) (F : Current) : Old :=
  sSup {E : Old | rho E ≤ F}

/-- Full-sup preservation of restriction is sufficient for the E3
adjunction; no original equivalence outside the supplied lattice enters. -/
theorem adjunction (rho : Old →o Current)
    (hSup : ∀ s : Set Old, rho (sSup s) = sSup (rho '' s))
    (E : Old) (F : Current) :
    rho E ≤ F ↔ E ≤ largestLift rho F := by
  constructor
  · intro h
    exact le_sSup h
  · intro h
    calc
      rho E ≤ rho (largestLift rho F) := rho.monotone h
      _ = sSup (rho '' {x : Old | rho x ≤ F}) := hSup _
      _ ≤ F := by
        apply sSup_le
        rintro y ⟨x, hx, rfl⟩
        exact hx

/-- E2 in source strength: if the original exact restriction is
surjective, the canonical largest lift REALLY maps to the requested F. -/
theorem largestLift_maps_to (rho : Old →o Current)
    (hSup : ∀ s : Set Old, rho (sSup s) = sSup (rho '' s))
    (hSurj : Function.Surjective rho) (F : Current) :
    rho (largestLift rho F) = F := by
  apply le_antisymm
  · exact (adjunction rho hSup (largestLift rho F) F).mpr le_rfl
  · obtain ⟨E, hE⟩ := hSurj F
    calc
      F = rho E := hE.symm
      _ ≤ rho (largestLift rho F) :=
        rho.monotone ((adjunction rho hSup E F).mp (le_of_eq hE))

/-- The canonical lift really dominates EVERY old exact relation with
that trace, not merely an arbitrarily chosen preimage. -/
theorem largestLift_dominates_fiber (rho : Old →o Current)
    (hSup : ∀ s : Set Old, rho (sSup s) = sSup (rho '' s))
    (E : Old) (F : Current) (h : rho E = F) :
    E ≤ largestLift rho F :=
  (adjunction rho hSup E F).mp (le_of_eq h)

/-- The right adjoint preserves binary meets. This is equality in the
OLD exact-equivalence lattice, with no full invariant lattice claim. -/
theorem largestLift_inf (rho : Old →o Current)
    (hSup : ∀ s : Set Old, rho (sSup s) = sSup (rho '' s))
    (F K : Current) :
    largestLift rho (F ⊓ K) = largestLift rho F ⊓ largestLift rho K := by
  apply le_antisymm
  · apply le_inf
    · apply (adjunction rho hSup _ F).mp
      exact ((adjunction rho hSup _ (F ⊓ K)).mpr le_rfl).trans inf_le_left
    · apply (adjunction rho hSup _ K).mp
      exact ((adjunction rho hSup _ (F ⊓ K)).mpr le_rfl).trans inf_le_right
  · apply (adjunction rho hSup _ (F ⊓ K)).mp
    apply le_inf
    · exact (adjunction rho hSup _ F).mpr inf_le_left
    · exact (adjunction rho hSup _ K).mpr inf_le_right

/-- Empty-meet convention: the canonical old lift of current Top is
ACTUAL old Top, not old identity. -/
theorem largestLift_top (rho : Old →o Current)
    (hSup : ∀ s : Set Old, rho (sSup s) = sSup (rho '' s)) :
    largestLift rho ⊤ = ⊤ := by
  apply top_unique
  exact (adjunction rho hSup ⊤ ⊤).mp le_top

/-- All small meets commute with the right adjoint, including the
empty meet. The binary E3 calculation is not limited to two factors. -/
theorem largestLift_sInf (rho : Old →o Current)
    (hSup : ∀ s : Set Old, rho (sSup s) = sSup (rho '' s))
    (s : Set Current) :
    largestLift rho (sInf s) = sInf (largestLift rho '' s) := by
  apply le_antisymm
  · apply le_sInf
    rintro x ⟨F, hF, rfl⟩
    apply (adjunction rho hSup _ F).mp
    exact ((adjunction rho hSup _ (sInf s)).mpr le_rfl).trans (sInf_le hF)
  · apply (adjunction rho hSup _ (sInf s)).mp
    apply le_sInf
    intro F hF
    apply (adjunction rho hSup _ F).mpr
    exact sInf_le ⟨F,hF,rfl⟩

/-- For a finite original exact-equivalence lattice, preserving only
bottom and binary joins already implies full-set Sup preservation.
No extra source hypothesis beyond C29/C30 is required. -/
theorem preserves_sSup_of_finite
    [Finite Old] (rho : Old →o Current)
    (hBot : rho ⊥ = ⊥)
    (hJoin : ∀ E K : Old, rho (E ⊔ K) = rho E ⊔ rho K) :
    ∀ s : Set Old, rho (sSup s) = sSup (rho '' s) := by
  classical
  intro s
  have hs : s.Finite := Set.toFinite s
  induction hs using Set.Finite.induction_on with
  | empty =>
      simpa only [sSup_empty, Set.image_empty] using hBot
  | @insert E s hnot hfin ih =>
      simp only [sSup_insert, Set.image_insert, hJoin, ih]

/-- Source C34/C35 order core under EXACTLY finite-lattice restrictions,
with only C29 bottom/C30 joins/C33 surjectivity left to instantiate. -/
theorem finite_exact_fiber_adjoint
    [Finite Old] (rho : Old →o Current)
    (hBot : rho ⊥ = ⊥)
    (hJoin : ∀ E K : Old, rho (E ⊔ K) = rho E ⊔ rho K)
    (hSurj : Function.Surjective rho)
    (F : Current) :
    rho (largestLift rho F) = F ∧
      ∀ E : Old, rho E ≤ F ↔ E ≤ largestLift rho F := by
  have hSup := preserves_sSup_of_finite rho hBot hJoin
  exact ⟨largestLift_maps_to rho hSup hSurj F,
    fun E => adjunction rho hSup E F⟩

end CCO.ExactEPGeometry.LargestLift
