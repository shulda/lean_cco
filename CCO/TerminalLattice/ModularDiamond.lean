import Mathlib.Order.ModularLattice

/-!
# B050: local algebraic normalisation of a modular diamond

This proves the **unconditional modular-lattice equalities** underlying
source v27/08 C04–C05. No distributivity criterion or `M₃` theorem is
taken as an oracle, and no source CCO/SAP hypothesis is used.

The predicates are ordinary lattice operations; to obtain the ORIGINAL
source instance use the accepted `ColourEq.modular` with the ambient
homogeneous source group in `OriginalModularity.lean`.
-/

universe u

namespace CCO.TerminalLattice

variable {L : Type u} [Lattice L] [IsModularLattice L]

/-- Dedekind's modular law twice yields this symmetric three-element
identity. It is false for arbitrary nonmodular lattices and is the
calculation used in the source's normalised M₃ extraction. -/
theorem modular_pairwise_sup_inf (a b c : L) :
    (a ⊔ (b ⊓ c)) ⊓ (b ⊔ (a ⊓ c)) =
      (a ⊓ b) ⊔ (a ⊓ c) ⊔ (b ⊓ c) := by
  have hAC : a ⊓ c ≤ a ⊔ (b ⊓ c) :=
    le_trans inf_le_left le_sup_left
  have hBC : b ⊓ c ≤ b := inf_le_left
  calc
    (a ⊔ (b ⊓ c)) ⊓ (b ⊔ (a ⊓ c)) =
        ((a ⊓ c) ⊔ b) ⊓ (a ⊔ (b ⊓ c)) := by rw [sup_comm b, inf_comm]
    _ = (a ⊓ c) ⊔ (b ⊓ (a ⊔ (b ⊓ c))) :=
        sup_inf_assoc_of_le b hAC
    _ = (a ⊓ c) ⊔ ((b ⊓ a) ⊔ (b ⊓ c)) := by
        rw [inf_sup_assoc_of_le a hBC]
    _ = (a ⊓ b) ⊔ (a ⊓ c) ⊔ (b ⊓ c) := by
        rw [inf_comm b a]
        ac_rfl

/-- The exact order dual of the previous calculation. -/
theorem modular_pairwise_inf_sup (a b c : L) :
    (a ⊓ (b ⊔ c)) ⊔ (b ⊓ (a ⊔ c)) =
      (a ⊔ b) ⊓ (a ⊔ c) ⊓ (b ⊔ c) := by
  exact modular_pairwise_sup_inf (L := OrderDual L) a b c

end CCO.TerminalLattice
