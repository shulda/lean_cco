import CCO.TerminalLattice.ModularDiamond

/-!
# B050 C04–C05: the normalised modular median interval

All computations are INTERNAL elementary modular-lattice arguments.
No distributivity, CCO, SAP, NR2, original source API or hidden
normalisation lemma is assumed. These pure lattice lemmas feed the
original FULL invariant-equivalence source instance, but are not that
instance by themselves.
-/

universe u

namespace CCO.TerminalLattice

variable {L : Type u} [Lattice L] [IsModularLattice L]

/-- The lower normalised modular median. -/
def modularLower (a b c : L) : L :=
  (a ⊓ b) ⊔ (a ⊓ c) ⊔ (b ⊓ c)

/-- The upper normalised modular median. -/
def modularUpper (a b c : L) : L :=
  (a ⊔ b) ⊓ (a ⊔ c) ⊓ (b ⊔ c)

def modularMiddle (l h a : L) : L :=
  (a ⊔ l) ⊓ h

theorem modularLower_swap (a b c : L) :
    modularLower a b c = modularLower b a c := by
  unfold modularLower
  ac_rfl

theorem modularUpper_swap (a b c : L) :
    modularUpper a b c = modularUpper b a c := by
  unfold modularUpper
  ac_rfl

/-- The lower median is below the upper median even in an arbitrary
lattice. The current modular typeclass is only used downstream. -/
theorem modularLower_le_upper (a b c : L) :
    modularLower a b c ≤ modularUpper a b c := by
  unfold modularLower modularUpper
  refine le_inf (le_inf ?_ ?_) ?_
  · refine sup_le (sup_le ?_ ?_) ?_
    · exact (inf_le_left : a ⊓ b ≤ a).trans le_sup_left
    · exact (inf_le_left : a ⊓ c ≤ a).trans le_sup_left
    · exact (inf_le_left : b ⊓ c ≤ b).trans le_sup_right
  · refine sup_le (sup_le ?_ ?_) ?_
    · exact (inf_le_left : a ⊓ b ≤ a).trans le_sup_left
    · exact (inf_le_left : a ⊓ c ≤ a).trans le_sup_left
    · exact (inf_le_right : b ⊓ c ≤ c).trans le_sup_right
  · refine sup_le (sup_le ?_ ?_) ?_
    · exact (inf_le_right : a ⊓ b ≤ b).trans le_sup_left
    · exact (inf_le_right : a ⊓ c ≤ c).trans le_sup_right
    · exact (inf_le_left : b ⊓ c ≤ b).trans le_sup_left

/-- Absorption of the two pair-meets involving a. -/
theorem sup_modularLower (a b c : L) :
    a ⊔ modularLower a b c = a ⊔ (b ⊓ c) := by
  apply le_antisymm
  · apply sup_le le_sup_left
    unfold modularLower
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (inf_le_left : a ⊓ b ≤ a).trans le_sup_left
    · exact (inf_le_left : a ⊓ c ≤ a).trans le_sup_left
    · exact le_sup_right
  · apply sup_le le_sup_left
    exact (le_sup_right : b ⊓ c ≤ modularLower a b c).trans le_sup_right

/-- Exact order-dual absorption for the upper median. -/
theorem inf_modularUpper (a b c : L) :
    a ⊓ modularUpper a b c = a ⊓ (b ⊔ c) := by
  exact sup_modularLower (L := OrderDual L) a b c

/-- C04 pairwise normalisation: for any modular triple, the two
normalised elements have EXACT common lower and upper medians.
The proof is Dedekind's law, not distributivity. -/
theorem modular_normalized_pair (a b c : L) :
    (modularMiddle (modularLower a b c) (modularUpper a b c) a ⊓
      modularMiddle (modularLower a b c) (modularUpper a b c) b =
      modularLower a b c) ∧
    (modularMiddle (modularLower a b c) (modularUpper a b c) a ⊔
      modularMiddle (modularLower a b c) (modularUpper a b c) b =
      modularUpper a b c) := by
  let l := modularLower a b c
  let h := modularUpper a b c
  change (((a ⊔ l) ⊓ h) ⊓ ((b ⊔ l) ⊓ h) = l) ∧
    (((a ⊔ l) ⊓ h) ⊔ ((b ⊔ l) ⊓ h) = h)
  have hlh : l ≤ h := modularLower_le_upper a b c
  have haSup : a ⊔ l = a ⊔ (b ⊓ c) := sup_modularLower a b c
  have hbSup : b ⊔ l = b ⊔ (a ⊓ c) := by
    change b ⊔ modularLower a b c = b ⊔ (a ⊓ c)
    rw [modularLower_swap a b c]
    exact sup_modularLower b a c
  have haInf : a ⊓ h = a ⊓ (b ⊔ c) := inf_modularUpper a b c
  have hbInf : b ⊓ h = b ⊓ (a ⊔ c) := by
    change b ⊓ modularUpper a b c = b ⊓ (a ⊔ c)
    rw [modularUpper_swap a b c]
    exact inf_modularUpper b a c
  have hMiddleA : (a ⊔ l) ⊓ h = (a ⊓ h) ⊔ l := by
    calc
      (a ⊔ l) ⊓ h = (l ⊔ a) ⊓ h := by ac_rfl
      _ = l ⊔ (a ⊓ h) := sup_inf_assoc_of_le a hlh
      _ = (a ⊓ h) ⊔ l := by ac_rfl
  have hMiddleB : (b ⊔ l) ⊓ h = (b ⊓ h) ⊔ l := by
    calc
      (b ⊔ l) ⊓ h = (l ⊔ b) ⊓ h := by ac_rfl
      _ = l ⊔ (b ⊓ h) := sup_inf_assoc_of_le b hlh
      _ = (b ⊓ h) ⊔ l := by ac_rfl
  constructor
  · calc
      ((a ⊔ l) ⊓ h) ⊓ ((b ⊔ l) ⊓ h) =
          ((a ⊔ l) ⊓ (b ⊔ l)) ⊓ h := by ac_rfl
      _ = ((a ⊔ (b ⊓ c)) ⊓ (b ⊔ (a ⊓ c))) ⊓ h := by rw [haSup, hbSup]
      _ = l ⊓ h := by rw [modular_pairwise_sup_inf a b c]; rfl
      _ = l := inf_of_le_left hlh
  · calc
      ((a ⊔ l) ⊓ h) ⊔ ((b ⊔ l) ⊓ h) =
          ((a ⊓ h) ⊔ l) ⊔ ((b ⊓ h) ⊔ l) := by rw [hMiddleA, hMiddleB]
      _ = ((a ⊓ h) ⊔ (b ⊓ h)) ⊔ l := by ac_rfl
      _ = ((a ⊓ (b ⊔ c)) ⊔ (b ⊓ (a ⊔ c))) ⊔ l := by rw [haInf, hbInf]
      _ = h ⊔ l := by rw [modular_pairwise_inf_sup a b c]; rfl
      _ = h := sup_eq_left.mpr hlh

/-- The same lower and upper medians simultaneously work for ALL
three cyclic normalisations, rather than three unrelated diamonds. -/
theorem modular_normalized_triple (a b c : L) :
    let l := modularLower a b c
    let h := modularUpper a b c
    let A := modularMiddle l h a
    let B := modularMiddle l h b
    let C := modularMiddle l h c
    A ⊓ B = l ∧ A ⊓ C = l ∧ B ⊓ C = l ∧
    A ⊔ B = h ∧ A ⊔ C = h ∧ B ⊔ C = h := by
  have hpAB := modular_normalized_pair a b c
  have hpAC := modular_normalized_pair a c b
  have hpBC := modular_normalized_pair b c a
  have loAC : modularLower a c b = modularLower a b c := by
    unfold modularLower; ac_rfl
  have hiAC : modularUpper a c b = modularUpper a b c := by
    unfold modularUpper; ac_rfl
  have loBC : modularLower b c a = modularLower a b c := by
    unfold modularLower; ac_rfl
  have hiBC : modularUpper b c a = modularUpper a b c := by
    unfold modularUpper; ac_rfl
  rw [loAC, hiAC] at hpAC
  rw [loBC, hiBC] at hpBC
  exact ⟨hpAB.1, hpAC.1, hpBC.1, hpAB.2, hpAC.2, hpBC.2⟩

end CCO.TerminalLattice
