import CCO.TerminalLattice.ModularNormalization
import CCO.TerminalLattice.M3CCOObstruction

/-!
# B050 C05/C09: extract an original M₃ from FULL invariant nondistributivity

The pure modular-lattice construction first supplies a strict lower/upper
interval and an actual normalized interior element. Combining this with
the six proved pairwise median equations produces the THREE original
equivalences required by the source's M₃ obstruction.

The source consumer explicitly requires FULL original NR2 ONLY to obtain
the original RAW words via accepted B011. No SAP, CCO, exact-lattice
distributivity, or previously assumed M₃ is used.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {L : Type u} [Lattice L] [IsModularLattice L]

/-- The extra meet b ⊓ c cannot enlarge the intersection with a:
this step uses only the modular Dedekind law, not distributivity. -/
theorem inf_modularLower (a b c : L) :
    a ⊓ modularLower a b c = (a ⊓ b) ⊔ (a ⊓ c) := by
  let d : L := (a ⊓ b) ⊔ (a ⊓ c)
  have hd : d ≤ a := sup_le inf_le_left inf_le_left
  have hExtra : (b ⊓ c) ⊓ a ≤ d := by
    have h : (b ⊓ c) ⊓ a ≤ a ⊓ b := by
      apply le_inf
      · exact inf_le_right
      · exact (inf_le_left : (b ⊓ c) ⊓ a ≤ b ⊓ c).trans inf_le_left
    exact h.trans le_sup_left
  calc
    a ⊓ modularLower a b c = (d ⊔ (b ⊓ c)) ⊓ a := by rw [inf_comm]; rfl
    _ = d ⊔ ((b ⊓ c) ⊓ a) := sup_inf_assoc_of_le (b ⊓ c) hd
    _ = d := sup_eq_left.mpr hExtra

/-- Genuine failure of one distributive inequality forces the
normalised modular lower/upper medians to be STRICTLY different. -/
theorem modularLower_lt_upper_of_nondistrib (a b c : L)
    (hND : ¬ a ⊓ (b ⊔ c) ≤ (a ⊓ b) ⊔ (a ⊓ c)) :
    modularLower a b c < modularUpper a b c := by
  refine lt_of_le_of_ne (modularLower_le_upper a b c) ?_
  intro hEq
  have hFalse : a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) := by
    calc
      a ⊓ (b ⊔ c) = a ⊓ modularUpper a b c :=
        (inf_modularUpper a b c).symm
      _ = a ⊓ modularLower a b c := by rw [hEq]
      _ = (a ⊓ b) ⊔ (a ⊓ c) := inf_modularLower a b c
  exact hND (le_of_eq hFalse)

/-- The first normalized modular element is a genuine INTERIOR point,
so the three paired relations yield an actual nondegenerate M₃, not
an identity/Top collapse. -/
theorem modularLower_lt_normalized_of_nondistrib (a b c : L)
    (hND : ¬ a ⊓ (b ⊔ c) ≤ (a ⊓ b) ⊔ (a ⊓ c)) :
    modularLower a b c <
      modularMiddle (modularLower a b c) (modularUpper a b c) a := by
  let l := modularLower a b c
  let h := modularUpper a b c
  let A := modularMiddle l h a
  let B := modularMiddle l h b
  let C := modularMiddle l h c
  have hlt : l < h := modularLower_lt_upper_of_nondistrib a b c hND
  have hleA : l ≤ A := by
    change l ≤ (a ⊔ l) ⊓ h
    exact le_inf le_sup_right hlt.le
  have hleB : l ≤ B := by
    change l ≤ (b ⊔ l) ⊓ h
    exact le_inf le_sup_right hlt.le
  have hleC : l ≤ C := by
    change l ≤ (c ⊔ l) ⊓ h
    exact le_inf le_sup_right hlt.le
  have hp := modular_normalized_triple a b c
  change (A ⊓ B = l) ∧ (A ⊓ C = l) ∧ (B ⊓ C = l) ∧
    (A ⊔ B = h) ∧ (A ⊔ C = h) ∧ (B ⊔ C = h) at hp
  rcases hp with ⟨_hMeetAB, _hMeetAC, hMeetBC, hJoinAB, hJoinAC, _hJoinBC⟩
  have hAne : A ≠ l := by
    intro hA
    have hB : B = h := by
      calc
        B = l ⊔ B := (sup_of_le_left hleB).symm
        _ = A ⊔ B := by rw [hA]
        _ = h := hJoinAB
    have hC : C = h := by
      calc
        C = l ⊔ C := (sup_of_le_left hleC).symm
        _ = A ⊔ C := by rw [hA]
        _ = h := hJoinAC
    have hEq : l = h := by
      calc
        l = B ⊓ C := hMeetBC.symm
        _ = h := by rw [hB, hC, inf_idem]
    exact (ne_of_lt hlt) hEq
  exact lt_of_le_of_ne hleA (Ne.symm hAne)

end CCO.TerminalLattice

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- Nondistributivity of the FULL original invariant equivalences,
expressed by failure of the distributive inequality. This does not
refer to an exact sublattice or a generated abstract M₃. -/
def FullInvariantNondistributive (H : HomogeneousSource S G) (i : ι) : Prop := by
  letI := ColourEq.lattice S H (i := i)
  exact ¬ ∀ a b c : ColourEq S i,
    a ⊓ (b ⊔ c) ≤ (a ⊓ b) ⊔ (a ⊓ c)

/-- Source corollary `cor:typed-terminal-nondistributive-noncco`:
under the original full NO-RELATIVE-INDEX-TWO premise, a
nondistributive full invariant-equivalence lattice gives a genuine
RAW-word original M₃ and hence an original CCO obstruction.

No SAP is assumed. The only CCO premise ever used is the *temporary
contradictory* CCO in the already-proved B002 private-fan reduction,
not the B011 terminal distributivity conclusion. -/
theorem terminal_nondistributive_forbid_CCO
    (H : HomogeneousSource S G) {i : ι}
    (nr2 : RealClosure.Bounds.SortNR2 S i)
    (hND : FullInvariantNondistributive S H i) :
    ¬ SemanticCCO.{u,v,max u v,w} S := by
  classical
  letI : Lattice (ColourEq S i) := ColourEq.lattice S H
  letI : IsModularLattice (ColourEq S i) := ColourEq.modular S H
  change ¬ ∀ a b c : ColourEq S i,
    a ⊓ (b ⊔ c) ≤ (a ⊓ b) ⊔ (a ⊓ c) at hND
  have hwitness : ∃ a b c : ColourEq S i,
      ¬ a ⊓ (b ⊔ c) ≤ (a ⊓ b) ⊔ (a ⊓ c) := by
    by_contra hnone
    apply hND
    intro a b c
    by_contra habc
    exact hnone ⟨a, b, c, habc⟩
  obtain ⟨a, b, c, hFail⟩ := hwitness
  let l := modularLower a b c
  let h := modularUpper a b c
  let E₁ := modularMiddle l h a
  let E₂ := modularMiddle l h b
  let E₃ := modularMiddle l h c
  have hp := modular_normalized_triple a b c
  change (E₁ ⊓ E₂ = l) ∧ (E₁ ⊓ E₃ = l) ∧
    (E₂ ⊓ E₃ = l) ∧ (E₁ ⊔ E₂ = h) ∧
    (E₁ ⊔ E₃ = h) ∧ (E₂ ⊔ E₃ = h) at hp
  rcases hp with ⟨hm12, hm13, _hm23, hj12, _hj13, hj23⟩
  have hProper : l < E₁ :=
    modularLower_lt_normalized_of_nondistrib a b c hFail
  have hJ12 : ColourEq.join S H E₁ E₂ = h := by
    change E₁ ⊔ E₂ = h
    exact hj12
  have hJ23 : ColourEq.join S H E₂ E₃ = h := by
    change E₂ ⊔ E₃ = h
    exact hj23
  exact original_m3_forbid_CCO_of_NR2 S H nr2 E₁ E₂ E₃ l h
    hm12 hm13 hJ12 hJ23 hProper

end CCO.TerminalLattice
