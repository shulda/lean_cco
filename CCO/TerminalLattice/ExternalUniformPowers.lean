import CCO.TerminalLattice.OriginalExternalWords
import CCO.TerminalLattice.FullCoverUniformPowers

/-!
# B050 C31: ONE eventual full STRONG power bound for ALL finite old labels

The finite family is indexed by original K-external OLD fine atoms,
not quotient-reduct automorphisms.  Every represented complete orbital
has its individual pure-power threshold from the already compiled
FULL original cover theorem.  A literal finite supremum yields one N
working simultaneously for all labels, including duplicate orbitals.
No CCO, global NR2, exactness, B049 or unproved provider appears.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- Source C31 common positive threshold for the CCO-free FULL-cover
quotient-orbital power theorem, indexed by the ACTUAL finite original
external labels.  The local index-two exclusion is asserted at ONE
old anchor, and moved to each old label representative by original
sort-transitive homogeneous relative-index uniformity. -/
theorem originalIndexedExternalOrbitalMenus_uniform_powers
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J K : ColourEq S i)
    (hJK : J ⋖ K) (hJ : (⊥ : ColourEq S i) < J)
    (anchor : X i)
    (hNotTwo : relativeIndex J.val K.val anchor ≠ 2) :
    ∃ N : Nat, 0 < N ∧
      ∀ j : Fin (Fintype.card (OriginalExternalAtom S J K)),
        ∀ n : Nat, N ≤ n →
          originalStrongPalettePower S
            (originalIndexedExternalOrbitalMenus S (G := G) J K j) (n-1) =
            originalEquivDiversityPalette S K := by
  classical
  let r := Fintype.card (OriginalExternalAtom S J K)
  have hEach : ∀ j : Fin r, ∃ n₀ : Nat, 0 < n₀ ∧
      ∀ n : Nat, n₀ ≤ n →
        originalStrongPalettePower S
          (originalIndexedExternalOrbitalMenus S (G := G) J K j) (n-1) =
            originalEquivDiversityPalette S K := by
    intro j
    let c : OriginalExternalAtom S J K :=
      (Fintype.equivFin (OriginalExternalAtom S J K)).symm j
    let p := originalExternalAtomWitness S J K c
    have hIndex :
        relativeIndex J.val K.val p.val.1 =
        relativeIndex J.val K.val anchor :=
      relativeIndex_uniform S H J K p.val.1 anchor
    have hNotTwoP :
        relativeIndex J.val K.val p.val.1 ≠ 2 := by
      intro hTwo
      exact hNotTwo (hIndex.symm.trans hTwo)
    change ∃ n₀ : Nat, 0 < n₀ ∧
      ∀ n : Nat, n₀ ≤ n →
        originalStrongPalettePower S
          (originalQuotientOrbitalPalette S (G := G) J
            p.val.1 p.val.2) (n-1) =
          originalEquivDiversityPalette S K
    exact originalQuotient_uniform_strong_palette_powers
      S H sap J K hJK hJ
        p.val.1 p.val.2 p.property.1 p.property.2.1 hNotTwoP
  choose threshold hThreshold using hEach
  let N : Nat := max 1
    ((Finset.univ : Finset (Fin r)).sup threshold)
  refine ⟨N, ?_, ?_⟩
  · dsimp [N]
    omega
  · intro j n hn
    have hSup : threshold j ≤
        (Finset.univ : Finset (Fin r)).sup threshold :=
      Finset.le_sup (by simp)
    have hjN : threshold j ≤ N :=
      hSup.trans (le_max_right _ _)
    exact (hThreshold j).2 n (hjN.trans hn)

end CCO.TerminalLattice
