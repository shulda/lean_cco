import CCO.TerminalLattice.SparseNoCentreCycleSpectrum
import CCO.TerminalLattice.PositiveFiniteChain
import CCO.TerminalLattice.ProjectedOrientedWords

/-!
# B050 C27/C33: EVERY actual sparse OLD private-word cycle has a homomorphism

The source C27 incidence analysis has now been carried out on the ONE
actual finite private OLD diagram built from a genuine B006 sparse
labelled graph and one last centre. There are only two cases for an
ACTUAL B002 compressed marked simple cycle:

* it visits the centre, so the real positive K-diversity spoke among
  the first n edges absorbs all the other nonempty old K-menus;
* it avoids the centre, so the literal ordered W graph cycle is long
  by actual girth, its real edge labels have a frequent occurrence,
  and their full old-group external menu powers saturate K-diversity.

Both cases establish the exact old STRONG spectrum of the first n
ordered, ORIENTED words. An actual nonempty closing OLD positive word
then gives one simultaneous real valuation for ALL marked roots.
The accepted B002 private-path constructor extends that valuation
to a genuine homomorphism of the ENTIRE raw simple cycle, including
all named-sort private interiors.

This is cycle-BY-cycle feasibility, NOT a fictitious global CCO
homomorphism, nor the original reset C40. It does not use original
CCO, quotient SAP, NR2 or any invented labelled skeleton.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- Literal C27/C33 receiving theorem for any B002 marked projection
of a true original sparse one-word-path diagram. Every hypothesis
is a real original source property, genuine sparse girth, exact
chosen positive old words, or already established full-cover powers.
There is NO assumption of a ready root assignment or a cycle map. -/
theorem oldSparseWordDiagram_projected_cycleHom
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g N : Nat}
    (K : ColourEq S i)
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (menus : Fin r → S.Menu i i)
    (hSpoke : PositiveWord.profile S spoke =
      originalEquivDiversityPalette S K)
    (hWords : ∀ j : Fin r,
      PositiveWord.profile S (words j) = menus j)
    (hMenus : ∀ j : Fin r,
      (menus j).Nonempty ∧
      menus j ⊆ originalEquivDiversityPalette S K)
    (hPowers : ∀ j : Fin r,
      originalStrongPalettePower S (menus j) (N-1) =
        originalEquivDiversityPalette S K)
    (hN : 0 < N)
    (hGirth : r * (N-1) + 1 ≤ g)
    (C : SimpleCycle (oldSparseWordDiagram S H sap W spoke words))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin (W.size+1) => i)
      (oldOptionalPositivePresentations S
        (oldSparseWordSelection S W spoke words))
      (oldOptionalPositivePresentations_nonempty S H sap
        (oldSparseWordSelection S W spoke words)) C) :
    CycleHom C := by
  classical
  let n : Nat := B.length - 1
  have hLength : B.length = n+1 := by
    dsimp [n]
    have hThree := B.length_ge_three
    omega
  have hn : 0 < n := by
    dsimp [n]
    have hThree := B.length_ge_three
    omega
  let branches : Fin (n+1) → PositiveWord S i i :=
    fun k => oldProjectedOrientedWord S H sap
      (oldSparseWordSelection S W spoke words) C B
      (Fin.cast hLength.symm k)
  have hSpectrum :
      originalPositiveStrongPath S
        ((List.ofFn (fun k : Fin n => branches k.castSucc)).map
          (PositiveWord.profile S)) =
        some (originalEquivDiversityPalette S K) := by
    by_cases hCentre : ∃ p : Fin B.length,
        B.vertices p = oldSparseCentre W
    · simpa only [branches] using
        (oldSparseWordDiagram_centre_complement_saturates
          S H sap K W spoke words hSpoke menus
          hMenus hWords C B hLength hCentre)
    · have hNoCentre : ∀ p : Fin B.length,
          B.vertices p ≠ oldSparseCentre W := by
        intro p hp
        exact hCentre ⟨p,hp⟩
      simpa only [branches] using
        (oldSparseWordDiagram_centre_free_complement_saturates
          S H sap K W spoke words menus hWords
          hMenus hPowers hN hGirth C B hLength hNoCentre)
  let closing : PositiveWord S i i := branches (Fin.last n)
  let D : S.Menu i i := PositiveWord.profile S closing
  have hD : D.Nonempty ∧
      D ⊆ originalEquivDiversityPalette S K := by
    exact oldSparseWordDiagram_oriented_profile_valid
      S H sap K W spoke words hSpoke menus hMenus hWords C B
      (Fin.cast hLength.symm (Fin.last n))
  obtain ⟨values,hValues⟩ :=
    original_saturated_positive_cyclic_values
      S H sap K hn branches D hD.1 hD.2 Set.Subset.rfl hSpectrum
  let b : Fin B.length → X i :=
    fun k => values (Fin.cast hLength k)
  apply oldOptionalPositive_cycleHom_of_oriented_values
    S H sap (oldSparseWordSelection S W spoke words) C B b
  intro k
  have hIndex :
      Fin.cast hLength.symm (Fin.cast hLength k) = k := Fin.ext rfl
  have hSuccessor :
      Fin.cast hLength (CCO.cyclicNext B.length_pos k) =
        CCO.cyclicNext (Nat.succ_pos n) (Fin.cast hLength k) := by
    apply Fin.ext
    change (k.val + 1) % B.length = (k.val + 1) % (n+1)
    rw [hLength]
  have hReal := hValues (Fin.cast hLength k)
  rw [← hSuccessor] at hReal
  change PositiveWord.represented S
    (oldProjectedOrientedWord S H sap
      (oldSparseWordSelection S W spoke words) C B
      (Fin.cast hLength.symm (Fin.cast hLength k)))
    (values (Fin.cast hLength k))
    (values (Fin.cast hLength (CCO.cyclicNext B.length_pos k))) at hReal
  rw [hIndex] at hReal
  exact hReal

/-- Genuine SOURCE C27/C33, universally for EVERY actual original
simple cycle of the ONE privately expanded sparse-star network.
The B002 one-word-per-pair theorem already guarantees a genuine
three-or-more-root marked projection of each original simple cycle;
there are no unhandled two-path/theta cycles. The preceding concrete
two-case proof discharges the necessary original word-realization.

This is the EXACT cycle-by-cycle premise of original semantic CCO,
NOT global CCO itself, nor source reset C40.
-/
theorem oldSparseWordDiagram_all_cyclesHom
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g N : Nat}
    (K : ColourEq S i)
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (menus : Fin r → S.Menu i i)
    (hSpoke : PositiveWord.profile S spoke =
      originalEquivDiversityPalette S K)
    (hWords : ∀ j : Fin r,
      PositiveWord.profile S (words j) = menus j)
    (hMenus : ∀ j : Fin r,
      (menus j).Nonempty ∧
      menus j ⊆ originalEquivDiversityPalette S K)
    (hPowers : ∀ j : Fin r,
      originalStrongPalettePower S (menus j) (N-1) =
        originalEquivDiversityPalette S K)
    (hN : 0 < N)
    (hGirth : r * (N-1) + 1 ≤ g) :
    ∀ C : SimpleCycle (oldSparseWordDiagram S H sap W spoke words),
      CycleHom C := by
  intro C
  obtain ⟨B⟩ :=
    oldOptionalPositiveDiagram_cycle_has_marked_projection
      S H sap (oldSparseWordSelection S W spoke words) C
  exact oldSparseWordDiagram_projected_cycleHom
    S H sap K W spoke words menus hSpoke hWords hMenus
      hPowers hN hGirth C B

end CCO.TerminalLattice
