import CCO.TerminalLattice.OriginalSparseThetaCentreSpectrum
import CCO.TerminalLattice.OriginalThetaCycleMenuReadout

/-!
# B050 source08 C26–C30: ORIGINAL multi-theta cycle-guard theorem

This module closes the actual pinned lemma
lem:typed-relative-reset-cycle-guard.

The frozen source's finite private theta presentation allows MULTIPLE
OLD positive atomic typed word branches per marked pair; every branch
profile only CONTAINS its assigned fine STRONG menu. The graph is the
actual B006 sparse labelled graph and its real marked private diagram
is constructed by the accepted B002 expansion.

For any simple cycle of THAT ONE finite original partial diagram,
accepted B002 either realizes it inside one two-root theta gadget
or projects it to a true injective cyclic list of original marked
roots. The centre-containing and centre-free source-specific
complementary STRONG path lemmas, each proved WITHOUT original CCO,
give precisely K-diversity after deleting the final edge. One actual
closing fine menu then gives a simultaneous valuation of ALL root
positions, which B002 turns into a genuine homomorphism of the
WHOLE original private atomic simple cycle, with all typed interiors.

This is cycle-by-cycle feasibility, NOT a global completion, not
injectivity of a CCO homomorphism, and not the full original reset.
The graph menu subpalette and positive power hypotheses remain the
true explicit source premises, not inferred from individual words.
No sorry/admit, new axioms, quotient SAP or B049 dependencies.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- Bridge from a genuinely saturated complementary ORIGINAL
STRONG path to ONE cyclic old root valuation on the actual B002
marked projection. The final edge has a real nonempty fine menu
inside K-diversity; ALL other guards are the real original menus.

The cast from the actual B002 length to n+1 does not change the
literal cyclic successor, any edge index or its old fine colour.
-/
theorem originalSparseTheta_projected_cyclic_guard_values
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g n : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (K : ParityHasse.Original.ColourEq S i)
    (hK : (⊥ : ParityHasse.Original.ColourEq S i) < K)
    (spokes : List (PositiveWord S i i))
    (menus : Fin r → S.Menu i i)
    (families : Fin r → List (PositiveWord S i i))
    (hSpec : OriginalSparseThetaBranchSpec S K spokes menus families)
    (hContained : ∀ j : Fin r,
      menus j ⊆ originalEquivDiversityPalette S K)
    (C : SimpleCycle
      (originalSparseThetaDiagram
        S H sap W K hK spokes menus families hSpec))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin (W.size+1) => i)
      (originalThetaPresentations S
        (originalSparseThetaSelection S W spokes families))
      (originalThetaPresentations_nonempty S H sap
        (originalSparseThetaSelection S W spokes families)
        (originalSparseThetaGuard S W K menus)
        (originalSparseTheta_guards_valid
          S W K hK spokes menus families hSpec)) C)
    (hLength : B.length = n+1)
    (hSpectrum : originalPositiveStrongPath S
      (List.ofFn (fun k : Fin n =>
        originalSparseThetaGuard S W K menus
          (B.edges (Fin.cast hLength.symm k.castSucc)))) =
          some (originalEquivDiversityPalette S K)) :
    ∃ values : Fin B.length → X i,
      ∀ k : Fin B.length,
        S.menuRel (originalSparseThetaGuard S W K menus (B.edges k))
          (values k) (values (CCO.cyclicNext B.length_pos k)) := by
  let edge : Fin (n+1) →
      CCO.RawExact.QuotientExpansion.Edge (W.size+1) :=
    fun k => B.edges (Fin.cast hLength.symm k)
  let chosenMenu : Fin (n+1) → S.Menu i i :=
    fun k => originalSparseThetaGuard S W K menus (edge k)
  have hLastPresent :=
    originalTheta_projected_edge_has_branch S H sap
      (originalSparseThetaSelection S W spokes families)
      (originalSparseThetaGuard S W K menus)
      (originalSparseTheta_guards_valid
        S W K hK spokes menus families hSpec)
      C B (Fin.cast hLength.symm (Fin.last n))
  have hLast :
      (chosenMenu (Fin.last n)).Nonempty ∧
      chosenMenu (Fin.last n) ⊆
        originalEquivDiversityPalette S K :=
    originalSparseThetaGuard_present_in_K S W K hK
      spokes menus families hSpec hContained
        (B.edges (Fin.cast hLength.symm (Fin.last n))) hLastPresent
  have hn : 0 < n := by
    have hThree := B.length_ge_three
    omega
  obtain ⟨raw, hRaw⟩ :=
    original_saturated_strong_menu_cyclic_values S H K hn
      chosenMenu (chosenMenu (Fin.last n))
      hLast.1 hLast.2 (Set.Subset.rfl _) hSpectrum
  let values : Fin B.length → X i :=
    fun k => raw (Fin.cast hLength k)
  refine ⟨values, ?_⟩
  intro k
  let k' : Fin (n+1) := Fin.cast hLength k
  have hInverse : Fin.cast hLength.symm k' = k := Fin.ext rfl
  have hMenu :
      chosenMenu k' = originalSparseThetaGuard S W K menus (B.edges k) := by
    change originalSparseThetaGuard S W K menus
      (B.edges (Fin.cast hLength.symm k')) =
      originalSparseThetaGuard S W K menus (B.edges k)
    rw [hInverse]
  have hCyclic :
      Fin.cast hLength (CCO.cyclicNext B.length_pos k) =
        CCO.cyclicNext (Nat.succ_pos n) k' := by
    apply Fin.ext
    change (k.val+1) % B.length = (k.val+1) % (n+1)
    rw [hLength]
  have hActual := hRaw k'
  change S.menuRel
      (originalSparseThetaGuard S W K menus (B.edges k))
      (raw k')
      (raw (Fin.cast hLength (CCO.cyclicNext B.length_pos k)))
  rw [← hMenu, hCyclic]
  exact hActual

/-- THE actual SOURCE08 independent C26–C30 theta-cycle guard.
Every specified simple cycle of ONE original finite multi-branch
private theta network has a colour-preserving homomorphism into
the ORIGINAL homogeneous SAP source, and this construction invokes
NO semantic CCO or global completion.

hContained (T_j ⊆ K-diversity), hPowers (T_j raised to every n>=N)
and the graph girth bound are the exact external mathematical
hypotheses of the frozen source. Branch presentations only have to
contain their assigned fine menu; bare spokes have no occurrences.
-/
theorem originalSparseTheta_cycle_guard
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g N : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (K : ParityHasse.Original.ColourEq S i)
    (hK : (⊥ : ParityHasse.Original.ColourEq S i) < K)
    (spokes : List (PositiveWord S i i))
    (menus : Fin r → S.Menu i i)
    (families : Fin r → List (PositiveWord S i i))
    (hSpec : OriginalSparseThetaBranchSpec S K spokes menus families)
    (hN : 0 < N) (hGirth : r * (N-1) + 1 ≤ g)
    (hContained : ∀ j : Fin r,
      menus j ⊆ originalEquivDiversityPalette S K)
    (hPowers : ∀ j : Fin r,
      originalStrongPalettePower S (menus j) (N-1) =
        originalEquivDiversityPalette S K)
    (C : SimpleCycle
      (originalSparseThetaDiagram
        S H sap W K hK spokes menus families hSpec)) :
    CycleHom C := by
  classical
  let selected := originalSparseThetaSelection S W spokes families
  let guards := originalSparseThetaGuard S W K menus
  let hGuard := originalSparseTheta_guards_valid
    S W K hK spokes menus families hSpec
  rcases originalTheta_cycleHom_or_marked_projection
      S H sap selected guards hGuard C with hSingle | hProjected
  · exact hSingle
  · obtain ⟨B⟩ := hProjected
    let n : Nat := B.length - 1
    have hLength : B.length = n+1 := by
      dsimp [n]
      have hPos := B.length_pos
      omega
    have hSpectrum : originalPositiveStrongPath S
        (List.ofFn (fun k : Fin n =>
          originalSparseThetaGuard S W K menus
            (B.edges (Fin.cast hLength.symm k.castSucc)))) =
        some (originalEquivDiversityPalette S K) := by
      by_cases hCentre : ∃ j : Fin B.length,
          B.vertices j = oldSparseCentre W
      · exact originalSparseTheta_centre_complement_spectrum
          S H sap W K hK spokes menus families hSpec
          hContained C B hLength hCentre
      · have hNoCentre : ∀ j : Fin B.length,
            B.vertices j ≠ oldSparseCentre W := by
          intro j hj
          exact hCentre ⟨j, hj⟩
        exact originalSparseTheta_noCentre_complement_spectrum
          S H sap W K hK spokes menus families hSpec
          hN hGirth hContained hPowers C B hNoCentre hLength
    obtain ⟨values,hValues⟩ :=
      originalSparseTheta_projected_cyclic_guard_values
        S H sap W K hK spokes menus families hSpec
        hContained C B hLength hSpectrum
    exact originalTheta_cycleHom_of_projected_guard_values
      S H sap selected guards hGuard C B values hValues

end CCO.TerminalLattice
