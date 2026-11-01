import CCO.TerminalLattice.OriginalSparseThetaGuardSpectrum

/-!
# B050 source08 C27–C30: actual centre-free multi-theta cycle spectrum

The previous source-faithful B002 compression proves that a projected
cycle avoiding the unique centre is an injective actual W graph cycle.
Here EVERY genuinely used private marked pair has its own real W label
and corresponding original nonempty STRONG guard T_j.

After deleting the arbitrarily chosen final projected edge, the
complementary path still has more than r*(N-1) edges by the true
original W girth bound. The established old SAP same-sort finite
label-power theorem proves its full K-diversity STRONG spectrum.

Individual old private typed branches only need to CONTAIN their
assigned fine menu. No CCO, quotient SAP, new source axiom or
arbitrary edge-label oracle is used.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- A REAL projected edge of a centre-free old MULTI-THETA cycle
has guard equal to one actually indexed W label menu T_j. The
family cannot be empty because B002 compression retains a true
original word occurrence; the edge cannot be a spoke because
B002's cyclic endpoints both avoid the unique centre. -/
theorem originalSparseTheta_noCentre_edge_guard_label
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (K : ParityHasse.Original.ColourEq S i)
    (hK : (⊥ : ParityHasse.Original.ColourEq S i) < K)
    (spokes : List (PositiveWord S i i))
    (menus : Fin r → S.Menu i i)
    (families : Fin r → List (PositiveWord S i i))
    (hSpec : OriginalSparseThetaBranchSpec S K spokes menus families)
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
    (hNoCentre : ∀ j : Fin B.length,
      B.vertices j ≠ oldSparseCentre W)
    (k : Fin B.length) :
    ∃ j : Fin r,
      originalSparseThetaGuard S W K menus (B.edges k) = menus j := by
  have hPresent :=
    originalTheta_projected_edge_has_branch S H sap
      (originalSparseThetaSelection S W spokes families)
      (originalSparseThetaGuard S W K menus)
      (originalSparseTheta_guards_valid
        S W K hK spokes menus families hSpec) C B k
  have hNotCentre : (B.edges k).val.2.val ≠ W.size := by
    intro hCentre
    have hRight :
        CCO.RawExact.QuotientExpansion.right (B.edges k) =
          oldSparseCentre W := by
      apply Fin.ext
      simpa [CCO.RawExact.QuotientExpansion.right, oldSparseCentre] using hCentre
    rcases B.endpoints k with ⟨_,hEnd⟩ | ⟨hStart,_⟩
    · exact hNoCentre (CCO.cyclicNext B.length_pos k) (hEnd.trans hRight)
    · exact hNoCentre k (hStart.trans hRight)
  exact originalSparseThetaGuard_present_graph S
    W K spokes menus families (B.edges k) hPresent hNotCentre

/-- The original C29 complementary path of an ACTUAL centre-free
B002 multi-theta projection has full OLD K-diversity STRONG spectrum.
The last cyclic edge is simply omitted: the true girth inequality
makes EVERY such deletion admissible, and the remaining ordered
labels still contain N copies of some original index.

hContained and hPowers are precisely the frozen source assumptions;
neither follows from the private branches' positive-profile inclusions.
-/
theorem originalSparseTheta_noCentre_complement_spectrum
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g N n : Nat}
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
    (hNoCentre : ∀ j : Fin B.length,
      B.vertices j ≠ oldSparseCentre W)
    (hLength : B.length = n+1) :
    originalPositiveStrongPath S
      (List.ofFn (fun k : Fin n =>
        originalSparseThetaGuard S W K menus
          (B.edges (Fin.cast hLength.symm k.castSucc)))) =
      some (originalEquivDiversityPalette S K) := by
  classical
  let E : Fin (n+1) →
      CCO.RawExact.QuotientExpansion.Edge (W.size+1) :=
    fun k => B.edges (Fin.cast hLength.symm k)
  have hLabelEach (k : Fin n) :
      ∃ j : Fin r,
        originalSparseThetaGuard S W K menus (E k.castSucc) =
          menus j :=
    originalSparseTheta_noCentre_edge_guard_label S H sap
      W K hK spokes menus families hSpec C B hNoCentre
      (Fin.cast hLength.symm k.castSucc)
  let labels : Fin n → Fin r := fun k => Classical.choose (hLabelEach k)
  have hLabel (k : Fin n) :
      originalSparseThetaGuard S W K menus (E k.castSucc) =
        menus (labels k) :=
    Classical.choose_spec (hLabelEach k)
  have hList :
      List.ofFn (fun k : Fin n =>
        originalSparseThetaGuard S W K menus (E k.castSucc)) =
        (List.ofFn labels).map menus := by
    have hFunction :
        (fun k : Fin n =>
          originalSparseThetaGuard S W K menus (E k.castSucc)) =
          (fun k : Fin n => menus (labels k)) := by
      funext k
      exact hLabel k
    simpa only [List.map_ofFn, Function.comp_def] using congrArg List.ofFn hFunction
  have hGenuineLength : g < B.length :=
    originalSparseTheta_projected_noCentre_long S H sap
      W K hK spokes menus families hSpec C B hNoCentre
  have hLong : r * (N-1) < n := by omega
  have hLongLabels : r * (N-1) < (List.ofFn labels).length := by
    simpa only [List.length_ofFn] using hLong
  have hMenuData (j : Fin r) :
      (menus j).Nonempty ∧
        menus j ⊆ originalEquivDiversityPalette S K :=
    ⟨(hSpec.2 j).2.1, hContained j⟩
  have hSat :=
    original_long_ordered_label_path_saturates
      S H sap K hN menus (List.ofFn labels)
        hLongLabels hMenuData hPowers
  change originalPositiveStrongPath S
      (List.ofFn (fun k : Fin n =>
        originalSparseThetaGuard S W K menus (E k.castSucc))) =
          some (originalEquivDiversityPalette S K)
  rw [hList]
  exact hSat

end CCO.TerminalLattice
