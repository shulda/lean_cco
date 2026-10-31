import CCO.TerminalLattice.SparseCentreCycleSpectrum
import CCO.TerminalLattice.SparseCycleNoCentre
import CCO.TerminalLattice.OriginalLabelListThreshold

/-!
# B050 C27/C29: actual centre-free B002 marked cycles have saturated complements

If the centre is ABSENT from a real compressed marked simple cycle
of the ONE original sparse private-word diagram, the accepted B002
projection is an injective cyclic ordering of ACTUAL graph roots in W.
Every actual used marked edge is a W-adjacent root pair carrying exactly
one original positive word for an ACTUAL graph label, irrespective of the
cyclic orientation. The original full-group external label menus are
nonempty and have uniform eventual K-diversity pure powers.

Consequently the real girth of W makes every complementary ordered
path (after deleting the last chosen closing edge) long enough for the
literal list-label pigeonhole theorem, with its own actual label order.
Its old STRONG endpoint spectrum is K-diversity.

No extra labelled skeleton, quotient reduction, new SAP, CCO completion,
fictional identity edge, or permutation of typed word interiors.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- In an ACTUAL centre-free compressed B002 cycle, the endpoint
profile of EVERY used old oriented positive word equals one of
the genuinely indexed W graph-label menus. The selected label is
literally W.label on a REAL adjacent unordered root pair, not a
hypothetical suborbital colour. -/
theorem oldSparseWordDiagram_centre_free_step_label
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (menus : Fin r → S.Menu i i)
    (hWords : ∀ j : Fin r,
      PositiveWord.profile S (words j) = menus j)
    (C : SimpleCycle (oldSparseWordDiagram S H sap W spoke words))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin (W.size+1) => i)
      (oldOptionalPositivePresentations S
        (oldSparseWordSelection S W spoke words))
      (oldOptionalPositivePresentations_nonempty S H sap
        (oldSparseWordSelection S W spoke words)) C)
    (hNoCentre : ∀ p : Fin B.length,
      B.vertices p ≠ oldSparseCentre W)
    (k : Fin B.length) :
    ∃ j : Fin r,
      PositiveWord.profile S
        (oldProjectedOrientedWord S H sap
          (oldSparseWordSelection S W spoke words) C B k) =
        menus j := by
  have hSelected :=
    oldProjectedCanonicalWord_selected S H sap
      (oldSparseWordSelection S W spoke words) C B k
  rcases oldSparseWordDiagram_projected_exact_word
      S H sap W spoke words C B k with
    ⟨hCentre,_⟩ | ⟨x,y,_,_,_,hWord⟩
  · have hRight :
        CCO.RawExact.QuotientExpansion.right (B.edges k) =
          oldSparseCentre W := by
      apply Fin.ext
      simpa [CCO.RawExact.QuotientExpansion.right,oldSparseCentre] using hCentre
    rcases B.endpoints k with ⟨_,hEnd⟩ | ⟨hStart,_⟩
    · exact False.elim
        (hNoCentre (CCO.cyclicNext B.length_pos k) (hEnd.trans hRight))
    · exact False.elim (hNoCentre k (hStart.trans hRight))
  · have hCanonical :
        oldProjectedCanonicalWord S H sap
          (oldSparseWordSelection S W spoke words) C B k =
          words (W.label s(x,y)) :=
      Option.some.inj (hSelected.symm.trans hWord)
    refine ⟨W.label s(x,y), ?_⟩
    calc
      PositiveWord.profile S
          (oldProjectedOrientedWord S H sap
            (oldSparseWordSelection S W spoke words) C B k) =
        PositiveWord.profile S
          (oldProjectedCanonicalWord S H sap
            (oldSparseWordSelection S W spoke words) C B k) :=
        oldProjectedOrientedWord_profile S H sap
          (oldSparseWordSelection S W spoke words) C B k
      _ = PositiveWord.profile S (words (W.label s(x,y))) := by
        rw [hCanonical]
      _ = menus (W.label s(x,y)) := hWords _

/-- Source C29 for the actual centre-FREE projected graph cycle.
The original B006 no-short-cycles statement forces length > girth
threshold, and the actual cyclic edge labels are extracted from
the literal B002 selections at each ordered graph root pair.

The whole finite OLD complement before the last closing edge has
STRONG spectrum exactly K-diversity, preserving original word
orientation and literal consecutive root order. -/
theorem oldSparseWordDiagram_centre_free_complement_saturates
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g N n : Nat}
    (K : ColourEq S i)
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (menus : Fin r → S.Menu i i)
    (hWords : ∀ j : Fin r,
      PositiveWord.profile S (words j) = menus j)
    (hMenus : ∀ j : Fin r,
      (menus j).Nonempty ∧
      menus j ⊆ originalEquivDiversityPalette S K)
    (hPowers : ∀ j : Fin r,
      originalStrongPalettePower S (menus j) (N-1) =
        originalEquivDiversityPalette S K)
    (hN : 0 < N) (hGirth : r * (N-1) + 1 ≤ g)
    (C : SimpleCycle (oldSparseWordDiagram S H sap W spoke words))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin (W.size+1) => i)
      (oldOptionalPositivePresentations S
        (oldSparseWordSelection S W spoke words))
      (oldOptionalPositivePresentations_nonempty S H sap
        (oldSparseWordSelection S W spoke words)) C)
    (hLength : B.length = n+1)
    (hNoCentre : ∀ p : Fin B.length,
      B.vertices p ≠ oldSparseCentre W) :
    originalPositiveStrongPath S
      ((List.ofFn (fun k : Fin n =>
        oldProjectedOrientedWord S H sap
          (oldSparseWordSelection S W spoke words) C B
          (Fin.cast hLength.symm k.castSucc))).map
        (PositiveWord.profile S)) =
      some (originalEquivDiversityPalette S K) := by
  classical
  obtain ⟨vertices,hEdges⟩ :=
    oldSparseWordDiagram_centre_free_graph_cycle
      S H sap W spoke words C B hNoCentre
  have hLong : r * (N-1) < n := by
    by_contra hh
    have hShort : B.length ≤ g := by omega
    have hImpossible := W.noShortCycles
      B.length B.length_ge_three hShort vertices hEdges
    exact hImpossible
  have hStep : ∀ k : Fin B.length,
      ∃ j : Fin r,
        PositiveWord.profile S
          (oldProjectedOrientedWord S H sap
            (oldSparseWordSelection S W spoke words) C B k) =
          menus j :=
    oldSparseWordDiagram_centre_free_step_label
      S H sap W spoke words menus hWords C B hNoCentre
  let labels : Fin n → Fin r :=
    fun k => Classical.choose
      (hStep (Fin.cast hLength.symm k.castSucc))
  have hChosen (k : Fin n) :
      PositiveWord.profile S
        (oldProjectedOrientedWord S H sap
          (oldSparseWordSelection S W spoke words) C B
          (Fin.cast hLength.symm k.castSucc)) =
        menus (labels k) :=
    Classical.choose_spec
      (hStep (Fin.cast hLength.symm k.castSucc))
  have hLongList : r * (N-1) <
      (List.ofFn labels).length := by
    simpa only [List.length_ofFn] using hLong
  have hSat :=
    original_long_ordered_label_path_saturates
      S H sap K hN menus (List.ofFn labels)
      hLongList hMenus hPowers
  have hFun :
      (fun k : Fin n =>
        PositiveWord.profile S
          (oldProjectedOrientedWord S H sap
            (oldSparseWordSelection S W spoke words) C B
            (Fin.cast hLength.symm k.castSucc))) =
      (fun k : Fin n => menus (labels k)) := by
    funext k
    exact hChosen k
  simpa only [List.map_ofFn, Function.comp_def, hFun] using hSat

end CCO.TerminalLattice
