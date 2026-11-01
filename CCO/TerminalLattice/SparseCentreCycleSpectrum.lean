import CCO.TerminalLattice.SparseCentreFirstSpoke
import CCO.TerminalLattice.CentrePathSpectrum
import Mathlib.Data.List.OfFn

/-!
# B050 C27/C28: genuine centre-containing projected OLD cycles saturate

Every marked edge of the ONE actual original sparse private-word diagram
is a specified old centre spoke or a REAL W edge. The former has profile
K-diversity; the latter is a selected complete old-group external orbital
menu lying nonemptily inside K-diversity. Reversed whole original words
retain exactly those same-sort endpoint palettes.

The prior-spoke theorem for a genuine B002 projection containing its
unique centre gives one K-diversity factor AMONG THE ACTUAL first n
cyclic branches. True old same-sort STRONG commutation/absorption then
saturates the complete ordered path before the final closing edge.

No abstract skeleton, artificial word, quotient-level SAP, original CCO
completion or conditional global reset is assumed.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- Each ACTUAL used oriented B002 sparse-star edge is a nonempty
original same-sort positive-word profile inside the original K°
diversity. This uses the exact one-word literal selection, not an
arbitrary exactness hypothesis. -/
theorem oldSparseWordDiagram_oriented_profile_valid
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g : Nat}
    (K : ColourEq S i)
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (hSpoke : PositiveWord.profile S spoke =
      originalEquivDiversityPalette S K)
    (menus : Fin r → S.Menu i i)
    (hMenus : ∀ j : Fin r,
      (menus j).Nonempty ∧
      menus j ⊆ originalEquivDiversityPalette S K)
    (hWords : ∀ j : Fin r,
      PositiveWord.profile S (words j) = menus j)
    (C : SimpleCycle (oldSparseWordDiagram S H sap W spoke words))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin (W.size+1) => i)
      (oldOptionalPositivePresentations S
        (oldSparseWordSelection S W spoke words))
      (oldOptionalPositivePresentations_nonempty S H sap
        (oldSparseWordSelection S W spoke words)) C)
    (k : Fin B.length) :
    (PositiveWord.profile S
      (oldProjectedOrientedWord S H sap
        (oldSparseWordSelection S W spoke words) C B k)).Nonempty ∧
    PositiveWord.profile S
      (oldProjectedOrientedWord S H sap
        (oldSparseWordSelection S W spoke words) C B k) ⊆
      originalEquivDiversityPalette S K := by
  rw [oldProjectedOrientedWord_profile S H sap
    (oldSparseWordSelection S W spoke words) C B k]
  have hSelected :=
    oldProjectedCanonicalWord_selected S H sap
      (oldSparseWordSelection S W spoke words) C B k
  rcases oldSparseWordDiagram_projected_exact_word
      S H sap W spoke words C B k with
    ⟨_,hSpokeSelected⟩ | ⟨x,y,_,_,_,hGraphSelected⟩
  · have heq :
        oldProjectedCanonicalWord S H sap
          (oldSparseWordSelection S W spoke words) C B k = spoke :=
      Option.some.inj (hSelected.symm.trans hSpokeSelected)
    rw [heq,hSpoke]
    refine ⟨?_,Set.Subset.rfl⟩
    rw [← hSpoke]
    exact PositiveWord.profile_nonempty_of_SAP S H sap spoke
  · have heq :
        oldProjectedCanonicalWord S H sap
          (oldSparseWordSelection S W spoke words) C B k =
          words (W.label s(x,y)) :=
      Option.some.inj (hSelected.symm.trans hGraphSelected)
    rw [heq,hWords]
    exact hMenus (W.label s(x,y))

/-- SOURCE C28, now for a REAL centre-containing B002 compression:
the original ordered positive STRONG product of EVERY cyclic edge
except the LAST chosen closing edge is exactly K°. For any cyclic
numbering, the centre must have an incident spoke before the last
edge, and its true original old positive profile is K°. All other
ACTUAL selected old profiles are nonempty inside K°.

There is no unproved assumption of an order-preserving graph path,
a hypothetical cycle oracle or a synthetic zero-length STRONG factor.
-/
theorem oldSparseWordDiagram_centre_complement_saturates
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g n : Nat}
    (K : ColourEq S i)
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (hSpoke : PositiveWord.profile S spoke =
      originalEquivDiversityPalette S K)
    (menus : Fin r → S.Menu i i)
    (hMenus : ∀ j : Fin r,
      (menus j).Nonempty ∧
      menus j ⊆ originalEquivDiversityPalette S K)
    (hWords : ∀ j : Fin r,
      PositiveWord.profile S (words j) = menus j)
    (C : SimpleCycle (oldSparseWordDiagram S H sap W spoke words))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin (W.size+1) => i)
      (oldOptionalPositivePresentations S
        (oldSparseWordSelection S W spoke words))
      (oldOptionalPositivePresentations_nonempty S H sap
        (oldSparseWordSelection S W spoke words)) C)
    (hLength : B.length = n+1)
    (hCentre : ∃ p : Fin B.length,
      B.vertices p = oldSparseCentre W) :
    originalPositiveStrongPath S
      ((List.ofFn (fun k : Fin n =>
        oldProjectedOrientedWord S H sap
          (oldSparseWordSelection S W spoke words) C B
          (Fin.cast hLength.symm k.castSucc))).map
        (PositiveWord.profile S)) =
      some (originalEquivDiversityPalette S K) := by
  let branches : Fin n → PositiveWord S i i :=
    fun k => oldProjectedOrientedWord S H sap
      (oldSparseWordSelection S W spoke words) C B
      (Fin.cast hLength.symm k.castSucc)
  let lst : List (PositiveWord S i i) := List.ofFn branches
  have hAll : ∀ word ∈ lst,
      (PositiveWord.profile S word).Nonempty ∧
      PositiveWord.profile S word ⊆
        originalEquivDiversityPalette S K := by
    intro word hword
    obtain ⟨k,hk⟩ :=
      (List.mem_ofFn' branches word).mp hword
    subst word
    exact oldSparseWordDiagram_oriented_profile_valid
      S H sap K W spoke words hSpoke menus hMenus hWords C B
      (Fin.cast hLength.symm k.castSucc)
  obtain ⟨k,hk⟩ :=
    oldSparseWordDiagram_projected_prior_spoke_profile
      S H sap W spoke words C B hLength hCentre
  have hSpokeList : ∃ word ∈ lst,
      PositiveWord.profile S word =
        originalEquivDiversityPalette S K := by
    refine ⟨branches k, ?_, ?_⟩
    · exact (List.mem_ofFn' branches (branches k)).mpr ⟨k,rfl⟩
    · exact hk.trans hSpoke
  have hSat :=
    original_positive_words_with_K_spoke_saturate
      S H sap K lst hAll hSpokeList
  simpa only [lst,branches] using hSat

end CCO.TerminalLattice
