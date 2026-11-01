import CCO.TerminalLattice.OriginalSparseKFrame
import CCO.TerminalLattice.ExternalUniformPowers
import CCO.ParityHasse.Sparse.Existence

/-!
# B050 C40: unconditional original FULL-cover reset with one actual CCO map

Source C40 is proved here with its EXACT original hypotheses:
homogeneous original source, original age-SAP and semantic CCO,
one nonzero FULL original invariant cover J ⋖ K, an original anchor
excluding local relative index two, and genuinely positive OLD typed
word presentations for BOTH J-diversity and K-diversity.

The finite external menu family is precisely the COMPLETE quotient
orbitals under the original full ambient group G. Its labels are
indexed by the actual K-external OLD fine atoms. Each menu has an
actual positive old word and one common full K-diversity STRONG power
threshold, proved independently of source CCO.

The sparse graph is the ACTUAL accepted B006 construction with the
exact finite colour palette of OLD K-diversity fine atoms. Its ONE
private old diagram is completed using original semantic CCO ONCE
plus real old SAP injectivization (C34). The actual centre-to-root
old colours then produce the genuine graph vertex colouring (C35),
and the labelled monochromatic edges hit every complete external
old-G orbital at once. The previously proved original algebra
upgrades those literal hits to the full STRONG square K-diversity
and separately to the equality-inclusive RAW square K.

No quotient-reduct group, quotient SAP/CCO, fictitious identity atom,
source-conditional network provider, B049 import, NR2, or stronger
source hypothesis appears.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- SOURCE C40: `thm:typed-original-full-cover-reset-single-path`.
The ORIGINAL full-group complete quotient orbital of a real
K-external pair p,z has genuine old STRONG square exactly K°,
and the equality-inclusive RAW relation of the SAME orbital
squares to the actual original invariant equivalence K.

The proof constructs ALL graph labels, all typed words, and the ONE
old global network using the source's OWN assumptions, not a
hypothetical conditional receiving structure. The distinct original
identity diagonal is added only by REAL two-step RAW returns and the
previously proved original SAP relation bridge. -/
theorem original_full_cover_reset_single_path
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (J K : ColourEq S i)
    (hJK : J ⋖ K) (hJ : (⊥ : ColourEq S i) < J)
    (anchor : X i)
    (hNotTwo : relativeIndex J.val K.val anchor ≠ 2)
    (wJ : PositiveWord S i i)
    (hwJ : PositiveWord.profile S wJ =
      originalEquivDiversityPalette S J)
    (wK : PositiveWord S i i)
    (hwK : PositiveWord.profile S wK =
      originalEquivDiversityPalette S K) :
    ∃ p z : X i, K p z ∧ ¬ J p z ∧
      (S.product
        (originalQuotientOrbitalPalette S (G := G) J p z)
        (originalQuotientOrbitalPalette S (G := G) J p z) =
          originalEquivDiversityPalette S K) ∧
      (RawSymmetric.compose
        (S.menuRel (originalQuotientOrbitalPalette S (G := G) J p z))
        (S.menuRel (originalQuotientOrbitalPalette S (G := G) J p z)) =
          K.val.r) := by
  classical
  let r : Nat := Fintype.card (OriginalExternalAtom S J K)
  let q : Nat := Fintype.card (OriginalKdivAtom S K)
  have hr : 0 < r :=
    originalExternalAtom_card_pos_of_full_cover S J K hJK
  have hK : (⊥ : ColourEq S i) < K := hJ.trans hJK.lt
  have hq : 0 < q := originalKdivAtom_card_pos S K hK
  let T : Fin r → S.Menu i i :=
    originalIndexedExternalOrbitalMenus S (G := G) J K
  let words : Fin r → PositiveWord S i i :=
    originalIndexedExternalPositiveWords
      S H sap J K hJ wJ hwJ
  have hWords : ∀ j : Fin r,
      PositiveWord.profile S (words j) = T j :=
    originalIndexedExternalPositiveWords_profile
      S H sap J K hJ wJ hwJ
  have hValid := originalIndexedExternalOrbitalMenus_valid
    S H J K hJK.le
  have hMenus : ∀ j : Fin r,
      (T j).Nonempty ∧
      T j ⊆ originalEquivDiversityPalette S K := by
    intro j
    exact (hValid j).1, (hValid j).2.1
  have hExternal : ∀ j : Fin r, ∀ c ∈ T j,
      c ∉ originalEquivDiversityPalette S J := by
    intro j c hc
    exact (hValid j).2.2 c hc
  have hEnumerate : ∀ x y : X i, K x y → ¬ J x y →
      ∃ j : Fin r, T j =
        originalQuotientOrbitalPalette S (G := G) J x y := by
    intro x y hKxy hNotJxy
    exact originalIndexedExternalOrbitalMenus_cover
      S H J K x y hKxy hNotJxy
  obtain ⟨N,hN,hUniform⟩ :=
    originalIndexedExternalOrbitalMenus_uniform_powers
      S H sap J K hJK hJ anchor hNotTwo
  have hPowers : ∀ j : Fin r,
      originalStrongPalettePower S (T j) (N-1) =
        originalEquivDiversityPalette S K := by
    intro j
    exact hUniform j N le_rfl
  let g : Nat := r * (N-1) + 2
  have hGirth : r * (N-1) + 1 ≤ g := by
    dsimp [g]
    omega
  obtain ⟨W⟩ :=
    CCO.ParityHasse.Sparse.sparse_labelled_graph_exists hq hr g
  obtain ⟨f,hInj⟩ :=
    oldSparseWordDiagram_injective_hom_of_original_CCO
      S H sap cco K W wK words T hwK hWords hMenus
        hPowers hN hGirth
  obtain ⟨p,z,hKpz,hNotJpz,hHits⟩ :=
    originalSparseRealization_all_external_hits
      S H sap J K hr W wK words hwK T
      hWords hExternal hEnumerate f hInj
  obtain ⟨hStrong,hRaw⟩ :=
    original_complete_reset_strong_and_RAW_of_all_hits
      S H sap J K hJK.le hJ p z hKpz hNotJpz hHits
  exact ⟨p,z,hKpz,hNotJpz,hStrong,hRaw⟩

end CCO.TerminalLattice
