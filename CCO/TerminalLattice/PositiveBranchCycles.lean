import CCO.TerminalLattice.SparseCycleSpectrum
import CCO.TerminalLattice.PrivateBranchCycles

/-!
# B050 C30: original positive-word cycles from saturated root path spectra

Whole positive typed word branches (whose interiors may have ARBITRARY
old named sorts) are concatenated only when their endpoints have the
same ORIGINAL sort. Their actual STRONG endpoint palettes multiply in
the exact old order by proved original SAP profile semantics.

This closes a contractible root-skeleton cycle through a genuinely
specified final positive branch. The separate C27 incidence analysis
must still prove that EACH simple cycle in the one finite private
network reduces to one of these closed positive typed words.  A
realizable closed RAW word is not silently asserted to be a `CycleHom`
for an unconstructed diagram.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- Concatenate exactly the given nonempty list of genuinely positive
typed branches. Since every ENDPOINT lies in original sort i,
intermediate named sorts remain whatever the source words specify. -/
def originalPositiveBranchPath {i : ι}
    (first : PositiveWord S i i)
    (remaining : List (PositiveWord S i i)) :
    PositiveWord S i i :=
  remaining.foldl (PositiveWord.append S) first

/-- The old STRONG endpoint profile of the exact concatenated word is
the product of the original whole-branch profiles in their real order.
Only the actual SAP source provider for positive-word concatenation
is used; no arbitrary quotient-level action appears. -/
theorem originalPositiveBranchPath_profile
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (first : PositiveWord S i i)
    (remaining : List (PositiveWord S i i)) :
    PositiveWord.profile S
      (originalPositiveBranchPath S first remaining) =
      (remaining.map (PositiveWord.profile S)).foldl
        (fun A B => S.product A B) (PositiveWord.profile S first) := by
  induction remaining generalizing first with
  | nil => rfl
  | cons branch rest ih =>
      change PositiveWord.profile S
          (originalPositiveBranchPath S (PositiveWord.append S first branch) rest) =
        (rest.map (PositiveWord.profile S)).foldl
          (fun A B => S.product A B)
          (S.product (PositiveWord.profile S first)
            (PositiveWord.profile S branch))
      rw [ih (PositiveWord.append S first branch)]
      rw [PositiveWord.profile_append_of_SAP S H sap first branch]

/-- The optional positive STRONG-fold API already proved in C29 is
the real profile of precisely the same nonempty typed word path.
The option is present because the first branch REALLY exists,
not because an identity colour was introduced. -/
theorem originalPositiveBranchPath_spectrum
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (first : PositiveWord S i i)
    (remaining : List (PositiveWord S i i)) :
    originalPositiveStrongPath S
      ((first :: remaining).map (PositiveWord.profile S)) =
      some (PositiveWord.profile S
        (originalPositiveBranchPath S first remaining)) := by
  unfold originalPositiveStrongPath
  simp only [List.map_cons, List.foldl_cons, originalOptionStrongStep]
  rw [originalOptionStrongFold_some S,
    originalPositiveBranchPath_profile S H sap first remaining]

/-- SOURCE C30 algebra-to-actual-old-word closure: a complementary
positive branch path has EXACT spectrum K-diversity; a nonempty
old closing menu D lies within K-diversity and within its positive
closing branch profile. The WHOLE closed RAW typed word, consisting
of all complementary branches and the reverse closing branch, has
one genuine original homomorphic realisation.

No requirement that the image of every path vertex be injective:
the original source requires CYCLE HOMOMORPHISMS at this stage, and
original SAP can later provide fresh injectivisation. -/
theorem original_saturated_positive_path_closes_with_branch
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (K : ColourEq S i)
    (first : PositiveWord S i i)
    (remaining : List (PositiveWord S i i))
    (closing : PositiveWord S i i)
    (D : S.Menu i i)
    (hD : D.Nonempty)
    (hDinside : D ⊆ originalEquivDiversityPalette S K)
    (hClosing : D ⊆ PositiveWord.profile S closing)
    (hPath : originalPositiveStrongPath S
        ((first :: remaining).map (PositiveWord.profile S)) =
      some (originalEquivDiversityPalette S K)) :
    ∃ x : X i,
      RawWord.relation S
        (RawWord.append S
          (PositiveWord.toRawWord S
            (originalPositiveBranchPath S first remaining))
          (RawWord.reverse S (PositiveWord.toRawWord S closing))) x x := by
  have hSem :=
    originalPositiveBranchPath_spectrum S H sap first remaining
  have hFull : PositiveWord.profile S
      (originalPositiveBranchPath S first remaining) =
        originalEquivDiversityPalette S K :=
    Option.some.inj (hSem.symm.trans hPath)
  have hFirst : D ⊆ PositiveWord.profile S
      (originalPositiveBranchPath S first remaining) := by
    rw [hFull]
    exact hDinside
  exact original_two_positive_branches_closed_walk S H sap
    D hD (originalPositiveBranchPath S first remaining)
      closing hFirst hClosing

/-- Complete same-sort positive-word C30 conclusion for the C29
actual labelled sparse-graph cycle, once C27 provides the genuine
ordered list of ALL complementary graph edges. The explicit list
permutation prevents assuming an arbitrary unrelated edge order;
the closing positive OLD word is the specific label of the deleted
graph edge. Words can travel through any original named sorts.

The result is ONE closed OLD RAW word-realization for EACH such
specified graph cycle. The missing private-network cycle
classification and ONE global CCO completion are not assumptions. -/
theorem originalSparseGraph_cycle_positive_word_closure
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (K : ColourEq S i)
    {q r g N m : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (hGirth : r * (N-1) + 1 ≤ g)
    (hN : 0 < N)
    (hm : 3 ≤ m)
    (vertices : Fin m ↪ Fin W.size)
    (hEdges : ∀ p : Fin m,
      W.graph.Adj (vertices p)
        (vertices (CCO.cyclicNext (by omega : 0 < m) p)))
    (closing : Fin m)
    (menus : Fin r → S.Menu i i)
    (words : Fin r → PositiveWord S i i)
    (hWords : ∀ j : Fin r, PositiveWord.profile S (words j) = menus j)
    (hMenus : ∀ j : Fin r,
      (menus j).Nonempty ∧
      menus j ⊆ originalEquivDiversityPalette S K)
    (hPowers : ∀ j : Fin r,
      originalStrongPalettePower S (menus j) (N-1) =
        originalEquivDiversityPalette S K)
    (first : Fin m) (remaining : List (Fin m))
    (hOrder : (first :: remaining).Perm
      ((Finset.univ : Finset (Fin m)).erase closing).toList) :
    let labels : Fin m → Fin r :=
      fun p => W.label s(vertices p,
        vertices (CCO.cyclicNext (by omega : 0 < m) p))
    ∃ x : X i,
      RawWord.relation S
        (RawWord.append S
          (PositiveWord.toRawWord S
            (originalPositiveBranchPath S (words (labels first))
              (remaining.map (fun p => words (labels p)))))
          (RawWord.reverse S
            (PositiveWord.toRawWord S (words (labels closing))))) x x := by
  let labels : Fin m → Fin r :=
    fun p => W.label s(vertices p,
      vertices (CCO.cyclicNext (by omega : 0 < m) p))
  have hSpectrum :=
    originalSparseGraph_complementary_strong_saturation
      S H sap K W hGirth hN hm vertices hEdges closing
      menus hMenus hPowers (first :: remaining) hOrder
  have hSpectrumWords :
      originalPositiveStrongPath S
        ((words (labels first) ::
          remaining.map (fun p => words (labels p))).map
            (PositiveWord.profile S)) =
        some (originalEquivDiversityPalette S K) := by
    simpa only [List.map_cons, List.map_map, Function.comp_def,
      hWords] using hSpectrum
  have hClosing :
      menus (labels closing) ⊆
        PositiveWord.profile S (words (labels closing)) := by
    rw [hWords]
  exact original_saturated_positive_path_closes_with_branch
    S H sap K (words (labels first))
    (remaining.map (fun p => words (labels p)))
    (words (labels closing))
    (menus (labels closing))
    (hMenus (labels closing)).1
    (hMenus (labels closing)).2
    hClosing hSpectrumWords

end CCO.TerminalLattice
