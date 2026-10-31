import CCO.TerminalLattice.PositiveBranchChain
import CCO.TerminalLattice.ReversePositiveWord
import CCO.RawExact.CyclicDeletion
import Mathlib.Data.List.OfFn

/-!
# B050 C27: a true old positive word chain becomes finite indexed root values

The original old positive-word path witnesses are now recorded as a
finite family of ACTUAL source points, one per marked root. Both the
linear edges and the cyclic closing edge retain their exact original
positive typed represented relation. The no-factor case introduces no
new positive identity word; it uses only equality of a path's endpoints.

This is independent of the sparse graph girth/label argument: its use
in C27 requires proving a saturated path in the exact cyclic order of
the compressed B002 marked projection, not merely a permutation
of unknown edges.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- A concrete OLD positive branch chain supplies ALL its successive
original-sort values. Every actual word occurs exactly at its own
Fin index and is realised between its two respective endpoints.
The final value is exactly the originally specified real endpoint. -/
theorem originalPositiveBranchChain_fin_values
    {i : ι} (words : List (PositiveWord S i i))
    (x y : X i)
    (h : originalPositiveBranchChain S words x y) :
    ∃ values : Fin (words.length+1) → X i,
      values 0 = x ∧
      values (Fin.last words.length) = y ∧
      ∀ k : Fin words.length,
        PositiveWord.represented S (words.get k)
          (values k.castSucc) (values k.succ) := by
  induction words generalizing x y with
  | nil =>
      change x = y at h
      subst y
      refine ⟨fun _ => x, rfl, rfl, ?_⟩
      intro k
      exact Fin.elim0 k
  | cons w rest ih =>
      change ∃ z : X i,
        PositiveWord.represented S w x z ∧
        originalPositiveBranchChain S rest z y at h
      obtain ⟨z,hFirst,hRest⟩ := h
      obtain ⟨tail,htail0,htailLast,htailEdges⟩ := ih z y hRest
      let values : Fin (rest.length+2) → X i := Fin.cons x tail
      refine ⟨values, ?_, ?_, ?_⟩
      · rfl
      · have hLastIndex :
          (Fin.last (rest.length+1) : Fin (rest.length+2)) =
            (Fin.last rest.length).succ := by
          apply Fin.ext
          rfl
        change values (Fin.last (rest.length+1)) = y
        rw [hLastIndex]
        simpa only [values, Fin.cons_succ] using htailLast
      · intro k
        induction k using Fin.cases with
        | zero =>
            change PositiveWord.represented S w (values 0) (values 1)
            have hOne : (1 : Fin (rest.length+2)) =
                (0 : Fin (rest.length+1)).succ := Fin.ext rfl
            rw [hOne]
            change PositiveWord.represented S w x (tail 0)
            rw [htail0]
            exact hFirst
        | succ k =>
            change PositiveWord.represented S (rest.get k)
              (values k.succ.castSucc) (values k.succ.succ)
            have hCast :
                (k.succ.castSucc : Fin (rest.length+2)) =
                  (k.castSucc).succ := Fin.ext rfl
            rw [hCast]
            simpa only [values, Fin.cons_succ] using htailEdges k

/-- For the actual finite cyclic numbering 0,...,n, the first n
successor edges DO NOT wrap, while the last edge wraps to 0. -/
theorem original_cyclicNext_castSucc
    {n : Nat} (hn : 0 < n) (k : Fin n) :
    CCO.cyclicNext (Nat.succ_pos n) k.castSucc = k.succ := by
  apply Fin.ext
  change (k.val + 1) % (n+1) = k.val + 1
  exact Nat.mod_eq_of_lt (by have hk := k.isLt; omega)

theorem original_cyclicNext_last
    {n : Nat} :
    CCO.cyclicNext (Nat.succ_pos n) (Fin.last n) =
      (0 : Fin (n+1)) := by
  apply Fin.ext
  change (n+1) % (n+1) = 0
  exact Nat.mod_self _

/-- Genuine C27 finite cycle root values, from a true ORIGINAL old
branch chain for every successive edge except the last, together
with its actual final closing word (in the reverse endpoint order).
The conclusion is simultaneous: ONE valuation works for ALL cyclic
positive OLD branch relations, with NO extra CCO, SAP or homomorphism
assumption. The separate sparse graph lemma must supply the path
chain and real last closing word using C29/C30. -/
theorem original_positive_branch_chain_cyclic_values
    {i : ι} {n : Nat}
    (branches : Fin (n+1) → PositiveWord S i i)
    (x y : X i)
    (hChain : originalPositiveBranchChain S
      (List.ofFn (fun k : Fin n => branches k.castSucc)) x y)
    (hClosing : PositiveWord.represented S
      (branches (Fin.last n)) y x) :
    ∃ values : Fin (n+1) → X i,
      ∀ k : Fin (n+1),
        PositiveWord.represented S (branches k)
          (values k)
          (values (CCO.cyclicNext (Nat.succ_pos n) k)) := by
  have hFinite :
      ∃ values : Fin (n+1) → X i,
        values 0 = x ∧
        values (Fin.last n) = y ∧
        ∀ t : Fin n,
          PositiveWord.represented S (branches t.castSucc)
            (values t.castSucc) (values t.succ) := by
    have hRaw :=
      originalPositiveBranchChain_fin_values S
        (List.ofFn (fun t : Fin n => branches t.castSucc)) x y hChain
    simp only [List.get_ofFn] at hRaw
    simpa [List.length_ofFn] using hRaw
  obtain ⟨values,hFirst,hLast,hEdges⟩ := hFinite
  refine ⟨values, ?_⟩
  intro k
  by_cases hkLast : k = Fin.last n
  · subst k
    rw [original_cyclicNext_last]
    simpa only [hFirst,hLast] using hClosing
  · let t : Fin n := ⟨k.val, by
      have hk := k.isLt
      have hkN : k.val ≠ n := by
        intro hkn
        exact hkLast (Fin.ext hkn)
      omega⟩
    have ht : t.castSucc = k := Fin.ext rfl
    have hNext :
        CCO.cyclicNext (Nat.succ_pos n) k = t.succ := by
      rw [← ht]
      exact original_cyclicNext_castSucc (by omega : 0 < n) t
    have hThis := hEdges t
    simpa only [ht, hNext] using hThis


/-- Genuine C27/C30 cyclic witness from the established same-sort
STRONG complementary-path spectrum. The first n ACTUAL old positive
branches, in their literal cyclic order, have the full diversity
spectrum K°. A nonempty fine menu D of the CLOSING branch lies in
K°, so the already proved C30 word-closure theorem can be applied
to the reverse closing word, whose same-sort STRONG profile is exact.

This constructs ONE simultaneous ORIGINAL real valuation for every
cyclic root, satisfying EVERY correctly oriented old positive word.
No original CCO completion, SAP at the quotient level, unproved
cycle-realization provider or invented identity factor is used.

To instantiate the original sparse network, C27 must still identify
its actual projected oriented branches and PROVE this precise
complementary spectrum from its centre/spoke or girth/label geometry.
-/
theorem original_saturated_positive_cyclic_values
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (K : ParityHasse.Original.ColourEq S i)
    {n : Nat} (hn : 0 < n)
    (branches : Fin (n+1) → PositiveWord S i i)
    (D : S.Menu i i)
    (hD : D.Nonempty)
    (hDinside : D ⊆ originalEquivDiversityPalette S K)
    (hClosing : D ⊆
      PositiveWord.profile S (branches (Fin.last n)))
    (hSpectrum : originalPositiveStrongPath S
      ((List.ofFn (fun k : Fin n => branches k.castSucc)).map
        (PositiveWord.profile S)) =
      some (originalEquivDiversityPalette S K)) :
    ∃ values : Fin (n+1) → X i,
      ∀ k : Fin (n+1),
        PositiveWord.represented S (branches k) (values k)
          (values (CCO.cyclicNext (Nat.succ_pos n) k)) := by
  cases hPath : (List.ofFn (fun k : Fin n => branches k.castSucc)) with
  | nil =>
      have hZero : n = 0 := by
        have hLength := congrArg List.length hPath
        simpa only [List.length_ofFn, List.length_nil] using hLength
      omega
  | cons first rest =>
      have hSpectrum' :
          originalPositiveStrongPath S
              ((first :: rest).map (PositiveWord.profile S)) =
            some (originalEquivDiversityPalette S K) := by
        simpa only [hPath] using hSpectrum
      have hClosingReverse : D ⊆
          PositiveWord.profile S
            (originalPositiveWordReverse S (branches (Fin.last n))) := by
        rw [originalPositiveWordReverse_same_sort_profile
          S H sap (branches (Fin.last n))]
        exact hClosing
      obtain ⟨x,y,hChain,hReverse⟩ :=
        original_saturated_positive_path_branch_values
          S H sap K first rest
          (originalPositiveWordReverse S (branches (Fin.last n)))
          D hD hDinside hClosingReverse hSpectrum'
      have hChainActual :
          originalPositiveBranchChain S
            (List.ofFn (fun k : Fin n => branches k.castSucc)) x y := by
        rw [hPath]
        exact hChain
      have hLastActual :
          PositiveWord.represented S (branches (Fin.last n)) y x := by
        change (TRel.converse
          (PositiveWord.represented S (branches (Fin.last n)))) x y
        rw [← originalPositiveWordReverse_represented
          S (branches (Fin.last n))]
        exact hReverse
      exact original_positive_branch_chain_cyclic_values
        S branches x y hChainActual hLastActual

end CCO.TerminalLattice
