import CCO.TerminalLattice.CentreAbsorption
import CCO.TerminalLattice.OriginalStrongAlgebra

/-!
# B050 C29: original same-sort STRONG path factor reordering

Once the sparse graph girth forces N occurrences of one external label,
the source proof must move these N ACTUAL full OLD endpoint menus next
to each other. This is permitted only for SAME-SORT STRONG menu
products, by accepted old symmetry + original AgeSAP complete-edge
associativity. No internal named-sort atom letters are permuted.

The current lemma expresses the exact semantic factorization AFTER
an explicit list permutation has been supplied. The remaining source
C29 link must extract that permutation from the actual C29 label count
and the formal graph-cycle path; neither is silently assumed by the
full cycle-guard theorem.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- SAME-SORT STRONG menu fold over finite formal edge factors is
permutation invariant with any genuine initial menu. The proof uses
only original AgeSAP for associativity, and old source symmetry for
commutativity, not CCO or mixed-sort exactness. -/
theorem original_strong_menu_fold_perm
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (seed : S.Menu i i)
    {xs ys : List (S.Menu i i)} (h : xs.Perm ys) :
    xs.foldl (fun A B => S.product A B) seed =
      ys.foldl (fun A B => S.product A B) seed := by
  induction h generalizing seed with
  | nil => rfl
  | @cons a xs ys _ ih =>
      simpa only [List.foldl_cons] using
        (ih (S.product seed a))
  | @swap a b xs =>
      have hc :
          S.product (S.product seed a) b =
            S.product (S.product seed b) a := by
        calc
          S.product (S.product seed a) b =
              S.product seed (S.product a b) :=
            original_same_sort_strong_assoc S H sap seed a b
          _ = S.product seed (S.product b a) := by
              rw [original_same_sort_strong_commute S a b]
          _ = S.product (S.product seed b) a :=
            (original_same_sort_strong_assoc S H sap seed b a).symm
      simpa only [List.foldl_cons] using
        (congrArg (fun M => xs.foldl (fun A B => S.product A B) M) hc).symm
  | @trans xs ys zs hxy hyz ihxy ihyz =>
      exact (ihxy seed).trans (ihyz seed)

/-- A genuine list of n copies of a SAME-SORT old diversity menu,
folded from that menu itself, is its actual positive STRONG power of
length n+1. No fictitious zero-length STRONG identity appears. -/
theorem original_strong_fold_replicate
    {i : ι} (T : S.Menu i i) (n : Nat) :
    (List.replicate n T).foldl (fun A B => S.product A B) T =
      originalStrongPalettePower S T n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hRep : List.replicate (n+1) T =
          List.replicate n T ++ [T] := by
        simp only [List.replicate_add, List.replicate_one]
      calc
        (List.replicate (n+1) T).foldl (fun A B => S.product A B) T =
            S.product
              ((List.replicate n T).foldl (fun A B => S.product A B) T)
              T := by
          rw [hRep, List.foldl_append]
          rfl
        _ = S.product (originalStrongPalettePower S T n) T := by rw [ih]
        _ = originalStrongPalettePower S T (n+1) := by
          change S.product (originalStrongPalettePower S T n) T =
            S.product T (originalStrongPalettePower S T n)
          exact S.loop_product_commute _ _

/-- C29 STRONG spectrum factorization, with the actual rearrangement
explicit. If the complementary old root path has N+1 genuine copies
of T (one seed and N further factors) and the remaining factors are
nonempty subpalettes of K-diversity, its ACTUAL STRONG endpoint
spectrum is exactly K-diversity whenever that T power already is K.

The original C29 label-counting and cycle-skeleton geometry must still
provide the permutation hypothesis here. This is NOT a full cycle
homomorphism or an application of original CCO. -/
theorem original_grouped_strong_path_saturates
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (K : ColourEq S i)
    (T : S.Menu i i) (n : Nat)
    (others original : List (S.Menu i i))
    (hPerm : original.Perm (List.replicate n T ++ others))
    (hPower : originalStrongPalettePower S T n =
      originalEquivDiversityPalette S K)
    (hOthers : ∀ D ∈ others,
      D.Nonempty ∧ D ⊆ originalEquivDiversityPalette S K) :
    original.foldl (fun A B => S.product A B) T =
      originalEquivDiversityPalette S K := by
  rw [original_strong_menu_fold_perm S H sap T hPerm,
    List.foldl_append, original_strong_fold_replicate S T n,
    hPower]
  exact originalKSpokePath_absorbed S H sap K others hOthers

end CCO.TerminalLattice
