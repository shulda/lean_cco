import CCO.TerminalLattice.LabelledPathGrouping
import CCO.TerminalLattice.StrongPathReordering

/-!
# B050 C29: exact positive STRONG product of an actual labelled root path

This is the algebraic complement of the real finite edge-label count.
No OLD identity colour or zero-length STRONG product is fabricated:
`none` denotes an EMPTY LIST OF FACTORS at the metalevel, and a
positive list has `some` of its genuine STRONG endpoint product.

Original SAP is used for OLD same-sort positive product associativity;
only the original same-sort symmetry is used for commutativity. The
interiors of individual typed atomic words are never permuted.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- Add one genuine old same-sort STRONG menu to an OPTIONAL nonempty
path product. The `none` case means there was NO path factor yet,
rather than that there is a synthetic STRONG identity. -/
def originalOptionStrongStep {i : ι}
    (acc : Option (S.Menu i i)) (D : S.Menu i i) :
    Option (S.Menu i i) :=
  match acc with
  | none => some D
  | some A => some (S.product A D)

/-- The actual product of a positive list of old same-sort fine-atom
menus, with `none` only for the zero-factor list. -/
def originalPositiveStrongPath {i : ι} (ds : List (S.Menu i i)) :
    Option (S.Menu i i) :=
  ds.foldl (originalOptionStrongStep S) none

private theorem originalOptionStrongStep_swap
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (seed : Option (S.Menu i i)) (A B : S.Menu i i) :
    originalOptionStrongStep S (originalOptionStrongStep S seed A) B =
      originalOptionStrongStep S (originalOptionStrongStep S seed B) A := by
  cases seed with
  | none =>
      change some (S.product A B) = some (S.product B A)
      exact congrArg Option.some (original_same_sort_strong_commute S A B)
  | some seed =>
      change some (S.product (S.product seed A) B) =
          some (S.product (S.product seed B) A)
      apply congrArg Option.some
      calc
        S.product (S.product seed A) B =
            S.product seed (S.product A B) :=
          original_same_sort_strong_assoc S H sap seed A B
        _ = S.product seed (S.product B A) := by
          rw [original_same_sort_strong_commute S A B]
        _ = S.product (S.product seed B) A :=
          (original_same_sort_strong_assoc S H sap seed B A).symm

/-- Reordering only SAME-SORT whole STRONG endpoint profiles preserves
the true product of an actual finite list, even if its first element
changes. `none` does not represent an atomic relation. -/
theorem originalOptionStrongFold_perm
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (seed : Option (S.Menu i i))
    {xs ys : List (S.Menu i i)} (h : xs.Perm ys) :
    xs.foldl (originalOptionStrongStep S) seed =
      ys.foldl (originalOptionStrongStep S) seed := by
  induction h generalizing seed with
  | nil => rfl
  | @cons a xs ys _ ih =>
      simpa only [List.foldl_cons] using
        (ih (originalOptionStrongStep S seed a))
  | @swap a b xs =>
      have hc := originalOptionStrongStep_swap S H sap seed a b
      simpa only [List.foldl_cons] using
        (congrArg (fun M => xs.foldl (originalOptionStrongStep S) M) hc).symm
  | @trans xs ys zs hxy hyz ihxy ihyz =>
      exact (ihxy seed).trans (ihyz seed)

private theorem originalOptionStrongFold_some {i : ι}
    (seed : S.Menu i i) (xs : List (S.Menu i i)) :
    xs.foldl (originalOptionStrongStep S) (some seed) =
      some (xs.foldl (fun A B => S.product A B) seed) := by
  induction xs generalizing seed with
  | nil => rfl
  | cons a xs ih =>
      simpa only [List.foldl_cons, originalOptionStrongStep] using
        (ih (S.product seed a))

/-- A list of n+1 ACTUAL copies of T, followed by any remaining
factors, gives precisely the already-established positive STRONG
power T^(n+1) followed by the remaining factors. -/
theorem originalOptionStrongFold_powers {i : ι}
    (T : S.Menu i i) (n : Nat) (rest : List (S.Menu i i)) :
    (List.replicate (n+1) T ++ rest).foldl
      (originalOptionStrongStep S) none =
      some (rest.foldl (fun A B => S.product A B)
        (originalStrongPalettePower S T n)) := by
  have hFirst :
      (List.replicate (n+1) T ++ rest).foldl
          (originalOptionStrongStep S) none =
        (List.replicate n T ++ rest).foldl
          (originalOptionStrongStep S) (some T) := by
    rw [List.replicate_succ]
    rfl
  rw [hFirst, originalOptionStrongFold_some S,
    List.foldl_append, original_strong_fold_replicate S T n]

/-- C29 genuine strong endpoint spectrum of a labelled OLD ROOT PATH.
If the actual ordered edge-label list contains at least n+1 copies
of one label, and that menu's (n+1)-fold STRONG power equals K-diversity,
the STRONG product of ALL edges in their actual order is K-diversity.

The other edge menus are arbitrary NONEMPTY subsets of K-diversity.
No special first-factor assumption, atomic-word interior reordering,
CCO, quotient action or fake STRONG identity is used. -/
theorem original_labelled_strong_path_saturation
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (K : ColourEq S i) {r : Nat}
    (menus : Fin r → S.Menu i i)
    (labels : List (Fin r)) (target : Fin r) (n : Nat)
    (hCount : n+1 ≤ labels.count target)
    (hPower : originalStrongPalettePower S (menus target) n =
      originalEquivDiversityPalette S K)
    (hMenus : ∀ j : Fin r,
      (menus j).Nonempty ∧ menus j ⊆ originalEquivDiversityPalette S K) :
    originalPositiveStrongPath S (labels.map menus) =
      some (originalEquivDiversityPalette S K) := by
  obtain ⟨remaining, hPerm⟩ :=
    label_list_perm_replicate target labels (n+1) hCount
  have hPermMapped : (labels.map menus).Perm
      (List.replicate (n+1) (menus target) ++ remaining.map menus) := by
    simpa only [List.map_append, List.map_replicate] using hPerm.map menus
  unfold originalPositiveStrongPath
  rw [originalOptionStrongFold_perm S H sap none hPermMapped,
    originalOptionStrongFold_powers S (menus target) n (remaining.map menus),
    hPower]
  have hOthers : ∀ D ∈ remaining.map menus,
      D.Nonempty ∧ D ⊆ originalEquivDiversityPalette S K := by
    intro D hD
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hD
    exact hMenus j
  change some (originalKSpokePath S K (remaining.map menus)) =
    some (originalEquivDiversityPalette S K)
  exact congrArg Option.some
    (originalKSpokePath_absorbed S H sap K (remaining.map menus) hOthers)

end CCO.TerminalLattice
