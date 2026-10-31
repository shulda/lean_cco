import CCO.RigidGroupoid.Geometry.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Lean.Elab.Tactic.Omega

/-!
# B062 / C32: original RAW exact powers stabilize without SAP

Every genuine equality-inclusive original RAW exact relation has exact
positive powers by the accepted original ExactCalculus. If it contains
the ORIGINAL diagonal, the powers increase. Since the ACTUAL source
has finitely many full-exact relations (finite optional pair orbitals),
the infinite sequence of powers repeats, and monotonicity forces two
successive powers to agree. That stable power is an original full-exact
equivalence, not an arbitrary invariant equivalence and not an assumed
finite-index quotient.

The later C32 step showing its precise marked trace equals a prescribed
current exact equivalence, and iteration across prefixes, remains open.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open RigidGroupoid.Geometry
noncomputable section

variable {ι : Type u} {X : ι → Type v}

/-- The genuine positive RAW powers: exponent zero means one factor R,
not the empty word / logical identity. It is an actual relation on the
one original source sort with explicit witnesses at every composition. -/
def originalPower {i : ι} (R : TRel X i i) : ℕ → TRel X i i
  | 0 => R
  | n + 1 => TRel.comp (originalPower R n) R

/-- Source C32 exactness of every positive power, from the accepted
original equality-inclusive convolution calculus alone. -/
theorem originalPower_exact
    (S : AtomicSource.{u,v,w} ι X) (C : ExactCalculus S)
    {i : ι} (R : TRel X i i) (hR : FullExact S R) :
    ∀ n, FullExact S (originalPower R n) := by
  intro n
  induction n with
  | zero => exact hR
  | succ n ih => exact C.comp ih hR

/-- Genuine old diagonal witnesses persist in every positive power. -/
theorem originalPower_reflexive {i : ι} (R : TRel X i i)
    (hRefl : ∀ x, R x x) (n : ℕ) :
    ∀ x, originalPower R n x x := by
  induction n with
  | zero => exact hRefl
  | succ n ih =>
      intro x
      exact ⟨x, ih x, hRefl x⟩

/-- If R contains old Id, adding a genuine last R-edge never loses a
pair: use the actual second endpoint as the middle witness. -/
theorem originalPower_step {i : ι} (R : TRel X i i)
    (hRefl : ∀ x, R x x) (n : ℕ) :
    ∀ x y, originalPower R n x y → originalPower R (n+1) x y := by
  intro x y hxy
  exact ⟨y,hxy,hRefl y⟩

/-- Nondecreasing positive RAW powers, via the exact natural-index order. -/
theorem originalPower_mono {i : ι} (R : TRel X i i)
    (hRefl : ∀ x, R x x) {n m : ℕ} (hnm : n ≤ m) :
    ∀ x y, originalPower R n x y → originalPower R m x y := by
  induction hnm with
  | refl =>
      exact fun _ _ hxy => hxy
  | @step k _ ih =>
      intro x y hxy
      exact originalPower_step R hRefl k x y (ih x y hxy)

/-- Every double RAW path in the powers is precisely one longer power.
The shift by one reflects the convention originalPower R 0 = R. -/
theorem originalPower_comp {i : ι} (R : TRel X i i) (n m : ℕ) :
    TRel.comp (originalPower R n) (originalPower R m) =
      originalPower R (n+m+1) := by
  induction m with
  | zero =>
      simp only [Nat.add_zero]
      rfl
  | succ m ih =>
      calc
        TRel.comp (originalPower R n) (originalPower R (m+1)) =
            TRel.comp (originalPower R n)
              (TRel.comp (originalPower R m) R) := rfl
        _ = TRel.comp
              (TRel.comp (originalPower R n) (originalPower R m)) R :=
          (TRel.comp_assoc _ _ _).symm
        _ = TRel.comp (originalPower R (n+m+1)) R := by rw [ih]
        _ = originalPower R (n+m+1+1) := rfl
        _ = originalPower R (n+(m+1)+1) := by congr 1

/-- Equalities of two separated powers in an increasing chain force
an adjacent equality already at the earlier index. -/
theorem originalPower_step_of_repeat {i : ι} (R : TRel X i i)
    (hRefl : ∀ x, R x x) {n m : ℕ} (hnm : n < m)
    (hEq : originalPower R n = originalPower R m) :
    originalPower R n = originalPower R (n+1) := by
  funext x y
  apply propext
  constructor
  · exact originalPower_step R hRefl n x y
  · intro hxy
    have hToM : originalPower R m x y :=
      originalPower_mono R hRefl (Nat.succ_le_of_lt hnm) x y hxy
    rw [← hEq] at hToM
    exact hToM

/-- Once adjacent powers agree, all later positive powers are literally
the same actual old relation. -/
theorem originalPower_stable {i : ι} (R : TRel X i i)
    (n : ℕ) (h : originalPower R n = originalPower R (n+1))
    (k : ℕ) : originalPower R (n+k) = originalPower R n := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        originalPower R (n+(k+1)) =
            TRel.comp (originalPower R (n+k)) R := by
              rw [Nat.add_succ]
              rfl
        _ = TRel.comp (originalPower R n) R := by rw [ih]
        _ = originalPower R (n+1) := rfl
        _ = originalPower R n := h.symm

/-- The SOURCE finiteness argument of C32. This is genuine finiteness
of the actual FULL-exact original relations, not finite index of an
equivalence or a quotient-SAP input. -/
theorem originalPower_stabilizes
    (S : AtomicSource.{u,v,w} ι X)
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (C : ExactCalculus S)
    {i : ι} (R : TRel X i i)
    (hExact : FullExact S R) (hRefl : ∀ x, R x x) :
    ∃ n : ℕ, originalPower R n = originalPower R (n+1) := by
  letI : Finite {T : TRel X i i // FullExact S T} :=
    finite_fullExact S H i i
  let f : ℕ → {T : TRel X i i // FullExact S T} :=
    fun n => ⟨originalPower R n,originalPower_exact S C R hExact n⟩
  obtain ⟨n,m,hnm,heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hPow : originalPower R n = originalPower R m :=
    congrArg Subtype.val heq
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact ⟨n,originalPower_step_of_repeat R hRefl hlt hPow⟩
  · exact ⟨m,originalPower_step_of_repeat R hRefl hgt hPow.symm⟩

/-- A stable, reflexive, same-original-sort RAW exact power is a genuine
old invariant equivalence. Symmetry comes from the actual pair-flipping
homogeneous source; transitivity follows from exact path concatenation
and stable powers, never from an alleged quotient action. -/
theorem originalPower_equiv_of_stable
    (S : AtomicSource.{u,v,w} ι X)
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (C : ExactCalculus S)
    {i : ι} (R : TRel X i i)
    (hExact : FullExact S R) (hRefl : ∀ x, R x x)
    (n : ℕ) (hStable : originalPower R n = originalPower R (n+1)) :
    RawSymmetric.EquivRel (originalPower R n) := by
  have hInv : TRel.Invariant (G := G) (originalPower R n) :=
    (originalPower_exact S C R hExact n).invariant S H
  have hSym : TRel.converse (originalPower R n) =
      originalPower R n :=
    invariant_same_sort_converse S H (originalPower R n) hInv
  have hComp :
      TRel.comp (originalPower R n) (originalPower R n) =
        originalPower R n := by
    calc
      _ = originalPower R (n+n+1) := originalPower_comp R n n
      _ = originalPower R n := by
        simpa only [Nat.add_assoc] using
          (originalPower_stable R n hStable (n+1))
  refine ⟨?_, ?_, ?_⟩
  · exact originalPower_reflexive R hRefl n
  · intro x y hxy
    have hh : TRel.converse (originalPower R n) y x := hxy
    rw [hSym] at hh
    exact hh
  · intro x y z hxy hyz
    have hh : TRel.comp (originalPower R n)
        (originalPower R n) x z := ⟨y,hxy,hyz⟩
    rw [hComp] at hh
    exact hh

/-- The substantial old ORIGINAL part of C32: every equality-inclusive
RAW exact relation containing old Id lies inside an original FULL-exact
equivalence obtained as one of its ACTUAL positive powers. This is an
unconditional source instance using only accepted HOM+CCO calculus,
not a conditional assumed stabilization provider. -/
theorem original_exact_equivalence_envelope
    (S : AtomicSource.{u,v,w} ι X)
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (C : ExactCalculus S)
    {i : ι} (D : RawExact.NonemptyExact S i i)
    (hRefl : ∀ x, RawExact.evaluate S D.words x x) :
    ∃ Q : TRel X i i,
      FullExact S Q ∧ RawSymmetric.EquivRel Q ∧
        (∀ x y, RawExact.evaluate S D.words x y → Q x y) := by
  let R := RawExact.evaluate S D.words
  have hFull : FullExact S R := ⟨D,rfl⟩
  obtain ⟨n,hStable⟩ := originalPower_stabilizes S H C R hFull hRefl
  refine ⟨originalPower R n, originalPower_exact S C R hFull n,
    originalPower_equiv_of_stable S H C R hFull hRefl n hStable, ?_⟩
  intro x y hxy
  exact originalPower_mono R hRefl (Nat.zero_le n) x y hxy

end
end CCO.ExactEPGeometry
