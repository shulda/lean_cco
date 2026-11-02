import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Omega

/-!
# B052 source10 C17–C21: malformed long unary transition cycles

For n>=2, consider quotient-only partial sources with exactly n
points x_i of sort QA and n points y_i of sort QB, no real roots,
and named total unary functions f(x_i)=y_i,
g(y_i)=x_(i+1 mod n).

The cyclic permutation is the actual finRotate n. It is a
single full orbit, so every NONEMPTY unary-functionally closed
two-sort substructure is the entire 2n-point source. These
sources are consequently irreducible in the elementary unary
free-amalgam sense, independently of any displayed binary edges.

In an ACTUAL completed hidden common-block structure the named
inverse terms satisfy g∘f=id on QA. Every function-preserving
map from this malformed source to such an actual member
therefore identifies consecutive distinct x-points. In
particular it cannot be a homomorphism-embedding of the
irreducible source. These are UNBOUNDED counterexamples to
an arbitrary-total-unary partial-input obstruction bound,
NOT examples satisfying unary-admissibility.

The separate B052 duty to build the original genuine
two-sort common-block SAP+CCO ambient source and to verify
the completed hidden binary predicate interpretation is
NOT inferred from these elementary cycle calculations.
-/

namespace CCO.UnaryTermsReturn

/-- The actual malformed g∘f step on the quotient QA
vertices, all of which are indexed modulo n. -/
def malformedCycleStep (n : Nat) : Fin n → Fin n :=
  finRotate n

/-- For every n>=2, the malformed return step has no fixed
quotient point. This uses the FULL support of the pinned
Mathlib finite-cycle permutation, not an assumed orbit property. -/
theorem malformed_cycle_step_ne_self
    {n : Nat} (hn : 2 ≤ n) (i : Fin n) :
    malformedCycleStep n i ≠ i := by
  have hMem : i ∈ (finRotate n).support := by
    rw [support_finRotate_of_le hn]
    simp
  simpa only [malformedCycleStep, Equiv.Perm.mem_support] using hMem

/-- A finite TWO-SORT partial unary substructure is
functionally closed exactly when f sends each kept x_i
to kept y_i, and g sends each kept y_i to kept
x_(i+1). No binary relation is needed for this test. -/
def MalformedCycleClosed {n : Nat}
    (A B : Set (Fin n)) : Prop :=
  (∀ i : Fin n, i ∈ A → i ∈ B) ∧
  (∀ i : Fin n, i ∈ B → malformedCycleStep n i ∈ A)

/-- B052 C17/C18: ANY nonempty functionally closed pair
of quotient-sort subsets must be FULL in both sorts.
The orbit argument works from an arbitrary starting x_i
or y_i, not just the distinguished vertex 0. -/
theorem malformed_cycle_closed_nonempty_is_full
    {n : Nat} (hn : 2 ≤ n)
    (A B : Set (Fin n))
    (hClosed : MalformedCycleClosed A B)
    (hne : A.Nonempty ∨ B.Nonempty) :
    A = Set.univ ∧ B = Set.univ := by
  obtain ⟨i,hi⟩ : ∃ i : Fin n, i ∈ A := by
    rcases hne with ⟨i,hi⟩ | ⟨j,hj⟩
    · exact ⟨i,hi⟩
    · exact ⟨malformedCycleStep n j,hClosed.2 j hj⟩
  have hPow : ∀ k : Nat, (finRotate n ^ k) i ∈ A := by
    intro k
    induction k with
    | zero =>
        simpa using hi
    | succ k ih =>
        have hNext : malformedCycleStep n ((finRotate n ^ k) i) ∈ A :=
          hClosed.2 _ (hClosed.1 _ ih)
        simpa only [malformedCycleStep,pow_succ',Equiv.Perm.mul_apply]
          using hNext
  have hCycle := isCycle_finRotate_of_le hn
  have hFullA : A = Set.univ := by
    apply Set.eq_univ_of_forall
    intro j
    obtain ⟨k,hk⟩ :=
      hCycle.exists_pow_eq
        (malformed_cycle_step_ne_self hn i)
        (malformed_cycle_step_ne_self hn j)
    rw [← hk]
    exact hPow k
  refine ⟨hFullA,?_⟩
  apply Set.eq_univ_of_forall
  intro j
  exact hClosed.1 j (by rw [hFullA]; trivial)

/-- The actual source has 2n tagged quotient points.
No real point or extra displayed binary orbital is inserted. -/
theorem malformed_cycle_carrier_card (n : Nat) :
    Fintype.card (Fin n ⊕ Fin n) = 2 * n := by
  simp [Fintype.card_sum, Nat.two_mul]

/-- Actual completed inverse transition identities force every
function-preserving map from the malformed cycle to identify
x_i with x_(i+1). Source images hA and hB preserve the real
named f and g separately. -/
theorem malformed_cycle_forced_collapse
    {n : Nat} {A B : Type*}
    (f : A → B) (g : B → A)
    (hInverse : ∀ x : A, g (f x) = x)
    (hA : Fin n → A) (hB : Fin n → B)
    (hF : ∀ i : Fin n, hB i = f (hA i))
    (hG : ∀ i : Fin n, hA (malformedCycleStep n i) = g (hB i))
    (i : Fin n) :
    hA (malformedCycleStep n i) = hA i := by
  rw [hG i,hF i,hInverse]

/-- B052 C19: no injective interpretation (hence no
homomorphism-embedding of an irreducible source) in any
genuine completed hidden member with the literal named
inverse g∘f=id. This argument does not presuppose
a hidden-SAP construction or unbounded closure theorem. -/
theorem malformed_cycle_no_injective_completion
    {n : Nat} (hn : 2 ≤ n)
    {A B : Type*}
    (f : A → B) (g : B → A)
    (hInverse : ∀ x : A, g (f x) = x)
    (hA : Fin n → A) (hB : Fin n → B)
    (hF : ∀ i : Fin n, hB i = f (hA i))
    (hG : ∀ i : Fin n, hA (malformedCycleStep n i) = g (hB i)) :
    ¬ Function.Injective hA := by
  intro hInjective
  have hpos : 0 < n := by omega
  let i : Fin n := ⟨0,hpos⟩
  have hBad := malformed_cycle_step_ne_self hn i
  exact hBad (hInjective
    (malformed_cycle_forced_collapse f g hInverse hA hB hF hG i))

/-- The sizes of irreducible, non-completable malformed
partial unary cycles are unbounded. The construction uses
n=N+2 so that n>=2 and the full carrier has 2n>N
elements; all its proper unary-closed nonempty pieces
are impossible by the preceding full-orbit lemma. -/
theorem malformed_cycle_arbitrarily_large
    (N : Nat) :
    ∃ n : Nat, 2 ≤ n ∧ N < Fintype.card (Fin n ⊕ Fin n) := by
  refine ⟨N+2,by omega,?_⟩
  rw [malformed_cycle_carrier_card]
  omega

end CCO.UnaryTermsReturn
