import CCO.TerminalLattice.OriginalQuotientOWLEscapeStep
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-!
# B050 source09 OWL: finite escape has an ACTUAL nonempty periodic label product

The finite quotient escape state is invariant under a deterministic
successor constructed by the ORIGINAL CCO+SAP finite positive Helly
argument. This file isolates the purely finite combinatorics:

* a self-map of a finite state set eventually visits a periodic state;
* a labelled successor satisfying R(next s)=R(s);C(s) yields one
  genuine positive nonempty quotient relation product W along the
  periodic cycle with R(s);W=R(s).

There is NO assumption that the quotient carrier itself is finite,
no equality as an OLD positive STRONG letter, and no hidden
periodicity of any specific original-G quotient orbital. These
lemmas work for arbitrary binary relations on any carrier.
-/

namespace CCO.TerminalLattice

/-- Finite pigeonhole for a genuine self-map: every trajectory
eventually reaches a periodic point of POSITIVE period. Unlike a
surjectivity assumption, this permits transient states. -/
theorem original_finite_iterate_eventually_periodic
    {α : Type*} [Finite α] (f : α → α) (x : α) :
    ∃ k n : Nat, 0 < n ∧ f^[n] (f^[k] x) = f^[k] x := by
  classical
  obtain ⟨m,n,hmne,heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun k : Nat => f^[k] x)
  rcases lt_or_gt_of_ne hmne with hmn | hnm
  · refine ⟨m,n-m,by omega,?_⟩
    calc
      f^[n-m] (f^[m] x) = f^[(n-m)+m] x :=
        (Function.iterate_add_apply f (n-m) m x).symm
      _ = f^[n] x := by
        congr 1
        omega
      _ = f^[m] x := heq.symm
  · refine ⟨n,m-n,by omega,?_⟩
    calc
      f^[m-n] (f^[n] x) = f^[(m-n)+n] x :=
        (Function.iterate_add_apply f (m-n) n x).symm
      _ = f^[m] x := by
        congr 1
        omega
      _ = f^[n] x := heq

/-- Genuine associativity of ordinary quotient RELATION composition.
The witnesses are actual intermediate quotient points; no
representative choice or STRONG identity is invoked. -/
theorem original_relation_comp_assoc
    {Q : Type*} (A B C : Q → Q → Prop) :
    RawSymmetric.compose (RawSymmetric.compose A B) C =
      RawSymmetric.compose A (RawSymmetric.compose B C) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z,⟨mid,hAmid,hBz⟩,hCy⟩
    exact ⟨mid,hAmid,z,hBz,hCy⟩
  · rintro ⟨mid,hAmid,z,hBz,hCy⟩
    exact ⟨z,⟨mid,hAmid,hBz⟩,hCy⟩

/-- An ACTUAL ordered NONEMPTY product of one-step labels starting at
state s. Index n means n+1 genuine factors, so it cannot be an
invented zero-length STRONG product or a quotient identity factor. -/
def original_finite_labelled_product
    {α Q : Type*} (f : α → α) (label : α → Q → Q → Prop) :
    α → Nat → Q → Q → Prop
  | s, 0 => label s
  | s, n+1 =>
      RawSymmetric.compose (label s)
        (original_finite_labelled_product f label (f s) n)

/-- If one ACTUAL successor equals right-composition by its genuine
label, the (n+1)-st iterate equals right-composition by the literal
positive (n+1)-factor quotient product. This equation holds for
arbitrary finite or infinite carrier Q, without assuming positivity,
invariance, symmetry or original CCO. -/
theorem original_finite_labelled_run
    {α Q : Type*} (f : α → α)
    (label state : α → Q → Q → Prop)
    (hStep : ∀ s : α,
      state (f s) = RawSymmetric.compose (state s) (label s)) :
    ∀ s : α, ∀ n : Nat,
      state (f^[n+1] s) =
        RawSymmetric.compose (state s)
          (original_finite_labelled_product f label s n) := by
  intro s n
  induction n generalizing s with
  | zero =>
      simpa only [Function.iterate_one,
        original_finite_labelled_product] using hStep s
  | succ n ih =>
      calc
        state (f^[(n+1)+1] s) =
            state (f^[n+1] (f s)) := by
          rw [Function.iterate_succ_apply]
        _ = RawSymmetric.compose (state (f s))
              (original_finite_labelled_product f label (f s) n) :=
          ih (f s)
        _ = RawSymmetric.compose
              (RawSymmetric.compose (state s) (label s))
              (original_finite_labelled_product f label (f s) n) := by
          rw [hStep s]
        _ = RawSymmetric.compose (state s)
              (original_finite_labelled_product f label s (n+1)) := by
          change RawSymmetric.compose
              (RawSymmetric.compose (state s) (label s))
              (original_finite_labelled_product f label (f s) n) =
            RawSymmetric.compose (state s)
              (RawSymmetric.compose (label s)
                (original_finite_labelled_product f label (f s) n))
          exact original_relation_comp_assoc (state s)
            (label s) (original_finite_labelled_product f label (f s) n)

/-- SOURCE OWL finite recurrence, abstract deterministic form.
Every finite labelled escape system contains a REACHABLE state
whose original relation is unchanged by right-composition with a
genuine NONEMPTY product W of its successive labels.

The theorem does not assert that W is off-diagonal or has full
eventual powers; the source's complete external-orbital no-return
and genuine quotient-power theorem establish those separately. -/
theorem original_finite_labelled_periodic_relation
    {α Q : Type*} [Finite α]
    (f : α → α) (label state : α → Q → Q → Prop)
    (hStep : ∀ s : α,
      state (f s) = RawSymmetric.compose (state s) (label s))
    (initial : α) :
    ∃ k n : Nat,
      state (f^[k] initial) =
        RawSymmetric.compose (state (f^[k] initial))
          (original_finite_labelled_product f label
            (f^[k] initial) n) := by
  obtain ⟨k,d,hd,hPeriodic⟩ :=
    original_finite_iterate_eventually_periodic f initial
  let n : Nat := d-1
  have hNum : n+1=d := by
    dsimp [n]
    omega
  refine ⟨k,n,?_⟩
  have hRun :=
    original_finite_labelled_run f label state hStep
      (f^[k] initial) n
  rw [hNum,hPeriodic] at hRun
  exact hRun

end CCO.TerminalLattice
