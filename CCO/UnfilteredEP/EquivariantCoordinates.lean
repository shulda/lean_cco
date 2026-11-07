import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# B064 C14–C20: independent symmetry of equivariant coordinates

The hypotheses are precisely the independent G-set hypotheses A02/A03.
No terminal source, CCO, Ramsey, SAP or named quotient family is imported.
The finite-index obstruction ranges over every invariant setoid on the
actual source carrier; it is not restricted to a represented sublattice.
-/

universe u v w
namespace CCO.UnfilteredEP

variable {G : Type u} [Group G] {S : Type v} {B : Type w}
variable [MulAction G S] [MulAction G B]

/-- Every invariant binary relation on the source is symmetric. -/
def InvariantRelationsSymmetric (G : Type u) [Group G] (S : Type v)
    [MulAction G S] : Prop :=
  ∀ R : S → S → Prop,
    (∀ (g : G) x y, R x y → R (g • x) (g • y)) → ∀ x y, R x y → R y x

/-- Invariance here means invariance under the entire given group action. -/
def InvariantSetoid (E : Setoid S) : Prop :=
  ∀ g : G, ∀ x y, E x y → E (g • x) (g • y)

/-- The actual E-classes in the F-class of a specified source point. -/
def RelativeClasses (E F : Setoid S) (x : S) : Type v :=
  Quotient (E.comap (fun y : {y : S // F x y} => y.val))

/-- No strict invariant interval above E has finite relative index > 1.
`Nat.card` is zero on infinite carriers, so this forbids precisely the
finite indices greater than one, retaining infinite intervals. -/
def NoFiniteIntervalAbove (E : Setoid S) : Prop :=
  ∀ F : Setoid S, InvariantSetoid (G := G) F → E < F →
    ∀ x : S, ¬ 1 < Nat.card (RelativeClasses E F x)

/-- Symmetry identifies the two kernels, before any terminality is used. -/
theorem equivariant_surjections_kernel_eq
    (symmetry : InvariantRelationsSymmetric G S)
    (tau sigma : S → B)
    (htau : ∀ (g : G) x, tau (g • x) = g • tau x)
    (hsigma : ∀ (g : G) x, sigma (g • x) = g • sigma x)
    (ontoTau : Function.Surjective tau) (ontoSigma : Function.Surjective sigma) :
    Setoid.ker tau = Setoid.ker sigma := by
  have symmetric : ∀ x y, tau x = sigma y → tau y = sigma x :=
    symmetry (fun x y => tau x = sigma y) (by
      intro g x y h
      rw [htau, hsigma, h])
  apply Setoid.ext
  intro x y
  constructor
  · intro h
    obtain ⟨z,hz⟩ := ontoSigma (tau x)
    have hzx : tau z = sigma x := symmetric x z hz.symm
    have hzy : tau z = sigma y := symmetric y z (h.symm.trans hz.symm)
    exact hzx.symm.trans hzy
  · intro h
    obtain ⟨z,hz⟩ := ontoTau (sigma x)
    have hxz : tau x = sigma z := symmetric z x hz
    have hyz : tau y = sigma z := symmetric z y (hz.trans h)
    exact hxz.trans hyz.symm

/-- The same actual quotient admits one equivariant involution relating
both onto coordinate maps. Kernel equality is proved rather than assumed. -/
theorem equivariant_surjections_involution
    (symmetry : InvariantRelationsSymmetric G S)
    (tau sigma : S → B)
    (htau : ∀ (g : G) x, tau (g • x) = g • tau x)
    (hsigma : ∀ (g : G) x, sigma (g • x) = g • sigma x)
    (ontoTau : Function.Surjective tau) (ontoSigma : Function.Surjective sigma) :
    ∃ f : B → B,
      (∀ x, f (tau x) = sigma x) ∧
      (∀ (g : G) b, f (g • b) = g • f b) ∧
      Function.Involutive f ∧ Function.Bijective f := by
  classical
  have hker := equivariant_surjections_kernel_eq symmetry tau sigma
    htau hsigma ontoTau ontoSigma
  let rep : B → S := fun b => (ontoTau b).choose
  have hrep (b : B) : tau (rep b) = b := (ontoTau b).choose_spec
  let f : B → B := fun b => sigma (rep b)
  have hfactor (x : S) : f (tau x) = sigma x := by
    have h : Setoid.ker tau (rep (tau x)) x := hrep _
    rw [hker] at h
    exact h
  have hequiv (g : G) (b : B) : f (g • b) = g • f b := by
    obtain ⟨x,rfl⟩ := ontoTau b
    rw [← htau, hfactor, hsigma, hfactor]
  have symmetric : ∀ x y, tau x = sigma y → tau y = sigma x :=
    symmetry (fun x y => tau x = sigma y) (by
      intro g x y h
      rw [htau, hsigma, h])
  have hinv : Function.Involutive f := by
    intro b
    obtain ⟨x,hx⟩ := ontoTau (f b)
    obtain ⟨y,hy⟩ := ontoTau b
    have hxy : tau x = sigma y := hx.trans ((congrArg f hy).symm.trans (hfactor y))
    have hyx := symmetric x y hxy
    calc
      f (f b) = f (tau x) := congrArg f hx.symm
      _ = sigma x := hfactor x
      _ = tau y := hyx.symm
      _ = b := hy
  exact ⟨f,hfactor,hequiv,hinv,hinv.bijective⟩

/-- Pulling the two-point involution orbits back to the source gives
an actual invariant source equivalence containing the coordinate kernel. -/
def involutionPullback (tau : S → B) (f : B → B)
    (hinv : Function.Involutive f) : Setoid S where
  r x y := tau y = tau x ∨ tau y = f (tau x)
  iseqv := {
    refl x := Or.inl rfl
    symm := by
      intro x y h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr ((hinv _).symm.trans (congrArg f h).symm)
    trans := by
      intro x y z hxy hyz
      rcases hxy with hx | hx <;> rcases hyz with hy | hy
      · exact Or.inl (hy.trans hx)
      · exact Or.inr (hy.trans (congrArg f hx))
      · exact Or.inr (hy.trans hx)
      · exact Or.inl (hy.trans ((congrArg f hx).trans (hinv _))) }

theorem involutionPullback_invariant
    (tau : S → B) (f : B → B) (hinv : Function.Involutive f)
    (htau : ∀ (g : G) x, tau (g • x) = g • tau x)
    (hf : ∀ (g : G) b, f (g • b) = g • f b) :
    InvariantSetoid (G := G) (involutionPullback tau f hinv) := by
  intro g x y h
  rcases h with h | h
  · exact Or.inl ((htau g y).trans ((congrArg (fun b => g • b) h).trans (htau g x).symm))
  · right
    calc
      tau (g • y) = g • tau y := htau g y
      _ = g • f (tau x) := congrArg (fun b => g • b) h
      _ = f (g • tau x) := (hf g _).symm
      _ = f (tau (g • x)) := congrArg f (htau g x).symm

/-- The literal pulled-back interval has exactly two coordinate classes
in each class whenever the involution is fixed-point-free. -/
theorem involutionPullback_relative_card_two
    (tau : S → B) (onto : Function.Surjective tau)
    (f : B → B) (hinv : Function.Involutive f)
    (hfree : ∀ b, f b ≠ b) (x : S) :
    Nat.card (RelativeClasses (Setoid.ker tau) (involutionPullback tau f hinv) x) = 2 := by
  classical
  let E := Setoid.ker tau
  let F := involutionPullback tau f hinv
  obtain ⟨y,hy⟩ := onto (f (tau x))
  let qx : RelativeClasses E F x := Quotient.mk _ ⟨x,Or.inl rfl⟩
  let qy : RelativeClasses E F x := Quotient.mk _ ⟨y,Or.inr hy⟩
  apply Nat.card_eq_two_iff.mpr
  refine ⟨qx,qy,?_,?_⟩
  · intro h
    have he : tau x = tau y := Quotient.exact h
    exact hfree (tau x) (hy.symm.trans he.symm)
  · apply Set.eq_univ_iff_forall.mpr
    intro q
    refine Quotient.inductionOn q ?_
    intro z
    rcases z.property with hz | hz
    · exact Or.inl (Quotient.sound hz)
    · exact Or.inr (Quotient.sound (hz.trans hy.symm))

/-- A nonidentity equivariant involution on a transitive target is
fixed-point-free. This uses actual transitivity, not finiteness. -/
theorem equivariant_involution_fixed_point_free
    (transitive : ∀ b c : B, ∃ g : G, g • b = c)
    (f : B → B) (hf : ∀ (g : G) b, f (g • b) = g • f b)
    (hne : ∃ b, f b ≠ b) : ∀ b, f b ≠ b := by
  obtain ⟨c,hc⟩ := hne
  intro b hb
  obtain ⟨g,hg⟩ := transitive b c
  exact hc (by rw [← hg,hf,hb])

/-- Full A03 excludes the actual two-sheet interval produced by the
involution. The resulting coordinate equality is literal equality of maps. -/
theorem equivariant_surjections_eq
    (symmetry : InvariantRelationsSymmetric G S)
    (transitive : ∀ b c : B, ∃ g : G, g • b = c)
    (tau sigma : S → B)
    (htau : ∀ (g : G) x, tau (g • x) = g • tau x)
    (hsigma : ∀ (g : G) x, sigma (g • x) = g • sigma x)
    (ontoTau : Function.Surjective tau) (ontoSigma : Function.Surjective sigma)
    (noFinite : NoFiniteIntervalAbove (G := G) (Setoid.ker tau)) :
    sigma = tau := by
  classical
  obtain ⟨f,hfactor,hf,hinv,_⟩ := equivariant_surjections_involution
    symmetry tau sigma htau hsigma ontoTau ontoSigma
  have hid : ∀ b, f b = b := by
    by_contra hn
    have hne : ∃ b, f b ≠ b := by simpa only [not_forall] using hn
    have hfree := equivariant_involution_fixed_point_free transitive f hf hne
    obtain ⟨b,hb⟩ := hne
    obtain ⟨x,hx⟩ := ontoTau b
    let F := involutionPullback tau f hinv
    have hEF : Setoid.ker tau ≤ F := fun _ _ h => Or.inl h.symm
    have hstrict : Setoid.ker tau < F := by
      refine lt_of_le_of_ne hEF ?_
      intro hEq
      obtain ⟨y,hy⟩ := ontoTau (f b)
      have hxy : F x y := Or.inr (hy.trans (congrArg f hx).symm)
      rw [← hEq] at hxy
      have he : tau x = tau y := hxy
      exact hb (hy.symm.trans (he.symm.trans hx))
    have hcard := involutionPullback_relative_card_two tau ontoTau f hinv hfree x
    exact noFinite F (involutionPullback_invariant tau f hinv htau hf) hstrict x
      (by rw [hcard]; decide)
  funext x
  exact (hfactor x).symm.trans (hid (tau x))

end CCO.UnfilteredEP
