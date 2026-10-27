import CCO.RawExact.PrivatePaths
import CCO.RawExact.Balls
import CCO.RawExact.QuotientRequests

/-!
# B002 C20: finite simultaneous original-real-point extension core

The pairwise ambient-orbit transport is proved with genuine group elements.
Exactly TWO providers are visible: (1) represented nonempty exact
presentations of the actual mixed real-to-quotient requests (from C09/C19)
and (2) heterogeneous exact-ball Helly (from C13). No unproved provider
is promoted to an unconditional source theorem. The full finite partial
isomorphism and back-and-forth are separate downstream obligations.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X)

/-- The source-strength C13 provider, stated for finite families with
one common original target sort but arbitrary original centre sorts.
Every D t includes its real-pair witness. Pairwise conditions include
equal indices; the requested C13 theorem will discharge them using
ordinary seriality in the zero/one-element boundaries. -/
def HeterogeneousExactBallHelly : Prop :=
  ∀ {I : Type} [Fintype I] {m : ι}
    (sort : I → ι)
    (D : ∀ t : I, NonemptyExact S m (sort t))
    (centres : ∀ t : I, X (sort t)),
    (∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty) →
    ∃ y : X m, ∀ t : I, evaluate S (D t).words y (centres t)

/-- Given a finite family of actual quotient parameters with all
pair orbitals preserved, pairwise compatible old ambient motions
yield exact balls with pairwise intersections. Heterogeneous Helly
then realizes ALL new real-to-quotient orbital requests simultaneously.
This is the substantive gluing step of source C20, conditional only on
the separately allocated C09/C13 providers. -/
theorem joint_real_point_requests_of_ball_helly
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
    {I : Type} [Fintype I] {m : ι}
    (sort : I → ι) (Q : I → Type w)
    [∀ t : I, MulAction G (Q t)]
    (π : ∀ t : I, X (sort t) → Q t)
    (x : X m)
    (source target : ∀ t : I, Q t)
    (targetRepresentatives : ∀ t : I, X (sort t))
    (hTarget : ∀ t, π t (targetRepresentatives t) = target t)
    (hPairOrbit : ∀ p q : I,
      GroupActions.orbital (G := G)
        (source p) (source q) (target p) (target q))
    (D : ∀ t : I, NonemptyExact S m (sort t))
    (hExactRequest : ∀ t : I,
      evaluate S (D t).words =
        GroupActions.pullback (fun y : X m => y) (π t)
          (GroupActions.orbital (G := G) x (source t)))
    (hHelly : HeterogeneousExactBallHelly S) :
    ∃ y : X m, ∀ t : I,
      GroupActions.orbital (G := G) x (source t) y (target t) := by
  have hPairBalls : ∀ p q : I,
      (ball (evaluate S (D p).words) (targetRepresentatives p) ∩
        ball (evaluate S (D q).words) (targetRepresentatives q)).Nonempty := by
    intro p q
    obtain ⟨g, hgp, hgq⟩ := hPairOrbit p q
    refine ⟨g • x, ?_, ?_⟩
    · change evaluate S (D p).words (g • x) (targetRepresentatives p)
      rw [hExactRequest p]
      change GroupActions.orbital (G := G)
        x (source p) (g • x) (π p (targetRepresentatives p))
      rw [hTarget p]
      exact ⟨g, rfl, hgp⟩
    · change evaluate S (D q).words (g • x) (targetRepresentatives q)
      rw [hExactRequest q]
      change GroupActions.orbital (G := G)
        x (source q) (g • x) (π q (targetRepresentatives q))
      rw [hTarget q]
      exact ⟨g, rfl, hgq⟩
  obtain ⟨y, hy⟩ := hHelly sort D targetRepresentatives hPairBalls
  refine ⟨y, ?_⟩
  intro t
  have h := hy t
  rw [hExactRequest t] at h
  change GroupActions.orbital (G := G)
    x (source t) y (π t (targetRepresentatives t)) at h
  rwa [hTarget t] at h

/-- C20's genuine injectivity guard for an already displayed original
real parameter: an orbital of a DISTINCT old pair cannot be mapped to
a collision by a group automorphism. This is independent of Helly,
SAP and any hypothetical freshness axiom. -/
theorem real_orbital_excludes_collision
    {G A : Type*} [Group G] [MulAction G A]
    (x c y b : A) (hDistinct : x ≠ c)
    (hOrbit : GroupActions.orbital (G := G) x c y b) :
    y ≠ b := by
  intro hyb
  obtain ⟨g, hgx, hgc⟩ := hOrbit
  have hEq : g • x = g • c :=
    hgx.trans (hyb.trans hgc.symm)
  have hinv := congrArg (fun t : A => g⁻¹ • t) hEq
  have hxc : x = c := by
    simpa only [inv_smul_smul] using hinv
  exact hDistinct hxc

end CCO.RawExact
