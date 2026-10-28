import CCO.RawExact.AtomicExact
import CCO.RawExact.Balls

/-!
# B002 C12–C13: exact-ball singleton and identity boundaries

These lemmas remove identity-only restrictions before constructing a
private-path fan. An actual equality word yields the singleton ball
at its real centre, not a diversity edge. Pairwise intersection with
that ball forces its unique point into every other ball, regardless
of the number of constraints, original sort labels or repeated centres.

No CCO, homogeneity, SAP or exact convolution is used.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- An equality word gives exactly one real point as its ball.
The target and centre have the SAME named original sort. -/
theorem ball_exactIdentity_eq_singleton (i : ι) (b : X i) :
    ball (evaluate S (exactIdentityAtom S i).words) b = {b} := by
  ext x
  change evaluate S (exactIdentityAtom S i).words x b ↔ x = b
  rw [exactIdentityAtom_relation S i]
  rfl

/-- A family whose one ball is a singleton satisfies Helly using only
pairwise intersections with that singleton ball. This holds even for
infinitely many balls; no finiteness or CCO is needed for this case. -/
theorem exactBallFamily_helly_of_singleton
    {I : Type*} {root : ι}
    (centreSort : I → ι)
    (D : ∀ t : I, NonemptyExact S root (centreSort t))
    (centres : ∀ t : I, X (centreSort t))
    (t₀ : I) (anchor : X root)
    (hSingle : ∀ x : X root,
      evaluate S (D t₀).words x (centres t₀) ↔ x = anchor)
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty) :
    ∃ x : X root, ∀ t : I, evaluate S (D t).words x (centres t) := by
  refine ⟨anchor, ?_⟩
  intro t
  obtain ⟨x, hx⟩ := hPair t₀ t
  have hxa : x = anchor := (hSingle x).mp hx.1
  exact hxa ▸ hx.2

/-- Exactly the same boundary for a finite presentation containing
the zero-length RAW loop word. A nonempty exact menu with this member
is contained in the actual diagonal; there is no fake STRONG Id. -/
theorem exact_loop_menu_ball_subsingleton
    {i : ι} (D : NonemptyExact S i i)
    (hEmpty : RawWord.nil i ∈ D.words)
    (b : X i) (x : X i)
    (hx : evaluate S D.words x b) :
    x = b := by
  have h := hx (RawWord.nil i) hEmpty
  change x = b at h
  exact h

/-- For the zero-word boundary, an actually nonempty ball is exactly
the singleton of its centre, even if its presentation contains
additional positive words with logical identity in their outputs. -/
theorem exact_loop_menu_ball_eq_singleton
    {i : ι} (D : NonemptyExact S i i)
    (hEmpty : RawWord.nil i ∈ D.words)
    (b : X i)
    (hBall : (ball (evaluate S D.words) b).Nonempty) :
    ball (evaluate S D.words) b = {b} := by
  ext x
  constructor
  · intro hx
    exact exact_loop_menu_ball_subsingleton S D hEmpty b x hx
  · intro hx
    obtain ⟨y, hy⟩ := hBall
    have hyb : y = b :=
      exact_loop_menu_ball_subsingleton S D hEmpty b y hy
    have hxb : x = b := hx
    subst x
    subst y
    exact hy

end CCO.RawExact
