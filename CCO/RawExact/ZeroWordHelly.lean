import CCO.RawExact.WordOccurrences
import CCO.RawExact.ZeroWordBoundary
import CCO.RawExact.IdentityBalls

/-!
# B002 C12/C13: dispose of ALL genuine zero-length word restrictions

An arbitrary finite full-exact menu may contain a RAW word consisting
only of logical identity letters, including several consecutive ones.
This one restriction forces the actual target and centre points to be
the same TAGGED real point. Pairwise ball intersections therefore
give a common point for the whole family, without constructing any
edge from the formal root to a distinct centre.

Crucially this case is about zero diversity LETTERS, not about
diagonal OUTPUTS of nonempty positive words.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- If an actual menu contains a zero-diversity word, all points
in its ball are equal. The statement has one fixed target sort;
the centre may have been introduced under a dependent sort label. -/
theorem zero_word_ball_subsingleton
    {root j : ι} (D : NonemptyExact S root j)
    (centre : X j)
    (word : RawWord S root j)
    (hmem : word ∈ D.words)
    (hzero : diversityLength S word = 0)
    (x y : X root)
    (hx : evaluate S D.words x centre)
    (hy : evaluate S D.words y centre) :
    x = y := by
  have hxtag : (⟨root, x⟩ : Sigma X) = ⟨j, centre⟩ :=
    (zeroLength_relation_iff_tagged_eq S word hzero x centre).mp
      (hx word hmem)
  have hytag : (⟨root, y⟩ : Sigma X) = ⟨j, centre⟩ :=
    (zeroLength_relation_iff_tagged_eq S word hzero y centre).mp
      (hy word hmem)
  have hxy : (⟨root, x⟩ : Sigma X) = ⟨root, y⟩ :=
    hxtag.trans hytag.symm
  simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hxy

/-- A full C13 boundary case: any zero-diversity word occurrence in
one of the actual menus forces the ENTIRE finite family of exact
balls to have a common witness, if the balls meet pairwise.
This includes repeated real centres, arbitrary original sort
labels and every equality-letter insertion. -/
theorem exact_ball_helly_of_zero_word_occurrence
    {root : ι} {I : Type (max u v)} [Finite I]
    (sort : I → ι)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty)
    (t₀ : I)
    (word : RawWord S root (sort t₀))
    (hmem : word ∈ (D t₀).words)
    (hzero : diversityLength S word = 0) :
    ∃ x : X root, ∀ t : I,
      evaluate S (D t).words x (centres t) := by
  obtain ⟨anchor, hAnchor, _⟩ := hPair t₀ t₀
  have hSingleton : ∀ y : X root,
      evaluate S (D t₀).words y (centres t₀) ↔ y = anchor := by
    intro y
    constructor
    · intro hy
      exact (zero_word_ball_subsingleton S (D t₀)
        (centres t₀) word hmem hzero y anchor hy hAnchor)
    · rintro rfl
      exact hAnchor
  exact exactBallFamily_helly_of_singleton S
    sort D centres t₀ anchor hSingleton hPair

end CCO.RawExact
