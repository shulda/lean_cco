import CCO.RawExact.FanCCOCompletion
import CCO.RawExact.FanCentreColours
import CCO.RawExact.FanHomWords
import CCO.RawExact.ZeroWordHelly
import CCO.RawExact.JointPoint
import CCO.RawExact.Convolution

/-!
# Full heterogeneous exact-ball Helly from original source CCO

A zero-diversity restriction makes its ball a singleton and is handled
directly. Otherwise the completed anchored fan realizes every original
RAW word at its root image. The full old centre diagram is preserved,
so one original automorphism puts all marked centres back at their
literal given values. Its image of the root satisfies every menu.

This proves the full C13 provider without a Helly premise, SAP,
quotient homogeneity, or an assumed quotient section.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Original homogeneity and semantic CCO give a common point for
any finite pairwise-intersecting family of full exact balls. Centre
sorts, repeated centre values and all RAW identity letters are retained. -/
theorem exact_ball_helly_of_CCO
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {root : ι} {I : Type (max u v)} [Finite I]
    (sort : I → ι)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty) :
    ∃ x : X root, ∀ t : I, evaluate S (D t).words x (centres t) := by
  classical
  by_cases hZero : ∃ o : WordOccurrence S D,
      diversityLength S (occurrenceWord S D o) = 0
  · obtain ⟨o, ho⟩ := hZero
    exact exact_ball_helly_of_zero_word_occurrence S sort D centres hPair
      o.1 (occurrenceWord S D o) (occurrenceWord_mem S D o) ho
  · obtain ⟨f⟩ := privateFanFull_completion_of_CCO S H cco D centres hPair
    obtain ⟨g, hg⟩ := privateFanFullHom_align_all_centres S H D centres f
    refine ⟨g • f.point (privateFanRoot S D centres), ?_⟩
    intro t word hWord
    obtain ⟨k, hk⟩ := List.get_of_mem hWord
    let o : WordOccurrence S D := ⟨t, k⟩
    have hPositive : 0 < diversityLength S (occurrenceWord S D o) :=
      Nat.pos_of_ne_zero (fun h => hZero ⟨o, h⟩)
    have hRelation := privateFanHom_word_relation S H D centres hPair f o hPositive
    have hTransport := word_invariant_of_homogeneous S H
      (occurrenceWord S D o) g _ _ hRelation
    have hCentre := hg (toDistinctCentre sort centres t)
    change g • f.point
      (privateFanCentre S D centres (toDistinctCentre sort centres t)) = centres t at hCentre
    change RawWord.relation S ((D t).words.get k)
      (g • f.point (privateFanRoot S D centres))
      (g • f.point (privateFanCentre S D centres (toDistinctCentre sort centres t)))
      at hTransport
    rw [hCentre, hk] at hTransport
    exact hTransport

/-- C13 with the source's pairwise-DISTINCT-index hypothesis.
Self-intersections follow from original-source coseriality of each
nonempty invariant exact relation, so empty and singleton families
carry no extra ball-existence premise. -/
theorem exact_ball_helly_of_pairwise_CCO
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {root : ι} {I : Type (max u v)} [Finite I]
    (sort : I → ι)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I, p ≠ q →
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty) :
    ∃ x : X root, ∀ t : I, evaluate S (D t).words x (centres t) := by
  apply exact_ball_helly_of_CCO S H cco sort D centres
  intro p q
  by_cases hpq : p = q
  · subst q
    obtain ⟨x, hx⟩ := ball_nonempty_of_homogeneous S H
      (evaluate S (D p).words) (D p).nonempty
      (presentation_invariant_of_homogeneous S H (D p).words) (centres p)
    exact ⟨x, hx, hx⟩
  · exact hPair p q hpq

/-- The actual source instance of C13 consumed by exact convolution,
word/menu Helly, saturation and joint point extension. -/
theorem heterogeneousExactBallHelly_of_CCO
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S) :
    HeterogeneousExactBallHelly S := by
  intro I _ root sort D centres hPair
  obtain ⟨x, hx⟩ := exact_ball_helly_of_CCO S H cco
    (fun t : ULift.{max u v} I => sort t.down)
    (fun t => D t.down)
    (fun t => centres t.down)
    (fun p q => hPair p.down q.down)
  exact ⟨x, fun t => hx ⟨t⟩⟩

end CCO.RawExact
