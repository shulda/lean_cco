import CCO.RawExact.FanAllCycles
import CCO.RawExact.ConvolutionFromHelly

/-!
# Arbitrary-length RAW word theta diagrams

Put one singleton word menu at a fixed actual target point for each
original word profile. Original-sort transitivity moves every pairwise
profile witness to that target, without choosing a simultaneous witness.
The private fan then is a genuine two-endpoint theta construction: each
word occurrence has its own private interiors and duplicate direct edges
are merged by the existing source-colour uniqueness proof.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {I : Type (max u v)} [Finite I] {i j : ι}

/-- Keep every indexed word profile as its own nonempty exact menu. -/
def wordThetaMenus (words : I → RawWord S i j)
    (hNonempty : ∀ t, TRel.Nonempty (RawWord.relation S (words t))) :
    ∀ _ : I, NonemptyExact S i j :=
  fun t => singletonExact S (words t) (hNonempty t)

/-- The one occurrence in the t-th singleton word menu. -/
def wordThetaOccurrence (words : I → RawWord S i j)
    (hNonempty : ∀ t, TRel.Nonempty (RawWord.relation S (words t)))
    (t : I) : WordOccurrence S (wordThetaMenus S words hNonempty) :=
  ⟨t, ⟨0, by simp [wordThetaMenus, singletonExact]⟩⟩

omit [Finite I] in
theorem wordThetaOccurrence_word (words : I → RawWord S i j)
    (hNonempty : ∀ t, TRel.Nonempty (RawWord.relation S (words t)))
    (t : I) :
    occurrenceWord S (wordThetaMenus S words hNonempty)
      (wordThetaOccurrence S words hNonempty t) = words t := rfl

/-- At positive diversity length, this word's far endpoint is
literally the one old target centre. Identity letters create no edges. -/
theorem wordThetaOccurrence_finish (words : I → RawWord S i j)
    (hNonempty : ∀ t, TRel.Nonempty (RawWord.relation S (words t)))
    (centre : X j) (t : I) (hPositive : 0 < diversityLength S (words t)) :
    privateFanAtWordPosition S (wordThetaMenus S words hNonempty)
      (fun _ => centre) (wordThetaOccurrence S words hNonempty t)
      (pathFinish S (occurrenceWord S (wordThetaMenus S words hNonempty)
        (wordThetaOccurrence S words hNonempty t))) =
      privateFanCentre S (wordThetaMenus S words hNonempty) (fun _ => centre)
        (toDistinctCentre (fun _ : I => j) (fun _ => centre) t) := by
  apply privateFanAt_finish S _ _ _
  simpa only [wordThetaOccurrence_word] using hPositive

omit [Finite I] in
/-- Pairwise profile compatibility gives genuine pairwise balls at
ONE arbitrary original target point, by original transitivity alone. -/
theorem wordTheta_pairwise_balls
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (words : I → RawWord S i j)
    (hNonempty : ∀ t, TRel.Nonempty (RawWord.relation S (words t)))
    (centre : X j)
    (hPair : ∀ p q : I, p ≠ q → TRel.Nonempty (fun x y =>
      RawWord.relation S (words p) x y ∧ RawWord.relation S (words q) x y)) :
    ∀ p q : I,
      (ball (evaluate S (wordThetaMenus S words hNonempty p).words) centre ∩
        ball (evaluate S (wordThetaMenus S words hNonempty q).words) centre).Nonempty := by
  intro p q
  have hCommon : TRel.Nonempty (fun x y =>
      RawWord.relation S (words p) x y ∧ RawWord.relation S (words q) x y) := by
    by_cases hpq : p = q
    · subst q
      obtain ⟨x, y, hxy⟩ := hNonempty p
      exact ⟨x, y, hxy, hxy⟩
    · exact hPair p q hpq
  obtain ⟨x, y, hp, hq⟩ := hCommon
  obtain ⟨g, hg⟩ := S.original_sort_transitive_of_homogeneous H j y centre
  refine ⟨g • x, ?_, ?_⟩
  · change evaluate S [words p] (g • x) centre
    rw [evaluate_single S]
    simpa only [hg] using word_invariant_of_homogeneous S H (words p) g x y hp
  · change evaluate S [words q] (g • x) centre
    rw [evaluate_single S]
    simpa only [hg] using word_invariant_of_homogeneous S H (words q) g x y hq

/-- C06: every actual simple cycle in the arbitrary-length,
equality-inclusive word theta diagram has an original-source homomorphism.
This supplies cycle witnesses before any CCO or Helly application. -/
theorem wordTheta_cycleHom_of_pairwise
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (words : I → RawWord S i j)
    (hNonempty : ∀ t, TRel.Nonempty (RawWord.relation S (words t)))
    (centre : X j)
    (hPair : ∀ p q : I, p ≠ q → TRel.Nonempty (fun x y =>
      RawWord.relation S (words p) x y ∧ RawWord.relation S (words q) x y)) :
    ∀ C : SimpleCycle (privateFanFullDiagram S H
        (wordThetaMenus S words hNonempty) (fun _ => centre)),
      CycleHom C :=
  privateFanFull_cycleHom_of_pairwise S H _ _
    (wordTheta_pairwise_balls S H words hNonempty centre hPair)

end CCO.RawExact
