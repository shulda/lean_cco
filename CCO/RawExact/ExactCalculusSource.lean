import CCO.RawExact.ExactBallHellySource
import CCO.RawExact.WordHellyFromBalls
import CCO.RawExact.SaturationDistribution

/-!
# Source instances of the full RAW exact calculus

The anchored-fan C13 theorem now discharges the previously explicit
Helly provider in word/menu Helly, exact convolution and nonempty-result
meet distribution. These exports use only the original homogeneous
source and semantic CCO. The nonempty meet-result premises remain visible.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
variable (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

include H cco

/-- C07 for arbitrary finite equality-inclusive RAW word profiles. -/
theorem wordProfileHelly_of_CCO : WordProfileHelly S :=
  wordProfileHelly_of_exactBallHelly S H
    (heterogeneousExactBallHelly_of_CCO S H cco)

/-- The source's C07 quantifiers: nonempty individual profiles and
pairwise compatibility only for distinct words. -/
theorem wordProfileHelly_pairwise_of_CCO
    {i j : ι} (P : Presentation S i j)
    (hNonempty : ∀ word, word ∈ P → TRel.Nonempty (RawWord.relation S word))
    (hPair : ∀ p, p ∈ P → ∀ q, q ∈ P → p ≠ q →
      TRel.Nonempty (fun x y =>
        RawWord.relation S p x y ∧ RawWord.relation S q x y)) :
    TRel.Nonempty (evaluate S P) := by
  apply wordProfileHelly_of_CCO S H cco P hNonempty
  intro p hp q hq
  by_cases hpq : p = q
  · subst q
    obtain ⟨x, y, hxy⟩ := hNonempty p hp
    exact ⟨x, y, hxy, hxy⟩
  · exact hPair p hp q hq hpq

/-- C08 for arbitrary finite nonempty exact menus, including the
empty family and genuine same-sort equality profiles. -/
theorem exactMenuHelly_of_CCO
    {i j : ι} (D : List (NonemptyExact S i j))
    (hPair : ∀ d, d ∈ D → ∀ e, e ∈ D → d ≠ e →
      TRel.Nonempty (fun x y =>
        evaluate S d.words x y ∧ evaluate S e.words x y)) :
    TRel.Nonempty (fun x y => ∀ d, d ∈ D → evaluate S d.words x y) :=
  exactMenuHelly_of_exactBallHelly S H
    (heterogeneousExactBallHelly_of_CCO S H cco) D hPair

/-- C09: the actual represented composite is exactly the finite
pair-word presentation. Both empty restriction-list cases are included. -/
theorem convolution_of_CCO
    {i j k : ι} (D : NonemptyExact S i j) (F : NonemptyExact S j k) :
    TRel.comp (evaluate S D.words) (evaluate S F.words) =
      evaluate S (pairWords S D.words F.words) :=
  convolution_of_exact_ball_helly S H
    (heterogeneousExactBallHelly_of_CCO S H cco) D F

/-- C10 right-argument distribution with its indispensable
nonempty resulting meet premise. -/
theorem comp_exact_meet_right_of_CCO
    {i j k : ι} (R : NonemptyExact S i j)
    (D : List (NonemptyExact S j k))
    (hMeet : TRel.Nonempty (fun y z =>
      ∀ d, d ∈ D → evaluate S d.words y z)) :
    TRel.comp (evaluate S R.words)
      (fun y z => ∀ d, d ∈ D → evaluate S d.words y z) =
      (fun x z => ∀ d, d ∈ D →
        TRel.comp (evaluate S R.words) (evaluate S d.words) x z) :=
  comp_exact_meet_right S H
    (heterogeneousExactBallHelly_of_CCO S H cco) R D hMeet

/-- C10 left-argument distribution, with no assertion about
empty meet results or symmetry of mixed typed arrows. -/
theorem comp_exact_meet_left_of_CCO
    {i j k : ι} (D : List (NonemptyExact S i j))
    (hMeet : TRel.Nonempty (fun x y =>
      ∀ d, d ∈ D → evaluate S d.words x y))
    (R : NonemptyExact S j k) :
    TRel.comp (fun x y => ∀ d, d ∈ D → evaluate S d.words x y)
      (evaluate S R.words) =
      (fun x z => ∀ d, d ∈ D →
        TRel.comp (evaluate S d.words) (evaluate S R.words) x z) :=
  comp_exact_meet_left S H
    (heterogeneousExactBallHelly_of_CCO S H cco) D hMeet R

/-- The full source two-sided exact saturation law, including
empty index families and retaining nonemptiness of the actual meet. -/
theorem fullExact_saturation_meet_distribution_of_CCO
    {i j : ι} (E : NonemptyExact S i i) (K : NonemptyExact S j j)
    (D : List (NonemptyExact S i j))
    (hD : TRel.Nonempty
      (fun x y => ∀ d, d ∈ D → evaluate S d.words x y)) :
    saturate (evaluate S E.words)
        (fun x y => ∀ d, d ∈ D → evaluate S d.words x y)
        (evaluate S K.words) =
      (fun x z => ∀ d, d ∈ D →
        saturate (evaluate S E.words) (evaluate S d.words)
          (evaluate S K.words) x z) :=
  fullExact_saturation_meet_distribution S H
    (heterogeneousExactBallHelly_of_CCO S H cco) E K D hD

end CCO.RawExact
