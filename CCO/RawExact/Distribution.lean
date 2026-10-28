import CCO.RawExact.MeetHelly
import CCO.RawExact.ConvolutionFromHelly

/-!
# B002 C10: nonempty exact-meet distributivity from C09

Finite exact restriction meets remain exact ONLY when the resulting
intersection is witnessed nonempty. Once C13 has given actual exact
convolution (C09), distributivity follows by flattening FINITE WORD LISTS,
not by invoking a false general relational distributive law.
Here heterogeneous exact-ball Helly remains an explicit source provider.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Finite nonempty-result exact meet with every duplicated restriction
retained. The proof witnesses a real pair, not a fake empty profile. -/
def exactFamilyMeet {i j : ι}
    (D : List (NonemptyExact S i j))
    (h : TRel.Nonempty (fun x y =>
      ∀ d, d ∈ D → evaluate S d.words x y)) :
    NonemptyExact S i j := by
  refine ⟨flattenExact S D, ?_⟩
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, (flattenExact_evaluate S D x y).mpr hxy⟩

theorem exactFamilyMeet_relation {i j : ι}
    (D : List (NonemptyExact S i j))
    (h : TRel.Nonempty (fun x y =>
      ∀ d, d ∈ D → evaluate S d.words x y)) :
    evaluate S (exactFamilyMeet S D h).words =
      (fun x y => ∀ d, d ∈ D → evaluate S d.words x y) := by
  funext x y
  exact propext (flattenExact_evaluate S D x y)

/-- Relational word-pair restrictions commute with flattening the
RIGHT finite list: purely syntactic, including empty factors. -/
theorem pairWords_flatten_right {i j k : ι}
    (P : Presentation S i j)
    (D : List (NonemptyExact S j k))
    (x : X i) (z : X k) :
    evaluate S (pairWords S P (flattenExact S D)) x z ↔
      ∀ d, d ∈ D → evaluate S (pairWords S P d.words) x z := by
  constructor
  · intro h d hd w hw
    obtain ⟨p, hp, hwMap⟩ := List.mem_flatMap.mp hw
    obtain ⟨q, hq, hwEq⟩ := List.mem_map.mp hwMap
    apply h w
    exact List.mem_flatMap.mpr
      ⟨p, hp, List.mem_map.mpr
        ⟨q, List.mem_flatMap.mpr ⟨d, hd, hq⟩, hwEq⟩⟩
  · intro h w hw
    obtain ⟨p, hp, hwMap⟩ := List.mem_flatMap.mp hw
    obtain ⟨q, hq, hwEq⟩ := List.mem_map.mp hwMap
    obtain ⟨d, hd, hdq⟩ := List.mem_flatMap.mp hq
    exact h d hd w (List.mem_flatMap.mpr
      ⟨p, hp, List.mem_map.mpr ⟨q, hdq, hwEq⟩⟩)

/-- The analogous statement for the LEFT word list. The order of
pair concatenation is preserved, not silently commuted. -/
theorem pairWords_flatten_left {i j k : ι}
    (D : List (NonemptyExact S i j))
    (Q : Presentation S j k)
    (x : X i) (z : X k) :
    evaluate S (pairWords S (flattenExact S D) Q) x z ↔
      ∀ d, d ∈ D → evaluate S (pairWords S d.words Q) x z := by
  constructor
  · intro h d hd w hw
    obtain ⟨p, hp, hwMap⟩ := List.mem_flatMap.mp hw
    obtain ⟨q, hq, hwEq⟩ := List.mem_map.mp hwMap
    apply h w
    exact List.mem_flatMap.mpr
      ⟨p, List.mem_flatMap.mpr ⟨d, hd, hp⟩,
        List.mem_map.mpr ⟨q, hq, hwEq⟩⟩
  · intro h w hw
    obtain ⟨p, hp, hwMap⟩ := List.mem_flatMap.mp hw
    obtain ⟨q, hq, hwEq⟩ := List.mem_map.mp hwMap
    obtain ⟨d, hd, hdp⟩ := List.mem_flatMap.mp hp
    exact h d hd w (List.mem_flatMap.mpr
      ⟨p, hdp, List.mem_map.mpr ⟨q, hq, hwEq⟩⟩)

/-- C10 right-argument distribution: R;(meet D_i) is the meet of
R;D_i, provided R and the RESULTING actual meet are nonempty exact.
The empty family is included and evaluates to typed Top. -/
theorem comp_exact_meet_right
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (hHelly : HeterogeneousExactBallHelly S)
    {i j k : ι} (R : NonemptyExact S i j)
    (D : List (NonemptyExact S j k))
    (hMeet : TRel.Nonempty (fun y z =>
      ∀ d, d ∈ D → evaluate S d.words y z)) :
    TRel.comp (evaluate S R.words)
      (fun y z => ∀ d, d ∈ D → evaluate S d.words y z) =
    (fun x z => ∀ d, d ∈ D →
      TRel.comp (evaluate S R.words) (evaluate S d.words) x z) := by
  let M := exactFamilyMeet S D hMeet
  have hM := exactFamilyMeet_relation S D hMeet
  have hConv := convolution_of_exact_ball_helly S H hHelly R M
  calc
    TRel.comp (evaluate S R.words)
        (fun y z => ∀ d, d ∈ D → evaluate S d.words y z) =
      TRel.comp (evaluate S R.words) (evaluate S M.words) := by rw [hM]
    _ = evaluate S (pairWords S R.words M.words) := hConv
    _ = (fun x z => ∀ d, d ∈ D →
        evaluate S (pairWords S R.words d.words) x z) := by
      funext x z
      exact propext (pairWords_flatten_right S R.words D x z)
    _ = (fun x z => ∀ d, d ∈ D →
        TRel.comp (evaluate S R.words) (evaluate S d.words) x z) := by
      funext x z
      apply propext
      constructor
      · intro h d hd
        rw [convolution_of_exact_ball_helly S H hHelly R d]
        exact h d hd
      · intro h d hd
        rw [← convolution_of_exact_ball_helly S H hHelly R d]
        exact h d hd

/-- C10 left-argument distribution, with the same indispensable
NONEMPTY meet-result premise. No symmetry or quotient SAP is needed. -/
theorem comp_exact_meet_left
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (hHelly : HeterogeneousExactBallHelly S)
    {i j k : ι}
    (D : List (NonemptyExact S i j))
    (hMeet : TRel.Nonempty (fun x y =>
      ∀ d, d ∈ D → evaluate S d.words x y))
    (R : NonemptyExact S j k) :
    TRel.comp
      (fun x y => ∀ d, d ∈ D → evaluate S d.words x y)
      (evaluate S R.words) =
    (fun x z => ∀ d, d ∈ D →
      TRel.comp (evaluate S d.words) (evaluate S R.words) x z) := by
  let M := exactFamilyMeet S D hMeet
  have hM := exactFamilyMeet_relation S D hMeet
  have hConv := convolution_of_exact_ball_helly S H hHelly M R
  calc
    TRel.comp
        (fun x y => ∀ d, d ∈ D → evaluate S d.words x y)
        (evaluate S R.words) =
      TRel.comp (evaluate S M.words) (evaluate S R.words) := by rw [hM]
    _ = evaluate S (pairWords S M.words R.words) := hConv
    _ = (fun x z => ∀ d, d ∈ D →
        evaluate S (pairWords S d.words R.words) x z) := by
      funext x z
      exact propext (pairWords_flatten_left S D R.words x z)
    _ = (fun x z => ∀ d, d ∈ D →
        TRel.comp (evaluate S d.words) (evaluate S R.words) x z) := by
      funext x z
      apply propext
      constructor
      · intro h d hd
        rw [convolution_of_exact_ball_helly S H hHelly d R]
        exact h d hd
      · intro h d hd
        rw [← convolution_of_exact_ball_helly S H hHelly d R]
        exact h d hd

end CCO.RawExact
