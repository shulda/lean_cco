import CCO.StrongExact.HellyConvolution

/-!
# C08 finite STRONG exact-meet distribution, conditional on C07

Once the source's positive-word theta Helly theorem is discharged,
the completely proved twice-Helly convolution formula immediately
distributes an exact nonempty multiplier over any finite exact meet
whose evaluated result is nonempty. The empty family is explicitly
included and means the ORIGINAL typed diversity Top.

This module establishes both directions algebraically under the
EXPLICIT `WordHelly S` premise. It does not assert that premise or
introduce an unproved provider into the source closure.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u, v, w} ι X)
variable {i j k : ι}

/-- Flat positive-word presentations for a finite collection of
exact domains; empty nested lists impose no restriction. -/
def flattenedPresentations
    (lists : List (List (PositiveWord S i j))) :
    List (PositiveWord S i j) :=
  lists.flatMap (fun xs => xs)

/-- C08 left distribution over arbitrary finite nonempty-evaluation
exact meets. Individual exact factors may be Top (empty word lists). -/
theorem product_distrib_right_exact_of_wordHelly
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (hHelly : WordHelly S)
    (left : List (PositiveWord S i j))
    (rights : List (List (PositiveWord S j k)))
    (hLeft : (present S left).Nonempty)
    (hMeet : (present S (flattenedPresentations S rights)).Nonempty) :
    S.product (present S left)
      (present S (flattenedPresentations S rights)) =
        {c | ∀ right ∈ rights,
          c ∈ S.product (present S left) (present S right)} := by
  have hEach (right : List (PositiveWord S j k)) (hr : right ∈ rights) :
      (present S right).Nonempty := by
    obtain ⟨b, hb⟩ := hMeet
    refine ⟨b, ?_⟩
    intro v hv
    exact hb v (List.mem_flatMap.mpr ⟨right, hr, hv⟩)
  ext c
  rw [exact_convolution_of_wordHelly S H sap hHelly
    left (flattenedPresentations S rights) hLeft hMeet]
  change (∀ u ∈ left, ∀ v ∈ flattenedPresentations S rights,
      c ∈ S.product (PositiveWord.profile S u)
        (PositiveWord.profile S v)) ↔
    (∀ right ∈ rights,
      c ∈ S.product (present S left) (present S right))
  constructor
  · intro hc right hr
    rw [exact_convolution_of_wordHelly S H sap hHelly
      left right hLeft (hEach right hr)]
    intro u hu v hv
    exact hc u hu v (List.mem_flatMap.mpr ⟨right, hr, hv⟩)
  · intro hc u hu v hv
    obtain ⟨right, hr, hvr⟩ := List.mem_flatMap.mp hv
    have hProd := hc right hr
    rw [exact_convolution_of_wordHelly S H sap hHelly
      left right hLeft (hEach right hr)] at hProd
    exact hProd u hu v hvr

/-- Symmetric right-factor distribution under the same actual
source hypotheses; repeated sorts and empty lists are preserved. -/
theorem product_distrib_left_exact_of_wordHelly
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (hHelly : WordHelly S)
    (lefts : List (List (PositiveWord S i j)))
    (right : List (PositiveWord S j k))
    (hMeet : (present S (flattenedPresentations S lefts)).Nonempty)
    (hRight : (present S right).Nonempty) :
    S.product (present S (flattenedPresentations S lefts))
      (present S right) =
        {c | ∀ left ∈ lefts,
          c ∈ S.product (present S left) (present S right)} := by
  have hEach (left : List (PositiveWord S i j)) (hl : left ∈ lefts) :
      (present S left).Nonempty := by
    obtain ⟨a, ha⟩ := hMeet
    refine ⟨a, ?_⟩
    intro u hu
    exact ha u (List.mem_flatMap.mpr ⟨left, hl, hu⟩)
  ext c
  rw [exact_convolution_of_wordHelly S H sap hHelly
    (flattenedPresentations S lefts) right hMeet hRight]
  change (∀ u ∈ flattenedPresentations S lefts, ∀ v ∈ right,
      c ∈ S.product (PositiveWord.profile S u)
        (PositiveWord.profile S v)) ↔
    (∀ left ∈ lefts,
      c ∈ S.product (present S left) (present S right))
  constructor
  · intro hc left hl
    rw [exact_convolution_of_wordHelly S H sap hHelly
      left right (hEach left hl) hRight]
    intro u hu v hv
    exact hc u (List.mem_flatMap.mpr ⟨left, hl, hu⟩) v hv
  · intro hc u hu v hv
    obtain ⟨left, hl, hul⟩ := List.mem_flatMap.mp hu
    have hProd := hc left hl
    rw [exact_convolution_of_wordHelly S H sap hHelly
      left right (hEach left hl) hRight] at hProd
    exact hProd u hul v hv

end CCO.StrongExact
