import CCO.RawExact.Balls

/-!
# B002 C09: first exact-convolution obligations

The cross-word presentation always contains the actual RAW composite.
Equality in the reverse direction is the substantive C07 word-Helly
consequence and is NOT assumed here. Nonemptiness is proved from
original source homogeneity (never from quotient transitivity).
-/

universe u v

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X)

/-- Pairwise concatenation of finite lists of correctly typed RAW words. -/
def pairWords {i j k : ι}
    (P : Presentation S i j) (Q : Presentation S j k) :
    Presentation S i k :=
  P.flatMap (fun w => Q.map (RawWord.append S w))

/-- Every actual composite satisfies every word-pair restriction. -/
theorem comp_subset_pairWords {i j k : ι}
    (P : Presentation S i j) (Q : Presentation S j k) :
    ∀ x z, TRel.comp (evaluate S P) (evaluate S Q) x z →
      evaluate S (pairWords S P Q) x z := by
  rintro x z ⟨y, hyP, hyQ⟩ w hw
  obtain ⟨p, hp, hmap⟩ := List.mem_flatMap.mp hw
  obtain ⟨q, hq, hword⟩ := List.mem_map.mp hmap
  subst w
  rw [RawWord.relation_append S]
  exact ⟨y, hyP p hp, hyQ q hq⟩

/-- An actual RAW word profile remains invariant under the original
colour-preserving action, including real equality letters and outputs. -/
theorem word_invariant_of_homogeneous
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G)
    {i j : ι} (w : RawWord S i j) :
    TRel.Invariant (G := G) (RawWord.relation S w) := by
  induction w with
  | nil t =>
      intro g x y hxy
      change x = y at hxy
      change g • x = g • y
      exact congrArg (fun t => g • t) hxy
  | identity tail ih =>
      exact ih
  | atom a tail ih =>
      intro g x z hcomp
      change ∃ y, S.atomRel a x y ∧ RawWord.relation S tail y z at hcomp
      obtain ⟨y, hxy, hyz⟩ := hcomp
      refine ⟨g • y, ?_, ih g y z hyz⟩
      change S.colour (g • x) (g • y) = some a
      exact (S.colourInvariant_of_homogeneous H g x y).trans hxy

theorem presentation_invariant_of_homogeneous
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G)
    {i j : ι} (P : Presentation S i j) :
    TRel.Invariant (G := G) (evaluate S P) := by
  intro g x y hxy word hw
  exact (word_invariant_of_homogeneous S H word)
    g x y (hxy word hw)

/-- A nonempty actual exact product gives a *nonempty word-pair menu*.
The converse inclusion, and hence C09's exact convolution theorem,
still needs the C07 source word-Helly construction. -/
theorem pairWords_nonempty_of_homogeneous
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G)
    {i j k : ι}
    (D : NonemptyExact S i j) (F : NonemptyExact S j k) :
    TRel.Nonempty (evaluate S (pairWords S D.words F.words)) := by
  obtain ⟨x, z, hcomp⟩ :=
    S.raw_nonempty_comp_of_homogeneous H
      (evaluate S D.words) (evaluate S F.words)
      D.nonempty F.nonempty
      (presentation_invariant_of_homogeneous S H F.words)
  exact ⟨x, z, comp_subset_pairWords S D.words F.words x z hcomp⟩

/-- Both genuine empty-presentation boundaries of C09 use only actual
original-sort transitivity and explicitly witnessed nonempty factors. -/
theorem empty_left_convolution
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G)
    {i j k : ι} (F : NonemptyExact S j k) :
    TRel.comp (evaluate S ([] : Presentation S i j))
      (evaluate S F.words) = TRel.top X i k := by
  rw [evaluate_nil S]
  exact S.raw_top_comp_of_homogeneous H
    (evaluate S F.words) F.nonempty
    (presentation_invariant_of_homogeneous S H F.words)

theorem empty_right_convolution
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G)
    {i j k : ι} (D : NonemptyExact S i j) :
    TRel.comp (evaluate S D.words)
      (evaluate S ([] : Presentation S j k)) = TRel.top X i k := by
  rw [evaluate_nil S]
  exact TRel.comp_top_invariant (G := G)
    (evaluate S D.words) D.nonempty
    (presentation_invariant_of_homogeneous S H D.words)
    (S.original_sort_transitive_of_homogeneous H i)

end CCO.RawExact
