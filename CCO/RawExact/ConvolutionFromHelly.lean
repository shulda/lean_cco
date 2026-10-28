import Mathlib.Data.Fintype.Sum
import CCO.RawExact.JointPoint
import CCO.RawExact.Convolution

/-!
# B002 C09: exact convolution from heterogeneous RAW ball Helly

This gives a shorter source-faithful alternative to the two Peirce/word-
Helly applications in N04: a single C13 heterogeneous exact-ball Helly
application to the word restrictions for the unknown middle point.
The source C13 claim DAG does NOT depend on C09, so this reordering is
not circular. C13 is an EXPLICIT premise until its anchored-fan proof
is formalized. The two empty-presentation cases are included.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

theorem evaluate_single {i j : ι} (word : RawWord S i j) :
    evaluate S [word] = RawWord.relation S word := by
  funext x y
  apply propext
  constructor
  · intro h
    exact h word (by simp)
  · intro h w hw
    have hEq : w = word := by simpa using hw
    subst w
    exact h

def singletonExact {i j : ι} (word : RawWord S i j)
    (hNonempty : TRel.Nonempty (RawWord.relation S word)) :
    NonemptyExact S i j := by
  refine ⟨[word], ?_⟩
  rw [evaluate_single S]
  exact hNonempty

/-- Conditional C09 equality from C13, for all finite word lists,
including empty presentations and words with identity outputs.
Original transitivity supplies same-side pairwise intersections;
right-hand word-pair restrictions supply the crossed intersections. -/
theorem convolution_of_exact_ball_helly
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (hHelly : HeterogeneousExactBallHelly S)
    {i j k : ι} (D : NonemptyExact S i j)
    (F : NonemptyExact S j k) :
    TRel.comp (evaluate S D.words) (evaluate S F.words) =
      evaluate S (pairWords S D.words F.words) := by
  funext x z
  apply propext
  constructor
  · exact comp_subset_pairWords S D.words F.words x z
  · intro hPairWords
    have hSerial : ∃ y : X j, evaluate S D.words x y :=
      (S.raw_serial_of_homogeneous H
        (evaluate S D.words) D.nonempty
        (presentation_invariant_of_homogeneous S H D.words)) x
    have hCoserial : ∃ y : X j, evaluate S F.words y z :=
      (S.raw_coserial_of_homogeneous H
        (evaluate S F.words) F.nonempty
        (presentation_invariant_of_homogeneous S H F.words)) z
    have hCross : ∀ (p : Fin D.words.length) (q : Fin F.words.length),
        ∃ y : X j,
          RawWord.relation S (D.words.get p) x y ∧
          RawWord.relation S (F.words.get q) y z := by
      intro p q
      have hMem : RawWord.append S (D.words.get p) (F.words.get q) ∈
          pairWords S D.words F.words := by
        change RawWord.append S (D.words.get p) (F.words.get q) ∈
          D.words.flatMap (fun w => F.words.map (RawWord.append S w))
        exact List.mem_flatMap.mpr
          ⟨D.words.get p, List.get_mem D.words p,
            List.mem_map.mpr
              ⟨F.words.get q, List.get_mem F.words q, rfl⟩⟩
      have hWalk := hPairWords _ hMem
      rw [RawWord.relation_append S] at hWalk
      exact hWalk
    let I : Type := Fin D.words.length ⊕ Fin F.words.length
    let centreSort : I → ι := fun t =>
      match t with
      | .inl _ => i
      | .inr _ => k
    let centre : (t : I) → X (centreSort t) := fun t =>
      match t with
      | .inl _ => x
      | .inr _ => z
    let profiles : (t : I) → NonemptyExact S j (centreSort t) := by
      intro t
      cases t with
      | inl p =>
          have hNonempty : TRel.Nonempty
              (RawWord.relation S (RawWord.reverse S (D.words.get p))) := by
            obtain ⟨a, b, hab⟩ := D.nonempty
            refine ⟨b, a, ?_⟩
            rw [RawWord.relation_reverse S]
            exact hab (D.words.get p) (List.get_mem D.words p)
          exact singletonExact S (RawWord.reverse S (D.words.get p)) hNonempty
      | inr q =>
          have hNonempty : TRel.Nonempty
              (RawWord.relation S (F.words.get q)) := by
            obtain ⟨a, b, hab⟩ := F.nonempty
            exact ⟨a, b, hab (F.words.get q) (List.get_mem F.words q)⟩
          exact singletonExact S (F.words.get q) hNonempty
    have hPairwiseBalls : ∀ p q : I,
        (ball (evaluate S (profiles p).words) (centre p) ∩
          ball (evaluate S (profiles q).words) (centre q)).Nonempty := by
      intro p q
      cases p with
      | inl a =>
          cases q with
          | inl b =>
              obtain ⟨y, hy⟩ := hSerial
              refine ⟨y, ?_, ?_⟩
              · change evaluate S [RawWord.reverse S (D.words.get a)] y x
                rw [evaluate_single S, RawWord.relation_reverse S]
                exact hy (D.words.get a) (List.get_mem D.words a)
              · change evaluate S [RawWord.reverse S (D.words.get b)] y x
                rw [evaluate_single S, RawWord.relation_reverse S]
                exact hy (D.words.get b) (List.get_mem D.words b)
          | inr b =>
              obtain ⟨y, hLeft, hRight⟩ := hCross a b
              refine ⟨y, ?_, ?_⟩
              · change evaluate S [RawWord.reverse S (D.words.get a)] y x
                rw [evaluate_single S, RawWord.relation_reverse S]
                exact hLeft
              · change evaluate S [F.words.get b] y z
                rw [evaluate_single S]
                exact hRight
      | inr a =>
          cases q with
          | inl b =>
              obtain ⟨y, hLeft, hRight⟩ := hCross b a
              refine ⟨y, ?_, ?_⟩
              · change evaluate S [F.words.get a] y z
                rw [evaluate_single S]
                exact hRight
              · change evaluate S [RawWord.reverse S (D.words.get b)] y x
                rw [evaluate_single S, RawWord.relation_reverse S]
                exact hLeft
          | inr b =>
              obtain ⟨y, hy⟩ := hCoserial
              refine ⟨y, ?_, ?_⟩
              · change evaluate S [F.words.get a] y z
                rw [evaluate_single S]
                exact hy (F.words.get a) (List.get_mem F.words a)
              · change evaluate S [F.words.get b] y z
                rw [evaluate_single S]
                exact hy (F.words.get b) (List.get_mem F.words b)
    obtain ⟨y, hy⟩ := hHelly centreSort profiles centre hPairwiseBalls
    refine ⟨y, ?_, ?_⟩
    · intro word hw
      obtain ⟨p, hp⟩ := List.get_of_mem hw
      have h := hy (.inl p)
      change evaluate S [RawWord.reverse S (D.words.get p)] y x at h
      rw [evaluate_single S, RawWord.relation_reverse S] at h
      rw [← hp]
      exact h
    · intro word hw
      obtain ⟨q, hq⟩ := List.get_of_mem hw
      have h := hy (.inr q)
      change evaluate S [F.words.get q] y z at h
      rw [evaluate_single S] at h
      rw [← hq]
      exact h

/-- Nonempty exactness of convolution follows even for empty restrictions;
only the equality of its represented product with the pair-word
presentation requires the separate C13 provider. -/
def convolutionExact
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) {i j k : ι}
    (D : NonemptyExact S i j) (F : NonemptyExact S j k) :
    NonemptyExact S i k :=
  ⟨pairWords S D.words F.words,
    pairWords_nonempty_of_homogeneous S H D F⟩

theorem convolutionExact_represents
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (hHelly : HeterogeneousExactBallHelly S)
    {i j k : ι} (D : NonemptyExact S i j)
    (F : NonemptyExact S j k) :
    evaluate S (convolutionExact S H D F).words =
      TRel.comp (evaluate S D.words) (evaluate S F.words) :=
  (convolution_of_exact_ball_helly S H hHelly D F).symm

end CCO.RawExact
