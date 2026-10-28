import CCO.RawWords

/-!
# RAW exact presentations: elementary closure

A presentation is a finite list of genuine typed RAW words. Its evaluation
is the equality-inclusive intersection of their actual endpoint relations.
The empty list means Top, not the empty relation. These elementary facts do
not assume RAW word Helly, CCO, SAP or exact convolution.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X)

/-- The syntactic words of an actual RAW exact presentation. -/
abbrev Presentation (i j : ι) := List (RawWord S i j)

/-- The full represented intersection, with logical identity retained. -/
def evaluate {i j : ι} (P : Presentation S i j) : TRel X i j :=
  fun x y => ∀ word, word ∈ P → RawWord.relation S word x y

theorem evaluate_nil {i j : ι} :
    evaluate S ([] : Presentation S i j) = TRel.top X i j := by
  funext x y
  apply propext
  simp [evaluate, TRel.top]

theorem evaluate_append {i j : ι} (P Q : Presentation S i j) :
    evaluate S (P ++ Q) =
      (fun x y => evaluate S P x y ∧ evaluate S Q x y) := by
  funext x y
  apply propext
  constructor
  · intro h
    constructor
    · intro word hw
      exact h word (List.mem_append.mpr (Or.inl hw))
    · intro word hw
      exact h word (List.mem_append.mpr (Or.inr hw))
  · rintro ⟨hP, hQ⟩ word hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hP word hw
    · exact hQ word hw

/-- Reverse all words; it reverses their endpoint sorts too. -/
def reversePresentation {i j : ι} (P : Presentation S i j) :
    Presentation S j i :=
  P.map (RawWord.reverse S)

theorem evaluate_reverse {i j : ι} (P : Presentation S i j) :
    evaluate S (reversePresentation S P) =
      TRel.converse (evaluate S P) := by
  funext y x
  apply propext
  constructor
  · intro h word hw
    have hmem : RawWord.reverse S word ∈ reversePresentation S P :=
      List.mem_map.mpr ⟨word, hw, rfl⟩
    have hword := h (RawWord.reverse S word) hmem
    rw [RawWord.relation_reverse S] at hword
    exact hword
  · intro h word hw
    obtain ⟨original, hmem, rfl⟩ := List.mem_map.mp hw
    rw [RawWord.relation_reverse S]
    exact h original hmem

/-- Semantic exactness includes a witnessed real pair. The underlying
intersection may include logical identity even for a positive word. -/
structure NonemptyExact (i j : ι) where
  words : Presentation S i j
  nonempty : TRel.Nonempty (evaluate S words)

namespace NonemptyExact

/-- Empty restrictions give inhabited typed Top, also for cross sorts. -/
def top (i j : ι) : NonemptyExact S i j := by
  refine ⟨[], ?_⟩
  obtain ⟨x⟩ := S.nonemptySort i
  obtain ⟨y⟩ := S.nonemptySort j
  exact ⟨x, y, by simp [evaluate]⟩

/-- Converse closure is purely syntactic and needs no CCO premise. -/
def converse {i j : ι} (D : NonemptyExact S i j) :
    NonemptyExact S j i := by
  refine ⟨reversePresentation S D.words, ?_⟩
  obtain ⟨x, y, h⟩ := D.nonempty
  refine ⟨y, x, ?_⟩
  rw [evaluate_reverse S]
  exact h

/-- Exact intersections remain exact whenever the result, not merely
the factors, is nonempty. -/
def meet {i j : ι} (D F : NonemptyExact S i j)
    (h : TRel.Nonempty
      (fun x y => evaluate S D.words x y ∧ evaluate S F.words x y)) :
    NonemptyExact S i j := by
  refine ⟨D.words ++ F.words, ?_⟩
  rw [evaluate_append S]
  exact h

theorem meet_relation {i j : ι} (D F : NonemptyExact S i j)
    (h : TRel.Nonempty
      (fun x y => evaluate S D.words x y ∧ evaluate S F.words x y)) :
    evaluate S (meet S D F h).words =
      (fun x y => evaluate S D.words x y ∧ evaluate S F.words x y) :=
  evaluate_append S D.words F.words

end NonemptyExact
end CCO.RawExact
