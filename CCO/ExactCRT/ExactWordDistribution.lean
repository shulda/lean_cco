import CCO.RawExact.ExactCalculusSource

/-! Full RAW nonempty-result saturation distribution in the literal
finite word presentation used by quotient descent. Empty lists are Top. -/
universe u v w t
namespace CCO.ExactCRT
open RawExact
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)

/-- Every restriction of a nonempty exact relation is itself a nonempty
word profile. The existing witness is kept, including diagonal outputs. -/
def wordRestriction {i j : ι} (D : NonemptyExact S i j)
    (word : {w // w ∈ D.words}) : NonemptyExact S i j :=
  singletonExact S word.val (by
    obtain ⟨x, y, hxy⟩ := D.nonempty
    exact ⟨x, y, hxy word.val word.property⟩)

@[simp] theorem wordRestriction_relation {i j : ι} (D : NonemptyExact S i j)
    (word : {w // w ∈ D.words}) :
    evaluate S (wordRestriction S D word).words = RawWord.relation S word.val :=
  evaluate_single S word.val

include H cco in
theorem saturation_evaluate_words {i j : ι}
    (E : NonemptyExact S i i) (K : NonemptyExact S j j)
    (D : NonemptyExact S i j) :
    saturate (evaluate S E.words) (evaluate S D.words) (evaluate S K.words) =
      (fun x y => ∀ word, word ∈ D.words →
        saturate (evaluate S E.words) (RawWord.relation S word) (evaluate S K.words) x y) := by
  let L : List (NonemptyExact S i j) := D.words.attach.map (wordRestriction S D)
  have hForall : ∀ P : (X i → X j → Prop) → Prop,
      (∀ d, d ∈ L → P (evaluate S d.words)) ↔
        ∀ word, word ∈ D.words → P (RawWord.relation S word) := by
    intro P
    constructor
    · intro h word hw
      have hh := h (wordRestriction S D ⟨word, hw⟩)
        (List.mem_map.mpr ⟨⟨word, hw⟩, by simp, rfl⟩)
      simpa only [wordRestriction_relation] using hh
    · intro h d hd
      obtain ⟨word, _, rfl⟩ := List.mem_map.mp hd
      rw [wordRestriction_relation]
      exact h word.val word.property
  have hMeet : (fun x y => ∀ d, d ∈ L → evaluate S d.words x y) =
      evaluate S D.words := by
    funext x y
    exact propext (hForall (fun R => R x y))
  have hn : TRel.Nonempty (fun x y => ∀ d, d ∈ L → evaluate S d.words x y) := by
    rw [hMeet]
    exact D.nonempty
  have h := fullExact_saturation_meet_distribution_of_CCO S H cco E K L hn
  rw [hMeet] at h
  exact h.trans (by
    funext x y
    exact propext (hForall (fun R => saturate (evaluate S E.words) R (evaluate S K.words) x y)))

end CCO.ExactCRT
