import CCO.RawExact.Presentations
import CCO.RawExact.WordHellyBoundaries

/-!
# B002 C08: flattening finite full-exact menus

This separates the exact C07 word-Helly theorem from its finite-meet
corollary. The theorem here is conditional on the explicit C07 provider:
it is NOT a proof of general WordProfileHelly or the CCO theta theorem.
The empty family means inhabited RAW Top and equal menu entries need no
spurious pairwise hypothesis.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- The precise C07 property; the only outstanding combinatorial
provider in the finite exact-menu Helly reduction. -/
def WordProfileHelly : Prop :=
  ∀ {i j : ι} (P : Presentation S i j),
    (∀ word, word ∈ P →
      TRel.Nonempty (RawWord.relation S word)) →
    (∀ p, p ∈ P → ∀ q, q ∈ P →
      TRel.Nonempty (fun x y =>
        RawWord.relation S p x y ∧
          RawWord.relation S q x y)) →
    TRel.Nonempty (evaluate S P)

/-- Keep all occurrences, including repeated restrictions. -/
def flattenExact {i j : ι}
    (D : List (NonemptyExact S i j)) : Presentation S i j :=
  D.flatMap (fun d => d.words)

theorem flattenExact_evaluate {i j : ι}
    (D : List (NonemptyExact S i j))
    (x : X i) (y : X j) :
    evaluate S (flattenExact S D) x y ↔
      ∀ d, d ∈ D → evaluate S d.words x y := by
  constructor
  · intro h d hd w hw
    exact h w (List.mem_flatMap.mpr ⟨d, hd, hw⟩)
  · intro h w hw
    obtain ⟨d, hd, hword⟩ := List.mem_flatMap.mp hw
    exact h d hd w hword

theorem flattened_words_nonempty {i j : ι}
    (D : List (NonemptyExact S i j))
    (w : RawWord S i j) (hw : w ∈ flattenExact S D) :
    TRel.Nonempty (RawWord.relation S w) := by
  obtain ⟨d, _, hdw⟩ := List.mem_flatMap.mp hw
  obtain ⟨x, y, hd⟩ := d.nonempty
  exact ⟨x, y, hd w hdw⟩

theorem flattened_words_pairwise {i j : ι}
    (D : List (NonemptyExact S i j))
    (hPair : ∀ d, d ∈ D → ∀ e, e ∈ D →
      TRel.Nonempty (fun x y =>
        evaluate S d.words x y ∧ evaluate S e.words x y))
    (p q : RawWord S i j)
    (hp : p ∈ flattenExact S D)
    (hq : q ∈ flattenExact S D) :
    TRel.Nonempty (fun x y =>
      RawWord.relation S p x y ∧
        RawWord.relation S q x y) := by
  obtain ⟨d, hd, hdp⟩ := List.mem_flatMap.mp hp
  obtain ⟨e, he, heq⟩ := List.mem_flatMap.mp hq
  obtain ⟨x, y, hdx, hex⟩ := hPair d hd e he
  exact ⟨x, y, hdx p hdp, hex q heq⟩

/-- C08: finite family Helly follows from C07 by FLATTENING the actual
word presentations. Includes zero family, singleton, duplicate menus
and arbitrary typed original source pairs, including true diagonals. -/
theorem exact_menu_helly_of_word_helly
    (hWord : WordProfileHelly S)
    {i j : ι}
    (D : List (NonemptyExact S i j))
    (hPairDistinct : ∀ d, d ∈ D → ∀ e, e ∈ D → d ≠ e →
      TRel.Nonempty (fun x y =>
        evaluate S d.words x y ∧ evaluate S e.words x y)) :
    TRel.Nonempty (fun x y =>
      ∀ d, d ∈ D → evaluate S d.words x y) := by
  have hPair : ∀ d, d ∈ D → ∀ e, e ∈ D →
      TRel.Nonempty (fun x y =>
        evaluate S d.words x y ∧ evaluate S e.words x y) := by
    intro d hd e he
    by_cases hEq : d = e
    · subst e
      obtain ⟨x, y, hxy⟩ := d.nonempty
      exact ⟨x, y, hxy, hxy⟩
    · exact hPairDistinct d hd e he hEq
  obtain ⟨x, y, hFlat⟩ :=
    hWord (flattenExact S D)
      (fun w hw => flattened_words_nonempty S D w hw)
      (fun p hp q hq => flattened_words_pairwise S D hPair p q hp hq)
  refine ⟨x, y, ?_⟩
  exact (flattenExact_evaluate S D x y).mp hFlat

end CCO.RawExact
