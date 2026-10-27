import CCO.RawExact.SortTrace

/-!
# B002 C12: genuinely typed atomic edge labels along a RAW word

The original word is turned into a finite list of EXISTING typed
diversity atoms, with its equality letters omitted. These labels
are never logical identity atoms. Their number is exactly the
finite path edge count; typed start and target data are retained
in each dependent sigma instead of fabricated from a Boolean table.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- One actual typed diversity letter. -/
abbrev TypedAtomicStep :=
  Σ i : ι, Σ j : ι, S.Atom i j

/-- List the original word's diversity letters, preserving their
actual directed original-sort types and their consecutive order. -/
def rawAtomicSteps {i j : ι} : RawWord S i j → List (TypedAtomicStep S)
  | .nil _ => []
  | .identity tail => rawAtomicSteps tail
  | .atom a tail => ⟨i, _, a⟩ :: rawAtomicSteps tail

theorem rawAtomicSteps_nil (i : ι) :
    rawAtomicSteps S (.nil i) = [] := rfl

theorem rawAtomicSteps_identity {i j : ι} (tail : RawWord S i j) :
    rawAtomicSteps S (.identity tail) = rawAtomicSteps S tail := rfl

theorem rawAtomicSteps_length {i j : ι} (word : RawWord S i j) :
    (rawAtomicSteps S word).length = diversityLength S word := by
  induction word with
  | nil _ => rfl
  | identity tail ih => exact ih
  | atom a tail ih =>
      simp only [rawAtomicSteps, List.length_cons, diversityLength, ih]
      omega

/-- Word equality erasure keeps the exact diversity label sequence;
it is not an instruction to erase identity OUTPUTS of positive walks. -/
theorem rawAtomicSteps_eraseEquality {i j : ι}
    (word : RawWord S i j) :
    rawAtomicSteps S (RawWord.eraseEquality S word) =
      rawAtomicSteps S word := by
  induction word with
  | nil _ => rfl
  | identity tail ih => exact ih
  | atom a tail ih =>
      simp only [RawWord.eraseEquality, rawAtomicSteps, ih]

end CCO.RawExact
