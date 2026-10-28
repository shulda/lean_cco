import CCO.RawExact.Saturation
import CCO.RawWords

/-!
# The exact place where typed kernel intertwining is used

A quotient word retains a kernel at EVERY intermediate sort. The recursion
below models this literally. Only a TI certificate for its actual atomic
letters permits deleting the intermediate kernels. Empty words retain the
endpoint kernel; genuine identity letters introduce no diversity atom.
-/

universe u v w

namespace CCO.ExactCRT

open CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) (E : ∀ i, TRel X i i)

def kernelWord : {i j : ι} → RawWord S i j → TRel X i j
  | _, _, .nil i => E i
  | _, _, .identity tail => kernelWord tail
  | _, _, .atom (i := i) (j := j) a tail =>
      TRel.comp (saturate (E i) (S.atomRel a) (E j)) (kernelWord tail)

def WordTI : {i j : ι} → RawWord S i j → Prop
  | _, _, .nil _ => True
  | _, _, .identity tail => WordTI tail
  | _, _, .atom (i := i) (j := j) a tail =>
      TRel.comp (E i) (S.atomRel a) = TRel.comp (S.atomRel a) (E j) ∧ WordTI tail

/-- TI for just the leading actual letter removes its intermediate kernel.
The remaining relation need not commute with either endpoint kernel.
-/
theorem saturated_letter_comp {i j k : ι}
    (a : S.Atom i j) (R : TRel X j k)
    (hEi : RawSymmetric.EquivRel (E i))
    (hEj : RawSymmetric.EquivRel (E j))
    (hTI : TRel.comp (E i) (S.atomRel a) =
      TRel.comp (S.atomRel a) (E j)) :
    TRel.comp (saturate (E i) (S.atomRel a) (E j)) (saturate (E j) R (E k)) =
      saturate (E i) (TRel.comp (S.atomRel a) R) (E k) := by
  have hs : saturate (E i) (S.atomRel a) (E j) =
      TRel.comp (E i) (S.atomRel a) := by
    unfold saturate
    rw [hTI, right_request_saturated (S.atomRel a) (E j) hEj, ← hTI]
  let A := saturate (E i) (S.atomRel a) (E j)
  calc
    TRel.comp A (saturate (E j) R (E k)) =
        TRel.comp (TRel.comp (TRel.comp A (E j)) R) (E k) := by
      change TRel.comp A (TRel.comp (TRel.comp (E j) R) (E k)) = _
      rw [← TRel.comp_assoc A (TRel.comp (E j) R) (E k),
        ← TRel.comp_assoc A (E j) R]
    _ = TRel.comp (TRel.comp A R) (E k) := by
      rw [(saturate_idempotent (E i) (S.atomRel a) (E j) hEi hEj).2]
    _ = TRel.comp (TRel.comp (TRel.comp (E i) (S.atomRel a)) R) (E k) := by
      dsimp only [A]
      rw [hs]
    _ = saturate (E i) (TRel.comp (S.atomRel a) R) (E k) := by
      rw [TRel.comp_assoc (E i) (S.atomRel a) R]
      rfl

theorem kernelWord_eq_saturate (hE : ∀ i, RawSymmetric.EquivRel (E i))
    {i j : ι} (word : RawWord S i j) (hTI : WordTI S E word) :
    kernelWord S E word = saturate (E i) (RawWord.relation S word) (E j) := by
  induction word with
  | nil i =>
      change E i = TRel.comp (TRel.comp (E i) (TRel.ident X i)) (E i)
      rw [TRel.comp_ident, typed_equiv_comp_self (E i) (hE i)]
  | identity tail ih => exact ih hTI
  | @atom i j k a tail ih =>
      change TRel.comp (saturate (E i) (S.atomRel a) (E j))
        (kernelWord S E tail) =
        saturate (E i) (TRel.comp (S.atomRel a) (RawWord.relation S tail)) (E k)
      rw [ih hTI.2]
      exact saturated_letter_comp S E a (RawWord.relation S tail) (hE i) (hE j) hTI.1

theorem wordTI_of_all_atoms
    (hTI : ∀ i j (a : S.Atom i j),
      TRel.comp (E i) (S.atomRel a) = TRel.comp (S.atomRel a) (E j))
    {i j : ι} (word : RawWord S i j) : WordTI S E word := by
  induction word with
  | nil _ => trivial
  | identity _ ih => exact ih
  | atom a _ ih => exact ⟨hTI _ _ a, ih⟩

/-- In a genuine one-sort source, commutation with each original atom supplies
the typed certificate. This does not assert mixed-sort commutation.
-/
theorem single_sort_wordTI {Y : Unit → Type v}
    (T : AtomicSource.{0,v,w} Unit Y) (J : ∀ i, TRel Y i i)
    (hcomm : ∀ a : T.Atom () (),
      TRel.comp (J ()) (T.atomRel a) = TRel.comp (T.atomRel a) (J ()))
    {i j : Unit} (word : RawWord T i j) : WordTI T J word := by
  apply wordTI_of_all_atoms T J
  intro i j a
  cases i
  cases j
  exact hcomm a

end CCO.ExactCRT
