import CCO.Atomic

/-!
# RAW words with true identity letters

A RAW word has an empty loop constructor, a genuine logical-equality
letter constructor, and a diversity constructor. Equality *letters* can
be erased without deleting diagonal *outputs* of a nonempty walk.
Every constructor keeps the sort indices correct, even for repeated sorts.
-/

universe u v w

namespace CCO

/-- A composable RAW word with genuine logical identity steps.
An identity step stays at the current root sort, while an atomic
diversity step follows an actual typed edge. -/
inductive RawWord {ι : Type u} {X : ι → Type v}
    (S : AtomicSource.{u,v,w} ι X) : ι → ι → Type (max u (max v w)) where
  | nil (i : ι) : RawWord S i i
  | identity {i j : ι} (tail : RawWord S i j) : RawWord S i j
  | atom {i j k : ι} (a : S.Atom i j) (tail : RawWord S j k) : RawWord S i k

namespace RawWord

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X)
variable {i j k : ι}

def relation {i j : ι} : RawWord S i j → TRel X i j
  | .nil i => TRel.ident X i
  | .identity tail => relation tail
  | .atom a tail => TRel.comp (S.atomRel a) (relation tail)

/-- Equality steps are deleted, rather than mistaken for diversity atoms. -/
def eraseEquality {i j : ι} : RawWord S i j → RawWord S i j
  | .nil i => .nil i
  | .identity tail => eraseEquality tail
  | .atom a tail => .atom a (eraseEquality tail)

theorem relation_eraseEquality (w : RawWord S i j) :
    relation S (eraseEquality S w) = relation S w := by
  induction w with
  | nil i => rfl
  | identity tail ih => exact ih
  | atom a tail ih =>
      change TRel.comp (S.atomRel a) (relation S (eraseEquality S tail)) =
        TRel.comp (S.atomRel a) (relation S tail)
      rw [ih]

def append {i j k : ι} : RawWord S i j → RawWord S j k → RawWord S i k
  | .nil _, v => v
  | .identity tail, v => .identity (append tail v)
  | .atom a tail, v => .atom a (append tail v)

theorem relation_append (u : RawWord S i j) (v : RawWord S j k) :
    relation S (append S u v) =
      TRel.comp (relation S u) (relation S v) := by
  induction u with
  | nil i =>
      change relation S v = TRel.comp (TRel.ident X i) (relation S v)
      rw [TRel.ident_comp]
  | identity tail ih =>
      change relation S (append S tail v) =
        TRel.comp (relation S tail) (relation S v)
      exact ih
  | atom a tail ih =>
      change TRel.comp (S.atomRel a) (relation S (append S tail v)) =
        TRel.comp (TRel.comp (S.atomRel a) (relation S tail))
          (relation S v)
      rw [ih, TRel.comp_assoc]

theorem atomRel_flip (a : S.Atom i j) :
    S.atomRel (S.conv a) = TRel.converse (S.atomRel a) := by
  funext y x
  apply propext
  change S.colour y x = some (S.conv a) ↔ S.colour x y = some a
  exact (S.colour_swap x y a).symm

/-- Reversal may erase identity letters, which do not affect the profile. -/
def reverse {i j : ι} : RawWord S i j → RawWord S j i
  | .nil i => .nil i
  | .identity tail => reverse tail
  | .atom a tail =>
      append S (reverse tail) (.atom (S.conv a) (.nil _))

theorem relation_reverse (w : RawWord S i j) :
    relation S (reverse S w) = TRel.converse (relation S w) := by
  induction w with
  | nil i =>
      funext x y
      apply propext
      exact eq_comm
  | identity tail ih => exact ih
  | atom a tail ih =>
      change relation S (append S (reverse S tail)
          (.atom (S.conv a) (.nil _))) =
        TRel.converse (TRel.comp (S.atomRel a) (relation S tail))
      rw [S.relation_append, ih]
      change TRel.comp (TRel.converse (relation S tail))
        (TRel.comp (S.atomRel (S.conv a)) (TRel.ident X _)) =
          TRel.converse (TRel.comp (S.atomRel a) (relation S tail))
      rw [TRel.comp_ident, S.atomRel_flip]
      exact (TRel.converse_comp (S.atomRel a) (relation S tail)).symm

theorem empty_word_is_identity (i : ι) :
    relation S (.nil i) = TRel.ident X i :=
  rfl

theorem identity_letter_is_identity (i : ι) :
    relation S (.identity (.nil i)) = TRel.ident X i :=
  rfl

end RawWord
end CCO
