import CCO.Atomic

/-!
# RAW words with genuine identity letters

An equality letter has a separate constructor from every diversity atom.
Removing equality *letters* preserves the full represented profile; it
does **not** delete diagonal pairs from the profile of a nonempty word.
-/

universe u v w

namespace CCO

inductive RawLetter {ι : Type u} {X : ι → Type v}
    (S : AtomicSource ι X) : ι → ι → Type w where
  | equality (i : ι) : RawLetter S i i
  | diversity {i j : ι} (a : S.Atom i j) : RawLetter S i j

namespace RawLetter

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource ι X)
variable {i j : ι}

def relation : RawLetter S i j → TRel X i j
  | .equality i => TRel.ident X i
  | .diversity a => S.atomRel a

def flip : RawLetter S i j → RawLetter S j i
  | .equality i => .equality i
  | .diversity a => .diversity (S.conv a)

theorem relation_flip (a : RawLetter S i j) :
    relation S (flip S a) = TRel.converse (relation S a) := by
  cases a with
  | equality i =>
      funext y x
      apply propext
      exact eq_comm
  | diversity a =>
      funext y x
      apply propext
      exact (S.colour_swap x y a).symm

end RawLetter

abbrev RawWord {ι : Type u} {X : ι → Type v}
    (S : AtomicSource ι X) (i j : ι) :=
  TypedWord (RawLetter S) i j

namespace RawWord

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource ι X)
variable {i j k : ι}

def relation (w : RawWord S i j) : TRel X i j :=
  TypedWord.eval (RawLetter.relation S) w

def eraseEquality : RawWord S i j → RawWord S i j
  | .nil i => .nil i
  | .cons (.equality _) tail => eraseEquality tail
  | .cons (.diversity a) tail => .cons (.diversity a) (eraseEquality tail)

theorem relation_eraseEquality (w : RawWord S i j) :
    relation S (eraseEquality S w) = relation S w := by
  induction w with
  | nil i => rfl
  | cons a tail ih =>
      cases a with
      | equality i =>
          change relation S (eraseEquality S tail) =
            TRel.comp (TRel.ident X i) (relation S tail)
          rw [TRel.ident_comp]
          exact ih
      | diversity a =>
          change TRel.comp (S.atomRel a) (relation S (eraseEquality S tail)) =
            TRel.comp (S.atomRel a) (relation S tail)
          rw [ih]

def reverse : RawWord S i j → RawWord S j i
  | .nil i => .nil i
  | .cons a tail =>
      TypedWord.append (reverse tail)
        (.cons (RawLetter.flip S a) (.nil _))

theorem relation_reverse (w : RawWord S i j) :
    relation S (reverse S w) = TRel.converse (relation S w) := by
  induction w with
  | nil i =>
      funext x y
      apply propext
      exact eq_comm
  | cons a tail ih =>
      change TRel.comp (relation S (reverse S tail))
          (TRel.comp (RawLetter.relation S (RawLetter.flip S a))
            (TRel.ident X _)) =
        TRel.converse (TRel.comp (RawLetter.relation S a) (relation S tail))
      rw [TRel.comp_ident, ih, RawLetter.relation_flip]
      exact (TRel.converse_comp (RawLetter.relation S a) (relation S tail)).symm

theorem relation_append (u : RawWord S i j) (v : RawWord S j k) :
    relation S (TypedWord.append u v) =
      TRel.comp (relation S u) (relation S v) :=
  TypedWord.eval_append (RawLetter.relation S) u v

theorem empty_word_is_identity (i : ι) :
    relation S (.nil i) = TRel.ident X i :=
  rfl

end RawWord

end CCO
