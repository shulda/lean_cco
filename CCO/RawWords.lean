import CCO.Atomic

/-!
# RAW words: logical equality is a real letter, not a diversity atom

An equality letter is the left summand of a *tagged* letter type, and an
atomic diversity letter is the right summand. Deleting an equality letter
does not project away any diagonal *output* of a nonempty diversity walk.
The theorem deletes an identity anywhere in a typed word, without
changing its represented endpoint relation.
-/

universe u v w

namespace CCO

/-- Logical equality exists only on loop sorts. The other constructor
uses a genuine diversity atom, so a fake identity cannot be inserted. -/
abbrev RawLetter {ι : Type u} {X : ι → Type v}
    (S : AtomicSource ι X) (i j : ι) :=
  (i = j) ⊕ S.Atom i j

namespace RawLetter

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource ι X)
variable {i j : ι}

def relation (a : RawLetter S i j) : TRel X i j :=
  match a with
  | .inl h => by
      cases h
      exact TRel.ident X i
  | .inr c => S.atomRel c

def flip (a : RawLetter S i j) : RawLetter S j i :=
  match a with
  | .inl h => .inl h.symm
  | .inr c => .inr (S.conv c)

theorem relation_flip (a : RawLetter S i j) :
    relation S (flip S a) = TRel.converse (relation S a) := by
  cases a with
  | inl h =>
      cases h
      funext y x
      apply propext
      exact eq_comm
  | inr c =>
      funext y x
      apply propext
      exact (S.colour_swap x y c).symm

end RawLetter

abbrev RawWord {ι : Type u} {X : ι → Type v}
    (S : AtomicSource ι X) (i j : ι) :=
  TypedWord (RawLetter S) i j

namespace TypedWord

variable {ι : Type u} {L : ι → ι → Type w} {X : ι → Type v}

/-- Delete a *genuine identity letter*, at an arbitrary position (specified
by typed prefix and suffix). The resulting represented relation, including
all diagonal outputs of the remaining word, is unchanged. -/
theorem eval_delete_identity
    (repr : ∀ {a b : ι}, L a b → TRel X a b)
    {i j k : ι} (prefix : TypedWord L i j)
    (e : L j j) (suffix : TypedWord L j k)
    (he : repr e = TRel.ident X j) :
    eval repr (append prefix (.cons e suffix)) =
      eval repr (append prefix suffix) := by
  calc
    eval repr (append prefix (.cons e suffix)) =
        TRel.comp (eval repr prefix) (eval repr (.cons e suffix)) :=
          eval_append repr prefix (.cons e suffix)
    _ = TRel.comp (eval repr prefix)
          (TRel.comp (repr e) (eval repr suffix)) := rfl
    _ = TRel.comp (eval repr prefix) (eval repr suffix) := by
          rw [he, TRel.ident_comp]
    _ = eval repr (append prefix suffix) :=
          (eval_append repr prefix suffix).symm

/-- Reverse a composable typed word, including the genuine empty loop. -/
def reverse (flip : ∀ {a b : ι}, L a b → L b a)
    {i j : ι} : TypedWord L i j → TypedWord L j i
  | .nil i => .nil i
  | .cons a tail =>
      append (reverse flip tail) (.cons (flip a) (.nil _))

theorem eval_reverse
    (repr : ∀ {a b : ι}, L a b → TRel X a b)
    (flip : ∀ {a b : ι}, L a b → L b a)
    (hflip : ∀ {a b : ι} (e : L a b),
      repr (flip e) = TRel.converse (repr e))
    {i j : ι} (w : TypedWord L i j) :
    eval repr (reverse flip w) = TRel.converse (eval repr w) := by
  induction w with
  | nil i =>
      funext x y
      apply propext
      exact eq_comm
  | cons a tail ih =>
      change eval repr (append (reverse flip tail)
          (.cons (flip a) (.nil _))) =
        TRel.converse (TRel.comp (repr a) (eval repr tail))
      rw [eval_append]
      change TRel.comp (eval repr (reverse flip tail))
          (TRel.comp (repr (flip a)) (TRel.ident X _)) =
        TRel.converse (TRel.comp (repr a) (eval repr tail))
      rw [TRel.comp_ident, ih, hflip]
      exact (TRel.converse_comp (repr a) (eval repr tail)).symm

end TypedWord

namespace RawWord

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource ι X)
variable {i j k : ι}

def relation (w : RawWord S i j) : TRel X i j :=
  TypedWord.eval (RawLetter.relation S) w

/-- Identity letters can be deleted anywhere. -/
theorem delete_equality (prefix : RawWord S i j)
    (suffix : RawWord S j k) :
    relation S (TypedWord.append prefix
      (.cons (.inl rfl) suffix)) =
    relation S (TypedWord.append prefix suffix) := by
  exact TypedWord.eval_delete_identity (RawLetter.relation S)
    prefix (.inl rfl) suffix rfl

theorem relation_reverse (w : RawWord S i j) :
    relation S (TypedWord.reverse (RawLetter.flip S) w) =
      TRel.converse (relation S w) := by
  exact TypedWord.eval_reverse (RawLetter.relation S)
    (RawLetter.flip S) (RawLetter.relation_flip S) w

theorem relation_append (u : RawWord S i j) (v : RawWord S j k) :
    relation S (TypedWord.append u v) =
      TRel.comp (relation S u) (relation S v) :=
  TypedWord.eval_append (RawLetter.relation S) u v

theorem empty_word_is_identity (i : ι) :
    relation S (.nil i) = TRel.ident X i :=
  rfl

end RawWord
end CCO
