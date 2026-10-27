import CCO.RawExact.ConvolutionFromHelly
import CCO.RawSource

/-!
# RAW C09/C14: every genuine original atomic orbital is exact

The singleton diversity orbit is a one-letter RAW word; the genuine
logical diagonal is a zero-letter RAW word. Both presentations have
actual real witnesses, independently of CCO, quotient lifting, SAP or
any finite-meet distributivity assumption. Cross-sort equality is never
invented.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

theorem atomic_word_relation {i j : ι} (a : S.Atom i j) :
    evaluate S [RawWord.atom a (.nil j)] = S.atomRel a := by
  rw [evaluate_single S]
  change TRel.comp (S.atomRel a) (TRel.ident X j) = S.atomRel a
  exact TRel.comp_ident (S.atomRel a)

/-- Any genuine diversity atom is a nonempty RAW exact relation:
its witness comes directly from the actual source colouring. -/
def exactDiversityAtom {i j : ι} (a : S.Atom i j) :
    NonemptyExact S i j := by
  refine ⟨[RawWord.atom a (.nil j)], ?_⟩
  rw [atomic_word_relation S a]
  obtain ⟨x, y, hxy⟩ := S.realized a
  exact ⟨x, y, hxy⟩

theorem exactDiversityAtom_relation {i j : ι}
    (a : S.Atom i j) :
    evaluate S (exactDiversityAtom S a).words = S.atomRel a :=
  atomic_word_relation S a

/-- The empty RAW word (not an empty LIST of restrictions) encodes
the ACTUAL same-sort identity relation, and is itself nonempty. -/
def exactIdentityAtom (i : ι) : NonemptyExact S i i := by
  refine ⟨[RawWord.nil i], ?_⟩
  rw [evaluate_single S]
  obtain ⟨x⟩ := S.nonemptySort i
  exact ⟨x, x, rfl⟩

theorem exactIdentityAtom_relation (i : ι) :
    evaluate S (exactIdentityAtom S i).words = TRel.ident X i := by
  rw [evaluate_single S]
  rfl

/-- A source equality atom is the true represented diagonal;
neither cross-sort identity nor an extra diversity colour exists. -/
theorem exactIdentityAtom_is_optional_none (i : ι) :
    evaluate S (exactIdentityAtom S i).words =
      S.rawAtomRel (none : Option (S.Atom i i)) := by
  rw [exactIdentityAtom_relation S i]
  funext x y
  apply propext
  constructor
  · intro h
    change x = y at h
    subst y
    exact (S.colour_none_iff x x).mpr rfl
  · intro h
    have hs : (⟨i, x⟩ : Sigma X) = ⟨i, y⟩ :=
      (S.colour_none_iff x y).mp h
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hs

end CCO.RawExact
