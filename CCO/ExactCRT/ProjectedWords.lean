import CCO.ExactCRT.TypedPullback
import CCO.ExactCRT.Intertwining

/-! A real original word projects to ONE actual quotient RAW word.
Old diversity letters may become genuine quotient equality letters.
No universal mixed-sort commutation is used here. -/
universe u v w q r t
namespace CCO.ExactCRT
open RawExact

/-- Every actual optional pair colour has a SINGLE RAW word, including
cross-sort and quotient-equality boundaries. -/
theorem actualPairWord_exists {ι : Type u} {Q : ι → Type q}
    (T : AtomicSource.{u,q,r} ι Q) {i j : ι} (x : Q i) (y : Q j) :
    ∃ word : RawWord T i j, RawWord.relation T word = T.rawAtomRel (T.colour x y) := by
  cases hc : T.colour x y with
  | some a =>
      refine ⟨.atom a (.nil j), ?_⟩
      change TRel.comp (T.atomRel a) (TRel.ident Q j) = T.atomRel a
      exact TRel.comp_ident _
  | none =>
      have htag := (T.colour_none_iff x y).mp hc
      cases htag
      refine ⟨.nil i, ?_⟩
      exact (exactIdentityAtom_is_optional_none T i).symm.trans
        (exactIdentityAtom_relation T i) |>.symm

noncomputable def actualPairWord {ι : Type u} {Q : ι → Type q}
    (T : AtomicSource.{u,q,r} ι Q) {i j : ι} (x : Q i) (y : Q j) : RawWord T i j :=
  Classical.choose (actualPairWord_exists T x y)

theorem actualPairWord_relation {ι : Type u} {Q : ι → Type q}
    (T : AtomicSource.{u,q,r} ι Q) {i j : ι} (x : Q i) (y : Q j) :
    RawWord.relation T (actualPairWord T x y) = T.rawAtomRel (T.colour x y) :=
  Classical.choose_spec (actualPairWord_exists T x y)

variable {ι : Type u} {X : ι → Type v} {Q : ι → Type q}
variable (S : AtomicSource.{u,v,w} ι X) (T : AtomicSource.{u,q,r} ι Q)
variable (π : ∀i, X i → Q i)

noncomputable def projectedLetter {i j : ι} (a : S.Atom i j) : RawWord T i j :=
  let p := Classical.choose (S.realized a)
  let p' := Classical.choose (Classical.choose_spec (S.realized a))
  actualPairWord T (π i p) (π j p')

noncomputable def projectedWord {i j : ι} : RawWord S i j → RawWord T i j
  | .nil i => .nil i
  | .identity tail => .identity (projectedWord tail)
  | .atom a tail => RawWord.append T (projectedLetter S T π a) (projectedWord tail)

variable {G : Type t} [Group G] [∀i, MulAction G (X i)] [∀i, MulAction G (Q i)]
variable (H : HomogeneousSource S G)
variable (equivπ : ∀i (g : G) x, π i (g • x) = g • π i x)
variable (E : ∀i, NonemptyExact S i i)
variable (hE : ∀i, GroupActions.kernel (π i) = evaluate S (E i).words)
variable (hT : ∀ {i j} (x : Q i) (y : Q j) (x' : Q i) (y' : Q j),
  T.colour x y = T.colour x' y' ↔ GroupActions.orbital (G := G) x y x' y')
include H equivπ hE hT

/-- Actual old optional colour and actual quotient orbit give precisely
one saturated atomic block. No external block provider is assumed. -/
theorem projectedLetter_pullback {i j : ι} (a : S.Atom i j) :
    GroupActions.pullback (π i) (π j)
      (RawWord.relation T (projectedLetter S T π a)) =
      saturate (evaluate S (E i).words) (S.atomRel a) (evaluate S (E j).words) := by
  unfold projectedLetter
  rw [actualPairWord_relation T]
  rw [quotient_pair_block S T H π equivπ E hE hT]
  have h := Classical.choose_spec (Classical.choose_spec (S.realized a))
  rw [h]
  rfl

variable (surjπ : ∀i, Function.Surjective (π i))
include surjπ

/-- Without TI the actual pullback retains ALL genuine intermediate
kernels, including those at repeated sorts and at zero-length words. -/
theorem projectedWord_pullback {i j : ι} (word : RawWord S i j) :
    GroupActions.pullback (π i) (π j)
      (RawWord.relation T (projectedWord S T π word)) =
      kernelWord S (fun i => evaluate S (E i).words) word := by
  induction word with
  | nil i => exact hE i
  | identity tail ih => exact ih
  | @atom i j k a tail ih =>
    change GroupActions.pullback (π i) (π k)
      (RawWord.relation T (RawWord.append T _ _)) = _
    rw [RawWord.relation_append T]
    change GroupActions.pullback (π i) (π k)
      (fun x z => ∃ y, RawWord.relation T (projectedLetter S T π a) x y ∧
        RawWord.relation T (projectedWord S T π tail) y z) = _
    rw [pullback_comp (π i) (π j) (π k) (surjπ j)]
    rw [projectedLetter_pullback S T π H equivπ E hE hT, ih]
    rfl

/-- C23: only the letters in THIS word require intertwining. -/
theorem projectedWord_pullback_of_TI {i j : ι} (word : RawWord S i j)
    (hTI : WordTI S (fun i => evaluate S (E i).words) word) :
    GroupActions.pullback (π i) (π j)
      (RawWord.relation T (projectedWord S T π word)) =
      saturate (evaluate S (E i).words) (RawWord.relation S word)
        (evaluate S (E j).words) := by
  rw [projectedWord_pullback S T π H equivπ E hE hT surjπ]
  apply kernelWord_eq_saturate S _ _ word hTI
  intro i
  rw [← hE i]
  exact kernel_equiv (π i)

end CCO.ExactCRT
