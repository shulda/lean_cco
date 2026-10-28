import CCO.RigidGroupoid.Geometry.Quotient.Algebra
import CCO.RigidGroupoid.Geometry.Quotient.Calculus

/-! Actual old full-exact blocks and their actual quotient orbital partition.
Logical equality is included, and distinct quotient sorts keep their tags. -/

universe u v w q r t

namespace CCO.RigidGroupoid.Geometry.Quotient

open RawExact

variable {ι : Type u} {X : ι → Type v} {Q : ι → Type q}
variable (S : AtomicSource.{u,v,w} ι X) (T : AtomicSource.{u,q,r} ι Q)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)] [∀ i, MulAction G (Q i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (π : ∀ i, X i → Q i) (surjπ : ∀ i, Function.Surjective (π i))
variable (equivπ : ∀ i (g : G) x, π i (g • x) = g • π i x)
variable (E : ∀ i, NonemptyExact S i i)
variable (hE : ∀ i, GroupActions.kernel (π i) = evaluate S (E i).words)
variable (hT : ∀ {i j} (x : Q i) (y : Q j) (x' : Q i) (y' : Q j),
  T.colour x y = T.colour x' y' ↔ GroupActions.orbital (G := G) x y x' y')

def block {i j : ι} (c : Option (S.Atom i j)) : TRel X i j :=
  saturate (evaluate S (E i).words) (S.rawAtomRel c) (evaluate S (E j).words)

include H cco in
theorem block_fullExact {i j : ι} (x : X i) (y : X j) :
    FullExact S (block S E (S.colour x y)) := by
  let C := exactCalculus_of_homogeneous_CCO S H cco
  exact C.comp (C.comp ⟨E i,rfl⟩ (fullExact_actual_atom S x y)) ⟨E j,rfl⟩

include hE in
theorem atom_subset_block {i j : ι} (c : Option (S.Atom i j)) :
    ∀ x y, S.rawAtomRel c x y → block S E c x y := by
  intro x y hxy
  refine ⟨y,⟨x,?_,hxy⟩,?_⟩
  · rw [←hE i]
    rfl
  · rw [←hE j]
    rfl

include H π equivπ hE hT in
/-- The same actual quotient pair orbital has the full old block as inverse
image. An old diversity atom may project to quotient logical equality.
-/
theorem block_pullback {i j : ι} (x : X i) (y : X j) :
    block S E (S.colour x y) = GroupActions.pullback (π i) (π j)
      (T.rawAtomRel (T.colour (π i x) (π j y))) :=
  (ExactCRT.quotient_pair_block S T H π equivπ E hE hT x y).symm

include H π equivπ hE hT in
theorem blocks_equal_or_disjoint {i j : ι} (x x' : X i) (y y' : X j) :
    block S E (S.colour x y) = block S E (S.colour x' y') ∨
      ∀ a b, ¬ (block S E (S.colour x y) a b ∧ block S E (S.colour x' y') a b) := by
  by_cases hc : T.colour (π i x) (π j y) = T.colour (π i x') (π j y')
  · left
    rw [block_pullback S T H π equivπ E hE hT x y,
      block_pullback S T H π equivπ E hE hT x' y']
    exact congrArg (GroupActions.pullback (π i) (π j)) (by rw [hc])
  · right
    intro a b hab
    rw [block_pullback S T H π equivπ E hE hT x y,
      block_pullback S T H π equivπ E hE hT x' y'] at hab
    exact hc (hab.1.symm.trans hab.2)

include H π equivπ hE hT in
theorem block_left_saturated {i j : ι} (x : X i) (y : X j) :
    TRel.comp (evaluate S (E i).words) (block S E (S.colour x y)) =
      block S E (S.colour x y) := by
  rw [block_pullback S T H π equivπ E hE hT x y,←hE i]
  exact pullback_left_kernel (π i) (π j) _

include H π equivπ hE hT in
theorem block_right_saturated {i j : ι} (x : X i) (y : X j) :
    TRel.comp (block S E (S.colour x y)) (evaluate S (E j).words) =
      block S E (S.colour x y) := by
  rw [block_pullback S T H π equivπ E hE hT x y,←hE j]
  exact pullback_right_kernel (π i) (π j) _

include hE in
theorem equality_pullback (i : ι) :
    GroupActions.pullback (π i) (π i) (TRel.ident Q i) = evaluate S (E i).words := hE i

include hE in
theorem identity_block (i : ι) :
    block S E (none : Option (S.Atom i i)) = evaluate S (E i).words := by
  have hId : S.rawAtomRel (none : Option (S.Atom i i)) = TRel.ident X i :=
    (exactIdentityAtom_is_optional_none S i).symm.trans (exactIdentityAtom_relation S i)
  unfold block saturate
  rw [hId,TRel.comp_ident,←hE i]
  exact typed_equiv_comp_self _ ⟨fun _ => rfl,fun _ _ h => h.symm,fun _ _ _ h h' => h.trans h'⟩

include hE in
theorem optional_equality_pullback (i : ι) :
    GroupActions.pullback (π i) (π i) (T.rawAtomRel (none : Option (T.Atom i i))) =
      evaluate S (E i).words := by
  have hId : T.rawAtomRel (none : Option (T.Atom i i)) = TRel.ident Q i :=
    (exactIdentityAtom_is_optional_none T i).symm.trans (exactIdentityAtom_relation T i)
  rw [hId]
  exact hE i

include H π surjπ equivπ hE hT in
theorem every_quotient_pair_block {i j : ι} (q : Q i) (r : Q j) :
    ∃ (x : X i) (y : X j), π i x = q ∧ π j y = r ∧
      block S E (S.colour x y) = GroupActions.pullback (π i) (π j)
        (T.rawAtomRel (T.colour q r)) := by
  obtain ⟨x,rfl⟩ := surjπ i q
  obtain ⟨y,rfl⟩ := surjπ j r
  exact ⟨x,y,rfl,rfl,block_pullback S T H π equivπ E hE hT x y⟩

include hE in
theorem diversity_disjoint_kernel {i : ι} (a : T.Atom i i) :
    ∀ x y, ¬ (GroupActions.pullback (π i) (π i) (T.atomRel a) x y ∧
      evaluate S (E i).words x y) := by
  rintro x y ⟨ha,hxy⟩
  have hk : π i x = π i y := by
    rw [←hE i] at hxy
    exact hxy
  change T.colour (π i x) (π i y) = some a at ha
  rw [hk,(T.colour_none_iff (π i y) (π i y)).mpr rfl] at ha
  cases ha

include hT in
theorem same_sort_converse {i : ι} (R : TRel Q i i)
    (hR : TRel.Invariant (G := G) R) : TRel.converse R = R := by
  have hf : RawSymmetric.PairFlip (G := G) (A := Q i) :=
    T.pair_flip_of_pair_homogeneous (fun x x' y y' h => (hT x y x' y').mp h)
  funext x y
  apply propext
  constructor
  · intro hyx
    obtain ⟨g,hgy,hgx⟩ := hf y x
    simpa only [hgy,hgx] using hR g y x hyx
  · intro hxy
    change R y x
    obtain ⟨g,hgx,hgy⟩ := hf x y
    simpa only [hgx,hgy] using hR g x y hxy

include hT in
theorem invariant_serial {i j : ι} (R : TRel Q i j) (hn : TRel.Nonempty R)
    (hR : TRel.Invariant (G := G) R) : TRel.Serial R :=
  TRel.invariant_serial R (transitive T hT i) hR hn

include hT in
theorem invariant_coserial {i j : ι} (R : TRel Q i j) (hn : TRel.Nonempty R)
    (hR : TRel.Invariant (G := G) R) : TRel.Coserial R :=
  TRel.invariant_coserial R (transitive T hT j) hR hn

include hT in
theorem same_sort_commute {i : ι} (R U : TRel Q i i)
    (hR : TRel.Invariant (G := G) R) (hU : TRel.Invariant (G := G) U) :
    TRel.comp R U = TRel.comp U R := by
  have hf : RawSymmetric.PairFlip (G := G) (A := Q i) :=
    T.pair_flip_of_pair_homogeneous (fun x x' y y' h => (hT x y x' y').mp h)
  exact RawSymmetric.invariant_commute R U hR hU hf

end CCO.RigidGroupoid.Geometry.Quotient
