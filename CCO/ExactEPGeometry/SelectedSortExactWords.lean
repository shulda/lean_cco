import CCO.ExactEPGeometry.SelectedSortExactRetyping
import CCO.RigidGroupoid.Geometry.Basic

/-!
# B062 C82: actual selected-sort transport of ALL equality-inclusive RAW words

The C82 selected-sort step cannot merely restrict old exact
presentations: old words can visit deleted intermediate sort names.
Given the ACTUAL equivariant point equivalences from the C82 orbital
retyping source, EVERY old intermediate witness can be transported
bijectively into its chosen selected sort.

This module constructs:
* a single correctly typed selected RAW word for every original word,
  preserving its WHOLE relation in both directions;
* the full finite restriction list for every genuine NONEMPTY RAW
  exact presentation, with its original actual pair witness;
* a complete full-RAW-exact image relation for any original full-exact
  relation, on arbitrary retyped endpoint sorts.

Nil and identity letters remain genuine equality, and an old diversity
atom that becomes quotient equality is transported by a genuine
actualPairWord, not converted to a fictitious diversity letter.

There is NO SAP, new axiom, arbitrary quotient descent, chosen
automorphism section or assumed full-exactness under plain deletion.
-/

universe u v w t

namespace CCO.ExactEPGeometry

noncomputable section

variable {ι κ : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable [Fintype κ] {σ : κ ↪ ι}
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (D : SelectedRetyping (X := X) σ (G := G))

namespace SelectedRetyping

/-- C82 actual RAW word retyping through EVERY intermediate old
sort, using one real equivariant E-class carrier equivalence at
each visited sort. Even a formerly diversity atom may be sent to
the true selected diagonal when its whole quotient orbit collapses. -/
noncomputable def retypeWord {i j : ι} :
    RawWord S i j →
      RawWord (selectedSortAtomicSource S σ) (D.target i) (D.target j)
  | .nil i => .nil (D.target i)
  | .identity tail => .identity (retypeWord tail)
  | .atom a tail =>
      RawWord.append (selectedSortAtomicSource S σ)
        (D.atomWord a) (retypeWord tail)

/-- The entire relation of EVERY original equality-inclusive RAW
word is preserved and reflected by literal REAL point equivalences
on both endpoints, with all intermediate witnesses translated
into the original word's corresponding selected sorts. -/
theorem retypeWord_iff
    (H : HomogeneousSource S G)
    {i j : ι} (word : RawWord S i j) :
    ∀ (x : X i) (z : X j),
      RawWord.relation S word x z ↔
        RawWord.relation (selectedSortAtomicSource S σ)
          (D.retypeWord word)
          (D.pointEquiv i x) (D.pointEquiv j z) := by
  induction word with
  | nil i =>
      intro x z
      change x = z ↔ D.pointEquiv i x = D.pointEquiv i z
      constructor
      · intro h
        subst z
        rfl
      · intro h
        exact (D.pointEquiv i).injective h
  | identity tail ih =>
      intro x z
      exact ih x z
  | @atom i j k a tail ih =>
      intro x z
      change (∃ y : X j, S.atomRel a x y ∧
          RawWord.relation S tail y z) ↔
        RawWord.relation (selectedSortAtomicSource S σ)
          (RawWord.append (selectedSortAtomicSource S σ)
            (D.atomWord a) (D.retypeWord tail))
          (D.pointEquiv i x) (D.pointEquiv k z)
      rw [RawWord.relation_append (selectedSortAtomicSource S σ)]
      change (∃ y : X j, S.atomRel a x y ∧
          RawWord.relation S tail y z) ↔
        ∃ y : X (σ (D.target j)),
          RawWord.relation (selectedSortAtomicSource S σ)
            (D.atomWord a) (D.pointEquiv i x) y ∧
          RawWord.relation (selectedSortAtomicSource S σ)
            (D.retypeWord tail) y (D.pointEquiv k z)
      constructor
      · rintro ⟨y,hxy,hyz⟩
        exact ⟨D.pointEquiv j y,
          (D.atomWord_iff H a x y).mp hxy,
          (ih y z).mp hyz⟩
      · rintro ⟨q,hxq,hqz⟩
        let y : X j := (D.pointEquiv j).symm q
        have hEq : D.pointEquiv j y = q :=
          (D.pointEquiv j).apply_symm_apply q
        refine ⟨y,?_,?_⟩
        · apply (D.atomWord_iff H a x y).mpr
          rw [hEq]
          exact hxq
        · apply (ih y z).mpr
          rw [hEq]
          exact hqz

/-- C82 semantic exactness with no erased source witness: every
nonempty original finite RAW presentation is retyped to a SINGLE
nonempty exact presentation on the selected sorts. -/
noncomputable def retypeExact
    (H : HomogeneousSource S G)
    {i j : ι} (R : RawExact.NonemptyExact S i j) :
    RawExact.NonemptyExact (selectedSortAtomicSource S σ)
      (D.target i) (D.target j) := by
  refine ⟨R.words.map (D.retypeWord),?_⟩
  obtain ⟨x,z,hxz⟩ := R.nonempty
  refine ⟨D.pointEquiv i x,D.pointEquiv j z,?_⟩
  intro word hw
  obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hw
  exact (D.retypeWord_iff H old x z).mp (hxz old hold)

/-- Full equality of the represented finite RAW intersections,
including the empty list (Top), nil-identity output and repeated
old intermediate sorts. No intersection support is replaced by
an unrelated set of pairwise compatible orbitals. -/
theorem retypeExact_iff
    (H : HomogeneousSource S G)
    {i j : ι} (R : RawExact.NonemptyExact S i j)
    (x : X i) (z : X j) :
    RawExact.evaluate S R.words x z ↔
      RawExact.evaluate (selectedSortAtomicSource S σ)
        (D.retypeExact H R).words
        (D.pointEquiv i x) (D.pointEquiv j z) := by
  change (∀ word, word ∈ R.words →
      RawWord.relation S word x z) ↔
    ∀ word, word ∈ R.words.map (D.retypeWord) →
      RawWord.relation (selectedSortAtomicSource S σ) word
        (D.pointEquiv i x) (D.pointEquiv j z)
  constructor
  · intro h word hw
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hw
    exact (D.retypeWord_iff H old x z).mp (h old hold)
  · intro h word hw
    exact (D.retypeWord_iff H word x z).mpr
      (h (D.retypeWord word)
        (List.mem_map.mpr ⟨word,hw,rfl⟩))

/-- Source-level C82 FULL RAW-exact transport. The TARGET relation
is the literal equivalence-transport of the whole real old relation,
not an unproved assumption about restricting an arbitrary selected
sublanguage. Recovered endpoints will be proven literally fixed
by the coherent original E-class transport in the B062 application. -/
theorem retypeFullExact
    (H : HomogeneousSource S G)
    {i j : ι} (R : TRel X i j)
    (hExact : RigidGroupoid.Geometry.FullExact S R) :
    RigidGroupoid.Geometry.FullExact
      (selectedSortAtomicSource S σ)
      (fun a b =>
        R ((D.pointEquiv i).symm a) ((D.pointEquiv j).symm b)) := by
  obtain ⟨W,hW⟩ := hExact
  refine ⟨D.retypeExact H W,?_⟩
  funext a b
  apply propext
  have h := D.retypeExact_iff H W
    ((D.pointEquiv i).symm a) ((D.pointEquiv j).symm b)
  simpa only [Equiv.apply_symm_apply,hW] using h.symm

end SelectedRetyping
end
end CCO.ExactEPGeometry
