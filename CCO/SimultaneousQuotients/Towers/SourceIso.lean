import CCO.SimultaneousQuotients.Towers.AtomicIso
import CCO.Atomic

/-! Actual complete atomic structure isomorphisms from equivariant bijections
of carriers in complete orbital languages. Atom names are transported
canonically from their realized relations; logical equality is preserved too. -/

universe u v w q r t
namespace CCO.SimultaneousQuotients.Towers

structure AtomicIso {ι : Type u} {A : ι → Type v} {B : ι → Type q}
    (S : AtomicSource.{u,v,w} ι A) (T : AtomicSource.{u,q,r} ι B) where
  point : ∀ i, A i ≃ B i
  atom : ∀ i j, S.Atom i j ≃ T.Atom i j
  colours : ∀ i j (x : A i) (y : A j),
    (S.colour x y).map (atom i j) = T.colour (point i x) (point j y)

section Construction
variable {ι : Type u} {A : ι → Type v} {B : ι → Type q}
variable (S : AtomicSource.{u,v,w} ι A) (T : AtomicSource.{u,q,r} ι B)
variable (e : ∀ i, A i ≃ B i)
variable (hp : ∀ {i j} (x x' : A i) (y y' : A j),
  S.colour x y = S.colour x' y' ↔
    T.colour (e i x) (e j y) = T.colour (e i x') (e j y'))

theorem equiv_colour_none {i j : ι} (x : A i) (y : A j) :
    T.colour (e i x) (e j y) = none ↔ S.colour x y = none := by
  constructor
  · intro h
    apply (S.colour_none_iff x y).mpr
    have hh := congrArg (fun p : Sigma B => (⟨p.1,(e p.1).symm p.2⟩ : Sigma A))
      ((T.colour_none_iff _ _).mp h)
    simpa only [Equiv.symm_apply_apply] using hh
  · intro h
    apply (T.colour_none_iff _ _).mpr
    exact congrArg (fun p : Sigma A => (⟨p.1,e p.1 p.2⟩ : Sigma B))
      ((S.colour_none_iff x y).mp h)

include hp in
theorem source_atom_image_exists {i j : ι} (a : S.Atom i j) :
    ∃ b : T.Atom i j, ∀ x y,
      S.atomRel a x y ↔ T.atomRel b (e i x) (e j y) := by
  obtain ⟨x,y,hxy⟩ := S.realized a
  obtain ⟨b,hb⟩ : ∃ b : T.Atom i j, T.colour (e i x) (e j y) = some b := by
    cases hc : T.colour (e i x) (e j y) with
    | some b => exact ⟨b,rfl⟩
    | none =>
      have hh := (equiv_colour_none S T e x y).mp hc
      rw [hxy] at hh
      cases hh
  refine ⟨b,?_⟩
  intro x' y'
  change S.colour x' y' = some a ↔ T.colour (e i x') (e j y') = some b
  rw [←hxy,←hb]
  exact hp x' x y' y

noncomputable def sourceAtomMap {i j : ι} (a : S.Atom i j) : T.Atom i j :=
  Classical.choose (source_atom_image_exists S T e hp a)

theorem sourceAtomMap_relation {i j : ι} (a : S.Atom i j) (x : A i) (y : A j) :
    S.atomRel a x y ↔ T.atomRel (sourceAtomMap S T e hp a) (e i x) (e j y) :=
  Classical.choose_spec (source_atom_image_exists S T e hp a) x y

theorem sourceAtomMap_injective (i j : ι) :
    Function.Injective (sourceAtomMap S T e hp (i := i) (j := j)) := by
  intro a b hab
  obtain ⟨x,y,hxy⟩ := S.realized a
  have ha := (sourceAtomMap_relation S T e hp a x y).mp hxy
  rw [hab] at ha
  have hb := (sourceAtomMap_relation S T e hp b x y).mpr ha
  change S.colour x y = some b at hb
  rw [hxy] at hb
  exact Option.some.inj hb

theorem sourceAtomMap_surjective (i j : ι) :
    Function.Surjective (sourceAtomMap S T e hp (i := i) (j := j)) := by
  intro b
  obtain ⟨x,y,hxy⟩ := T.realized b
  let x' := (e i).symm x
  let y' := (e j).symm y
  have h' : T.colour (e i x') (e j y') = some b := by
    simpa only [x',y',Equiv.apply_symm_apply] using hxy
  obtain ⟨a,ha⟩ : ∃ a : S.Atom i j, S.colour x' y' = some a := by
    cases hc : S.colour x' y' with
    | some a => exact ⟨a,rfl⟩
    | none =>
      have hh := (equiv_colour_none S T e x' y').mpr hc
      rw [h'] at hh
      cases hh
  have hb := (sourceAtomMap_relation S T e hp a x' y').mp ha
  change T.colour (e i x') (e j y') = some (sourceAtomMap S T e hp a) at hb
  exact ⟨a,Option.some.inj (hb.symm.trans h')⟩

noncomputable def atomicIso : AtomicIso S T where
  point := e
  atom i j := Equiv.ofBijective _
    ⟨sourceAtomMap_injective S T e hp i j,sourceAtomMap_surjective S T e hp i j⟩
  colours i j x y := by
    cases hc : S.colour x y with
    | none => exact ((equiv_colour_none S T e x y).mpr hc).symm
    | some a =>
      exact ((sourceAtomMap_relation S T e hp a x y).mp hc).symm

end Construction
end CCO.SimultaneousQuotients.Towers
