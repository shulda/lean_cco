import CCO.Owners.Provider.GenericEPPA
import Mathlib.Data.Set.Finite.Lattice

/-! The genuinely generic finite-base theorem for relational languages
of arbitrary arity. Full induced automorphisms preserve EVERY original
relation; no binary-orbital replacement or countability is used. -/
namespace CCO.Owners.Provider.Relational
variable {A O R : Type*} (S : Structure A) [Finite R]

/-- The actual quotient kernel is recognized by finite induced maps in
the ORIGINAL relational language. This is the explicit source quotient
recognition premise, quantified over full all-arity automorphisms. -/
def KernelRecognizable (π : A → O) : Prop :=
  ∀ C : Set A, C.Finite → ∀ β : Aut S (Subtype.val : C → A), ∀ x y : C,
    π (β.val x).val = π (β.val y).val ↔ π x.val = π y.val

/-- An actual invariant quotient of the full original structure. -/
def KernelInvariant (π : A → O) : Prop :=
  ∀ g : Aut S (id : A → A), ∀ x y : A,
    π x = π y → π (g.val x) = π (g.val y)

/-- Original all-arity homogeneity derives finite kernel recognition;
it is not retained as an additional unproved provider in the generic export. -/
theorem kernelRecognizable_of_invariant (hom : Homogeneous S)
    (π : A → O) (invariant : KernelInvariant S π) : KernelRecognizable S π := by
  intro C hC β x y
  obtain ⟨g,hg⟩ := finite_aut_ambient S hom C hC β
  constructor
  · intro hxy
    have h := invariant g⁻¹ (β.val x).val (β.val y).val hxy
    rw [← hg x,← hg y] at h
    simpa using h
  · intro hxy
    have h := invariant g x.val y.val hxy
    simpa only [hg x,hg y] using h

noncomputable def restrictInducedAut {C D : Set A} [Finite D]
    (β : Aut S (Subtype.val : C → A)) (inside : D ⊆ C)
    (maps : ∀ x : D, (β.val ⟨x.val,inside x.property⟩).val ∈ D) :
    Aut S (Subtype.val : D → A) := by
  let f : D → D := fun x => ⟨(β.val ⟨x.val,inside x.property⟩).val,maps x⟩
  have hi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hv : (β.val ⟨x.val,inside x.property⟩).val =
        (β.val ⟨y.val,inside y.property⟩).val := congrArg (fun z : D => z.val) h
    exact congrArg (fun z : C => z.val) (β.val.injective (Subtype.ext hv))
  let e : Equiv.Perm D := Equiv.ofBijective f ⟨hi,Finite.surjective_of_injective hi⟩
  refine ⟨e,?_⟩
  intro r tuple
  exact β.property r (fun j => ⟨(tuple j).val,inside (tuple j).property⟩)

/-- One finite all-arity EPPA host restricts above the entire fixed B.
The caller may restrict gamma to full owner-structure automorphisms;
the stronger statement below allows any supplied ambient-realized owner
permutations. The ambient-lift input is exactly the generic source premise. -/
theorem finite_base_restriction
    (hom : Homogeneous S) (ep : OrdinaryEPPA S)
    (π : A → O) (invariant : KernelInvariant S π)
    (T : Set A) (B : Set O) (hT : T.Finite) (hB : B.Finite)
    (over : ∀ x : T, π x.val ∈ B)
    (onto : Function.Surjective (fun x : T => (⟨π x.val,over x⟩ : B)))
    (γ : R → Equiv.Perm B) (g : R → Aut S (id : A → A))
    (owner : ∀ r (x : A) (hx : π x ∈ B),
      π ((g r).val x) = ((γ r) ⟨π x,hx⟩).val) :
    ∃ W : Set A, W.Finite ∧ ∃ contains : T ⊆ W,
      ∃ overW : ∀ x : W, π x.val ∈ B,
      Function.Surjective (fun x : W => (⟨π x.val,overW x⟩ : B)) ∧
      ∀ r : R, ∃ β : Aut S (Subtype.val : W → A),
        (∀ x : T, (β.val ⟨x.val,contains x.property⟩).val = (g r).val x.val) ∧
        (∀ x : W, π (β.val x).val = ((γ r) ⟨π x.val,overW x⟩).val) := by
  classical
  have recognizable := kernelRecognizable_of_invariant S hom π invariant
  let U : Set A := T ∪ ⋃ r : R, (g r).val '' T
  have hU : U.Finite := hT.union (Set.finite_iUnion (fun r => hT.image (g r).val))
  have inc : T ⊆ U := Set.subset_union_left
  obtain ⟨C,hC,incC,hep⟩ := eppa_over_original S hom ep U hU
  let W : Set A := C ∩ π ⁻¹' B
  have hW : W.Finite := hC.subset Set.inter_subset_left
  letI : Finite W := hW.to_subtype
  have contains : T ⊆ W := fun x hx => ⟨incC (inc hx),over ⟨x,hx⟩⟩
  have overW : ∀ x : W, π x.val ∈ B := fun x => x.property.2
  have ontoW : Function.Surjective (fun x : W => (⟨π x.val,overW x⟩ : B)) := by
    intro b
    obtain ⟨x,hx⟩ := onto b
    exact ⟨⟨x.val,contains x.property⟩,hx⟩
  refine ⟨W,hW,contains,overW,ontoW,?_⟩
  intro r
  let p : Partial S (Subtype.val : U → A) := {
    domain := {x | x.val ∈ T}
    map := fun x => ⟨(g r).val x.val.val,
      Or.inr (Set.mem_iUnion.mpr ⟨r,⟨x.val.val,x.property,rfl⟩⟩)⟩
    injective := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact (g r).val.injective (congrArg Subtype.val h)
    preserves := by
      intro symbol tuple
      exact (g r).property symbol (fun j => (tuple j).val.val) }
  obtain ⟨β,hβ⟩ := hep p
  have extT (x : T) : (β.val ⟨x.val,incC (inc x.property)⟩).val = (g r).val x.val :=
    hβ ⟨⟨x.val,inc x.property⟩,x.property⟩
  have ownerW (x : W) : π (β.val ⟨x.val,x.property.1⟩).val =
      ((γ r) ⟨π x.val,overW x⟩).val := by
    obtain ⟨a,ha⟩ := onto ⟨π x.val,overW x⟩
    have hπa : π x.val = π a.val := (congrArg Subtype.val ha).symm
    have hk := (recognizable C hC β ⟨x.val,x.property.1⟩
      ⟨a.val,incC (inc a.property)⟩).mpr hπa
    rw [hk,extT a,owner r a.val (over a)]
    exact congrArg (fun b : B => ((γ r) b).val) ha
  have maps : ∀ x : W, (β.val ⟨x.val,x.property.1⟩).val ∈ W := by
    intro x
    refine ⟨(β.val ⟨x.val,x.property.1⟩).property,?_⟩
    change π (β.val ⟨x.val,x.property.1⟩).val ∈ B
    rw [ownerW x]
    exact ((γ r) ⟨π x.val,overW x⟩).property
  exact ⟨restrictInducedAut S β Set.inter_subset_left maps,extT,ownerW⟩

/-- The original generic source formulation: the real input need not
meet every owner. Representatives of ALL B are adjoined before the one
EPPA host is formed. Empty input, empty B and empty request families remain
included. Any finite partial request extended by g is therefore extended
by the resulting beta, with its exact entire prescribed owner action. -/
theorem finite_base_lifting
    (hom : Homogeneous S) (ep : OrdinaryEPPA S)
    (π : A → O) (ontoπ : Function.Surjective π) (invariant : KernelInvariant S π)
    (T : Set A) (B : Set O) (hT : T.Finite) (hB : B.Finite)
    (over : ∀ x : T, π x.val ∈ B)
    (γ : R → Equiv.Perm B) (g : R → Aut S (id : A → A))
    (owner : ∀ r (x : A) (hx : π x ∈ B),
      π ((g r).val x) = ((γ r) ⟨π x,hx⟩).val) :
    ∃ W : Set A, W.Finite ∧ ∃ contains : T ⊆ W,
      ∃ overW : ∀ x : W, π x.val ∈ B,
      Function.Surjective (fun x : W => (⟨π x.val,overW x⟩ : B)) ∧
      ∀ r : R, ∃ β : Aut S (Subtype.val : W → A),
        (∀ x : T, (β.val ⟨x.val,contains x.property⟩).val = (g r).val x.val) ∧
        (∀ x : W, π (β.val x).val = ((γ r) ⟨π x.val,overW x⟩).val) := by
  classical
  letI : Finite B := hB.to_subtype
  let reps : B → A := fun b => Classical.choose (ontoπ b.val)
  have hrep (b : B) : π (reps b) = b.val := Classical.choose_spec (ontoπ b.val)
  let U : Set A := T ∪ Set.range reps
  have hU : U.Finite := hT.union (Set.finite_range reps)
  have inc : T ⊆ U := Set.subset_union_left
  have overU : ∀ x : U, π x.val ∈ B := by
    rintro ⟨x,hx⟩
    rcases hx with hx | ⟨b,rfl⟩
    · exact over ⟨x,hx⟩
    · rw [hrep b]; exact b.property
  have ontoU : Function.Surjective (fun x : U => (⟨π x.val,overU x⟩ : B)) := by
    intro b
    exact ⟨⟨reps b,Or.inr ⟨b,rfl⟩⟩,Subtype.ext (hrep b)⟩
  obtain ⟨W,hW,hUW,overW,ontoW,extensions⟩ :=
    finite_base_restriction S hom ep π invariant U B hU hB overU ontoU γ g owner
  refine ⟨W,hW,inc.trans hUW,overW,ontoW,?_⟩
  intro r
  obtain ⟨β,hβ,howner⟩ := extensions r
  exact ⟨β,fun x => hβ ⟨x.val,inc x.property⟩,howner⟩

/-- The finite list of genuine original partial requests, with their
supplied simultaneous ambient lifts, has ONE common witness. Empty real
domains with arbitrary owner motions are included without any coherence. -/
theorem finite_base_requests
    (hom : Homogeneous S) (ep : OrdinaryEPPA S)
    (π : A → O) (ontoπ : Function.Surjective π) (invariant : KernelInvariant S π)
    (T : Set A) (B : Set O) (hT : T.Finite) (hB : B.Finite)
    (over : ∀ x : T, π x.val ∈ B)
    (p : R → Partial S (Subtype.val : T → A))
    (γ : R → Equiv.Perm B) (g : R → Aut S (id : A → A))
    (extendsReal : ∀ r (x : (p r).domain),
      (g r).val x.val.val = ((p r).map x).val)
    (owner : ∀ r (x : A) (hx : π x ∈ B),
      π ((g r).val x) = ((γ r) ⟨π x,hx⟩).val) :
    ∃ W : Set A, W.Finite ∧ ∃ contains : T ⊆ W,
      ∃ overW : ∀ x : W, π x.val ∈ B,
      Function.Surjective (fun x : W => (⟨π x.val,overW x⟩ : B)) ∧
      ∀ r : R, ∃ β : Aut S (Subtype.val : W → A),
        (∀ x : (p r).domain,
          (β.val ⟨x.val.val,contains x.val.property⟩).val = ((p r).map x).val) ∧
        (∀ x : W, π (β.val x).val = ((γ r) ⟨π x.val,overW x⟩).val) := by
  obtain ⟨W,hW,contains,overW,ontoW,extensions⟩ :=
    finite_base_lifting S hom ep π ontoπ invariant T B hT hB over γ g owner
  refine ⟨W,hW,contains,overW,ontoW,?_⟩
  intro r
  obtain ⟨β,hβ,howner⟩ := extensions r
  exact ⟨β,fun x => (hβ x.val).trans (extendsReal r x),howner⟩

end CCO.Owners.Provider.Relational
