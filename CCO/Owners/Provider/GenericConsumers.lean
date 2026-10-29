import CCO.Owners.Provider.GenericRestriction

/-! A literal ternary-relation consumer of the generic finite-base
theorem. Ordinary homogeneity/EPPA refer to the ORIGINAL ternary relation,
and each resulting witness automorphism preserves every ternary tuple. -/
namespace CCO.Owners.Provider.Relational
variable {A O I : Type*} [Finite I]

def ternaryStructure (R : A → A → A → Prop) : Structure A where
  Symbol := Unit
  arity _ := 3
  relation _ tuple := R (tuple 0) (tuple 1) (tuple 2)

theorem ternary_aut_preserves (R : A → A → A → Prop) (D : Set A)
    (β : Aut (ternaryStructure R) (Subtype.val : D → A)) (x y z : D) :
    R (β.val x).val (β.val y).val (β.val z).val ↔ R x.val y.val z.val := by
  let tuple : Fin 3 → D := Fin.cases x (Fin.cases y (fun _ => z))
  exact β.property () tuple

theorem ternary_finite_base (R : A → A → A → Prop)
    (hom : Homogeneous (ternaryStructure R)) (ep : OrdinaryEPPA (ternaryStructure R))
    (π : A → O) (ontoπ : Function.Surjective π) (invariant : KernelInvariant (ternaryStructure R) π)
    (T : Set A) (B : Set O) (hT : T.Finite) (hB : B.Finite)
    (over : ∀ x : T, π x.val ∈ B)
    (γ : I → Equiv.Perm B) (g : I → Aut (ternaryStructure R) (id : A → A))
    (owner : ∀ i (x : A) (hx : π x ∈ B), π ((g i).val x) = ((γ i) ⟨π x,hx⟩).val) :
    ∃ W : Set A, W.Finite ∧ ∃ contains : T ⊆ W,
      ∃ overW : ∀ x : W, π x.val ∈ B,
      Function.Surjective (fun x : W => (⟨π x.val,overW x⟩ : B)) ∧
      ∀ i : I, ∃ β : Aut (ternaryStructure R) (Subtype.val : W → A),
        (∀ x : T, (β.val ⟨x.val,contains x.property⟩).val = (g i).val x.val) ∧
        (∀ x : W, π (β.val x).val = ((γ i) ⟨π x.val,overW x⟩).val) ∧
        ∀ x y z : W, R (β.val x).val (β.val y).val (β.val z).val ↔ R x.val y.val z.val := by
  obtain ⟨W,hW,contains,overW,ontoW,extensions⟩ :=
    finite_base_lifting (ternaryStructure R) hom ep π ontoπ invariant T B hT hB over γ g owner
  refine ⟨W,hW,contains,overW,ontoW,?_⟩
  intro i
  obtain ⟨β,hβ,howner⟩ := extensions i
  exact ⟨β,hβ,howner,ternary_aut_preserves R W β⟩

end CCO.Owners.Provider.Relational
