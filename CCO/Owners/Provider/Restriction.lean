import CCO.Owners.Provider.FiniteBase
import Mathlib.Data.Set.Finite.Lattice

/-! C02–C03: one EPPA host and its restriction above the ENTIRE fixed
finite owner base. Ambient lifts are explicit input only in this generic
theorem; the exact-source branch constructs them. -/
namespace CCO.Owners.Provider
open Product
variable {G A O R : Type*} [Group G] [MulAction G A] [MulAction G O] [Finite R]

theorem finite_base_restriction
    (hom : OrbitalHomogeneous G A) (ep : OrdinaryEPPA G A)
    (π : A → O) (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (S : Set A) (B : Set O) (hS : S.Finite) (hB : B.Finite)
    (hSB : ∀ x : S, π x.val ∈ B)
    (ontoS : Function.Surjective (ownerProjection π S B hSB))
    (γ : R → OrbitalAut G O (Subtype.val : B → O))
    (g : R → OrbitalAut G A (id : A → A))
    (owner : ∀ r (x : A) (hx : π x ∈ B),
      π ((g r).val x) = ((γ r).val ⟨π x,hx⟩).val) :
    ∃ W : Set A, W.Finite ∧ ∃ hSW : S ⊆ W,
      ∃ hWB : ∀ x : W, π x.val ∈ B,
      Function.Surjective (ownerProjection π W B hWB) ∧
      ∀ r : R, ∃ β : OrbitalAut G A (Subtype.val : W → A),
        (∀ x : S, (β.val ⟨x.val,hSW x.property⟩).val = (g r).val x.val) ∧
        (∀ x : W, π (β.val x).val =
          ((γ r).val (ownerProjection π W B hWB x)).val) := by
  classical
  let T : Set A := S ∪ ⋃ r : R, (g r).val '' S
  have hT : T.Finite := hS.union (Set.finite_iUnion (fun r => hS.image (g r).val))
  have hST : S ⊆ T := Set.subset_union_left
  obtain ⟨C,hC,hTC,hep⟩ := eppa_over_original hom ep T hT
  let W : Set A := C ∩ π ⁻¹' B
  have hW : W.Finite := hC.subset Set.inter_subset_left
  letI : Finite W := hW.to_subtype
  have hSW : S ⊆ W := fun x hx => ⟨hTC (hST hx),hSB ⟨x,hx⟩⟩
  have hWB : ∀ x : W, π x.val ∈ B := fun x => x.property.2
  have ontoW : Function.Surjective (ownerProjection π W B hWB) := by
    intro b
    obtain ⟨x,hx⟩ := ontoS b
    exact ⟨⟨x.val,hSW x.property⟩,hx⟩
  refine ⟨W,hW,hSW,hWB,ontoW,?_⟩
  intro r
  let p : OrbitalPartial (G := G) (Subtype.val : T → A) := {
    domain := {x | x.val ∈ S}
    map := fun x => ⟨(g r).val x.val.val,
      Or.inr (Set.mem_iUnion.mpr ⟨r,⟨x.val.val,x.property,rfl⟩⟩)⟩
    injective := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact (g r).val.injective (congrArg Subtype.val h)
    pair := fun x y => orbitalAut_pair (g r) x.val.val y.val.val }
  obtain ⟨β,hβ⟩ := hep p
  have extS (s : S) : (β.val ⟨s.val,hTC (hST s.property)⟩).val = (g r).val s.val :=
    hβ ⟨⟨s.val,hST s.property⟩,s.property⟩
  have ownerW (x : W) :
      π (β.val ⟨x.val,x.property.1⟩).val =
        ((γ r).val (ownerProjection π W B hWB x)).val := by
    let b : B := ownerProjection π W B hWB x
    obtain ⟨s,hs⟩ := ontoS b
    have hπs : π x.val = π s.val := (congrArg Subtype.val hs).symm
    have hk := (equivariant_kernel_iff π equivπ
      (orbitalAut_pair β ⟨x.val,x.property.1⟩ ⟨s.val,hTC (hST s.property)⟩)).mpr hπs
    change π (β.val ⟨x.val,x.property.1⟩).val = π (β.val ⟨s.val,_⟩).val at hk
    rw [hk,extS s,owner r s.val (hSB s)]
    exact congrArg (fun b : B => ((γ r).val b).val) hs
  have mapsW : ∀ x : W, (β.val ⟨x.val,x.property.1⟩).val ∈ W := by
    intro x
    refine ⟨(β.val ⟨x.val,x.property.1⟩).property,?_⟩
    change π (β.val ⟨x.val,x.property.1⟩).val ∈ B
    rw [ownerW x]
    exact ((γ r).val (ownerProjection π W B hWB x)).property
  let βW := restrictInducedAut β Set.inter_subset_left mapsW
  refine ⟨βW,?_,?_⟩
  · intro s
    exact extS s
  · exact ownerW

/-- Empty owner bases have only the empty actual witness, independently
of EPPA and of any requested owner permutation. -/
theorem empty_base_forces_empty (π : A → O) (D : Set A)
    (h : ∀ x ∈ D, π x ∈ (∅ : Set O)) : D = ∅ := by
  ext x
  exact ⟨fun hx => h x hx,fun hx => hx.elim⟩

end CCO.Owners.Provider
