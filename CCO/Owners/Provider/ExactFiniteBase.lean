import CCO.Owners.Provider.Restriction
import CCO.Owners.Provider.ExactLift

/-! Exact fixed-base lifting and the ALL-request finite host (C05/C09).
The earlier ambient-lift input is constructed from original H+CCO and
the actual exact kernel, and is absent from this conclusion's premises. -/
universe v w t
namespace CCO.Owners.Provider
open Product RawExact
variable {A O : Type v} {G : Type t} [Group G] [MulAction G A] [MulAction G O]

theorem exact_fixed_base [Countable A]
    (S : AtomicSource.{0,v,w} Unit (fun _ => A))
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
    (ep : OrdinaryEPPA G A)
    (π : A → O) (ontoπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (K : NonemptyExact S () ()) (hK : GroupActions.kernel π = evaluate S K.words)
    (D : Set A) (B : Set O) (hDfin : D.Finite) (hBfin : B.Finite)
    (hD : ∀ x : D, π x.val ∈ B) :
    ∃ W : Set A, W.Finite ∧ ∃ hDW : D ⊆ W,
      ∃ hWB : ∀ x : W, π x.val ∈ B,
      Function.Surjective (ownerProjection π W B hWB) ∧
      ∀ r : OwnerRequest (G := G) π D B hD,
        ∃ β : OrbitalAut G A (Subtype.val : W → A),
          (∀ x : r.part.domain,
            (β.val ⟨x.val.val,hDW x.val.property⟩).val = (r.part.map x).val) ∧
          (∀ x : W, π (β.val x).val =
            (r.owner.val (ownerProjection π W B hWB x)).val) := by
  classical
  letI : Finite D := hDfin.to_subtype
  letI : Finite B := hBfin.to_subtype
  let reps : B → A := fun b => Classical.choose (ontoπ b.val)
  have reps_spec (b : B) : π (reps b) = b.val := Classical.choose_spec (ontoπ b.val)
  let T : Set A := D ∪ Set.range reps
  have hT : T.Finite := hDfin.union (Set.finite_range reps)
  have hDT : D ⊆ T := Set.subset_union_left
  have hTB : ∀ x : T, π x.val ∈ B := by
    rintro ⟨x,hx⟩
    rcases hx with hx | ⟨b,rfl⟩
    · exact hD ⟨x,hx⟩
    · rw [reps_spec b]; exact b.property
  have ontoT : Function.Surjective (ownerProjection π T B hTB) := by
    intro b
    exact ⟨⟨reps b,Or.inr ⟨b,rfl⟩⟩,Subtype.ext (reps_spec b)⟩
  let R := OwnerRequest (G := G) π D B hD
  have lifts (r : R) := exact_ambient_lift S H cco π ontoπ equivπ K hK D B hD r
  let g : R → OrbitalAut G A (id : A → A) := fun r => (lifts r).choose
  have gext (r : R) (x : r.part.domain) : (g r).val x.val.val = (r.part.map x).val :=
    (lifts r).choose_spec.1 x
  have gown (r : R) (x : A) (hx : π x ∈ B) :
      π ((g r).val x) = (r.owner.val ⟨π x,hx⟩).val := (lifts r).choose_spec.2 x hx
  obtain ⟨W,hW,hTW,hWB,ontoW,hw⟩ := finite_base_restriction
    (source_orbital_homogeneous S H) ep π equivπ T B hT hBfin hTB ontoT
    (fun r : R => r.owner) g gown
  refine ⟨W,hW,hDT.trans hTW,hWB,ontoW,?_⟩
  intro r
  obtain ⟨β,hβ,howner⟩ := hw r
  refine ⟨β,?_,howner⟩
  intro x
  exact (hβ ⟨x.val.val,hDT x.val.property⟩).trans (gext r x)

end CCO.Owners.Provider
