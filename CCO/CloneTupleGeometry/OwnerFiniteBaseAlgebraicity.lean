import CCO.CloneTupleGeometry.OwnerFiniteBasePhase

/-! Actual stabilizer-orbit algebraicity over arbitrary finite marked owner
bases. Whole finite homogeneity identifies complete named types with the
actual pointwise-base orbits; the genuine character step preserves their
finiteness in both directions. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w t
namespace CCO.CloneTupleGeometry
open APCharacter APCharacter.SourceAge RigidGroupoid.Geometry TerminalPowers
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- The true orbit under the pointwise stabilizer of the entire displayed
finite actual base; there is no assumption of a one-sort reduct action. -/
def ownerOrbitOver {m : ℕ} (base : Fin m → Sigma X) {i : ι} (x : X i) : Set (X i) :=
  {y | ∃ g : G, (∀ a, g • base a = base a) ∧ g • x = y}

/-- Complete old named types are exactly the actual ambient stabilizer
orbits. Both directions use the SAME whole-source action. -/
theorem ownerTypeOver_eq_orbit (H : HomogeneousSource S G)
    {m : ℕ} (base : Fin m → Sigma X) {i : ι} (x : X i) :
    ownerTypeOver S base x = ownerOrbitOver (G := G) base x := by
  ext y
  constructor
  · intro hy
    let source : ULift.{max u v} (Fin m) ⊕ ULift.{max u v} Unit → Sigma X :=
      Sum.elim (fun a => base a.down) (fun _ => ⟨i,x⟩)
    let target : ULift.{max u v} (Fin m) ⊕ ULift.{max u v} Unit → Sigma X :=
      Sum.elim (fun a => base a.down) (fun _ => ⟨i,y⟩)
    have hc : ∀ a b, taggedColour S (source a) (source b) =
        taggedColour S (target a) (target b) := by
      intro a b
      cases a with
      | inl a =>
        cases b with
        | inl b => rfl
        | inr b => exact (hy a.down).symm
      | inr a =>
        cases b with
        | inl b =>
          exact RawExact.taggedColour_reverse_eq_of_eq S _ _ _ _ (hy b.down).symm
        | inr b =>
          apply congrArg (fun z => (⟨i,i,z⟩ : Age.Colour S))
          exact ((S.colour_none_iff x x).mpr rfl).trans
            ((S.colour_none_iff y y).mpr rfl).symm
    obtain ⟨g,hg⟩ := H.extends_finite_diagram source target hc
    refine ⟨g,(fun a => hg (Sum.inl ⟨a⟩)),?_⟩
    have hh : (⟨i,g • x⟩ : Sigma X) = ⟨i,y⟩ := hg (Sum.inr ⟨()⟩)
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hh
  · rintro ⟨g,hg,hx⟩ a
    have hh := H.preserves_colours g (base a) (⟨i,x⟩ : Sigma X)
    change taggedColour S (g • base a) ⟨i,g • x⟩ = _ at hh
    rw [hg a,hx] at hh
    exact hh

section OneSort
variable {M : Type v} {K : Type t} [Group K] [MulAction K M]
variable (S₀ : AtomicSource.{0,v,w} Unit (fun _ => M)) (H₀ : HomogeneousSource S₀ K)

include H₀ in
/-- Finset readout for ANY actual homogeneous one-sort action. A finite
base enumeration need not be injective here: precisely its range matters.
This permits the original packet-closure action without a group isomorphism. -/
theorem ownerTypeOver_finset_orbit_eq {m : ℕ} (base : Fin m → M)
    (A : Finset M) (covers : ∀ z, z ∈ A ↔ ∃ j, base j = z) (x : M) :
    ownerTypeOver S₀ (fun j => (⟨(),base j⟩ : Sigma (fun _ : Unit => M))) (i := ()) x =
      {y | ∃ g : K, (∀ a ∈ A, g • a = a) ∧ g • x = y} := by
  rw [ownerTypeOver_eq_orbit S₀ H₀]
  ext y
  constructor
  · rintro ⟨g,hg,hx⟩
    refine ⟨g,?_,hx⟩
    intro a ha
    obtain ⟨j,rfl⟩ := (covers a).mp ha
    have hh : (⟨(),g • base j⟩ : Sigma (fun _ : Unit => M)) = ⟨(),base j⟩ := hg j
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hh
  · rintro ⟨g,hg,hx⟩
    refine ⟨g,?_,hx⟩
    intro j
    exact congrArg (Sigma.mk ()) (hg (base j) ((covers (base j)).mpr ⟨j,rfl⟩))

end OneSort

variable (H : HomogeneousSource S G) (ap : AgeAP S)
variable (C : ExactCalculus (CloneSAP.source S))
variable {r : ι} {A : Kernel (CloneSAP.source S) r}
variable (P : SourcePhase (CloneSAP.source S) (CloneSAP.homogeneous S H) C A)
variable (cco : SemanticCCO.{u,v,max u v,w} S)
variable (I : CloneMarkedIdentification S H C P cco)

/-- A child full type injects into the corresponding parent full type by
the literal owner projection. Thus finite parent types stay finite. -/
theorem finite_owner_parent_type_child {m : ℕ}
    (base : Fin m ↪ Sigma (OwnerChild S H C P cco I))
    {c : Rank.Child (UnarySource.β
      (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I)}
    (x : OwnerChild S H C P cco I c)
    (hparent : (ownerTypeOver S
      ((ownerProjection S H ap C P cco I).project ∘ base) x.val).Finite) :
    (ownerTypeOver (owner_child_source S H ap C P cco I) base x).Finite := by
  let parent := ownerTypeOver S ((ownerProjection S H ap C P cco I).project ∘ base) x.val
  let child := ownerTypeOver (owner_child_source S H ap C P cco I) base x
  let f : child → parent := fun y => ⟨y.val.val,fun a =>
    owner_project_tagged S H ap C P cco I (y.property a)⟩
  have hf : Function.Injective f := by
    intro y z he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun p : parent => p.val) he
  letI : Finite parent := hparent.to_subtype
  letI : Finite child := Finite.of_injective f hf
  exact Set.finite_coe_iff.mp (inferInstance : Finite child)

/-- Finiteness of the COMPLETE child type is equivalent to finiteness of
its parent type. The reverse implication uses the actual anchored global
character seed, marked embedding and full-base alignment proved above. -/
theorem owner_child_type_finite_iff {m : ℕ}
    (base : Fin m ↪ Sigma (OwnerChild S H C P cco I))
    {c : Rank.Child (UnarySource.β
      (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I)}
    (x : OwnerChild S H C P cco I c) :
    (ownerTypeOver (owner_child_source S H ap C P cco I) base x).Finite ↔
      (ownerTypeOver S ((ownerProjection S H ap C P cco I).project ∘ base) x.val).Finite := by
  constructor
  · intro hc
    by_contra hp
    exact owner_child_type_infinite S H ap C P cco I base x hp hc
  · exact finite_owner_parent_type_child S H ap C P cco I base x

/-- N09 actual source conclusion for EVERY finite base, with no extra
source/provider hypothesis. Algebraicity is finite true pointwise-base
orbit in the whole original and whole marked owner sources respectively. -/
theorem actual_owner_phase_algebraicity_iff {m : ℕ}
    (base : Fin m ↪ Sigma (OwnerChild S H C P cco I))
    {c : Rank.Child (UnarySource.β
      (completion := P.completion_property (CloneSAP.CCO.cco_forward S cco)) I)}
    (x : OwnerChild S H C P cco I c) :
    (ownerOrbitOver (G := FullAut (owner_child_source S H ap C P cco I)) base x).Finite ↔
      (ownerOrbitOver (G := FullAut S)
        ((ownerProjection S H ap C P cco I).project ∘ base) x.val).Finite := by
  rw [← ownerTypeOver_eq_orbit (owner_child_source S H ap C P cco I)
    (actual_marked_owner_homogeneous S H ap C P cco I) base x,
    ← ownerTypeOver_eq_orbit S (full_homogeneous S H)
      ((ownerProjection S H ap C P cco I).project ∘ base) x.val]
  exact owner_child_type_finite_iff S H ap C P cco I base x

end
end CCO.CloneTupleGeometry
