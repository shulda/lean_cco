import CCO.Owners.Provider.ExactFiniteBase
import CCO.Owners.Provider.RequestInclusion
import CCO.Owners.Provider.Trim
import CCO.Owners.Provider.PointTransfer

/-! The actual finite full-packet owner provider, conditional only on
ordinary EPPA of the CURRENT source. All exact ambient lifts, packet
projection, finite request enumeration and orbit trimming are discharged. -/
universe v w t
namespace CCO.Owners.Provider
open Product RawExact
variable {A O : Type v} {G : Type t} [Group G] [MulAction G A] [MulAction G O]

theorem actual_owner_provider [Countable A]
    (S : AtomicSource.{0,v,w} Unit (fun _ => A))
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
    (ep : OrdinaryEPPA G A)
    (π : A → O) (ontoπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (K : NonemptyExact S () ()) (hK : GroupActions.kernel π = evaluate S K.words)
    (B : Set O) (hB : B.Finite) (nonemptyB : B.Nonempty)
    (closedB : ∀ u ∈ B, ∀ v, ownerPacket S H π ontoπ equivπ u v → v ∈ B)
    (T : Set A) (hT : T.Finite) (overT : ∀ x : T, π x.val ∈ B) :
    ∃ D : Set A, D.Finite ∧ ∃ inc : T ⊆ D,
      FullPacketClosed S H D ∧ ∃ overD : ∀ x : D, π x.val ∈ B,
      ∃ ontoD : Function.Surjective (ownerProjection π D B overD),
      (∀ r : OwnerRequest (G := G) π T B overT,
        ∃ β : OrbitalAut G A (Subtype.val : D → A),
          (∀ x : r.part.domain,
            (β.val ⟨x.val.val,inc x.val.property⟩).val = (r.part.map x).val) ∧
          (inducedQuotient π equivπ D B overD ontoD).action β = r.owner) ∧
      GroupActions.PrescribedLift
        (inducedQuotient π equivπ D B overD ontoD).action (ownerProjection π D B overD) ∧
      Function.Surjective (inducedQuotient π equivπ D B overD ontoD).action ∧
      GroupActions.FibreTransitive
        (inducedQuotient π equivπ D B overD ontoD).action (ownerProjection π D B overD) := by
  classical
  obtain ⟨U,hU,incT,nonemptyU,closedU,overU,ontoU⟩ :=
    packet_seed S H π ontoπ equivπ B hB nonemptyB closedB T hT
      (fun x hx => overT ⟨x,hx⟩)
  letI : Finite U := hU.to_subtype
  letI : Finite B := hB.to_subtype
  let R := OwnerRequest (G := G) π U B overU
  obtain ⟨D₀,hD₀,incU₀,over₀,onto₀,all₀⟩ :=
    exact_fixed_base S H cco ep π ontoπ equivπ K hK U B hU hB overU
  let β : R → OrbitalAut G A (Subtype.val : D₀ → A) := fun r => (all₀ r).choose
  have βext (r : R) (x : r.part.domain) :
      ((β r).val ⟨x.val.val,incU₀ x.val.property⟩).val = (r.part.map x).val :=
    (all₀ r).choose_spec.1 x
  have βowner (r : R) (x : D₀) :
      π ((β r).val x).val = (r.owner.val (ownerProjection π D₀ B over₀ x)).val :=
    (all₀ r).choose_spec.2 x
  obtain ⟨D₁,hD₁,inc₀₁,closed₁,over₁,onto₁,α,αext,αowner⟩ :=
    packet_enlargement S H π ontoπ equivπ B closedB D₀ hD₀ over₀ onto₀
      β (fun r : R => r.owner) βowner
  obtain ⟨D,hD,incUD,inside,closedD,θ,θeq,cover⟩ :=
    trim_selected_actions S H D₁ U hD₁ closed₁ (incU₀.trans inc₀₁) closedU α
  have incTD : T ⊆ D := incT.trans incUD
  have overD : ∀ x : D, π x.val ∈ B := fun x => over₁ ⟨x.val,inside x.property⟩
  have ontoD : Function.Surjective (ownerProjection π D B overD) := by
    intro b
    obtain ⟨a,ha⟩ := ontoU b
    exact ⟨⟨a.val,incUD a.property⟩,ha⟩
  let Q := inducedQuotient π equivπ D B overD ontoD
  have θext (r : R) (x : r.part.domain) :
      ((θ r).val ⟨x.val.val,incUD x.val.property⟩).val = (r.part.map x).val := by
    rw [θeq r ⟨x.val.val,incUD x.val.property⟩]
    exact (αext r ⟨x.val.val,incU₀ x.val.property⟩).trans (βext r x)
  have θowner (r : R) : Q.action (θ r) = r.owner := by
    apply induced_owner_unique π equivπ D B overD ontoD (θ r) r.owner
    intro x
    apply Subtype.ext
    exact (αowner r ⟨x.val,inside x.property⟩).symm.trans
      (congrArg π (θeq r x)).symm
  let seed : Set D := {x | x.val ∈ U}
  have coverSeed : ∀ x : D, ∃ g : OrbitalAut G A (Subtype.val : D → A), g • x ∈ seed := by
    intro x
    exact cover x
  have seedLift : ∀ a ∈ seed, ∀ a' ∈ seed,
      ∀ γ : OrbitalAut G O (Subtype.val : B → O),
      γ • Q.projection a = Q.projection a' →
      ∃ k : OrbitalAut G A (Subtype.val : D → A), Q.action k = γ ∧ k • a = a' := by
    intro a ha a' ha' γ hγ
    let aU : U := ⟨a.val,ha⟩
    let aU' : U := ⟨a'.val,ha'⟩
    have hγU : γ.val (ownerProjection π U B overU aU) = ownerProjection π U B overU aU' := hγ
    let r : R := singletonRequest (S.original_sort_transitive_of_homogeneous H ())
      π U B overU aU aU' γ hγU
    refine ⟨θ r,θowner r,?_⟩
    apply Subtype.ext
    exact θext r ⟨aU,Set.mem_singleton aU⟩
  have points : GroupActions.PrescribedLift Q.action Q.projection :=
    prescribedLift_of_seed Q.action Q.projection
      (fun g x => (Q.action_projection g x).symm) seed coverSeed seedLift
  letI : Nonempty D := by
    obtain ⟨a,ha⟩ := nonemptyU
    exact ⟨⟨a,incUD ha⟩⟩
  have kernel := (GroupActions.prescribed_action_point_lifting Q.action Q.projection ontoD
    (fun g x => (Q.action_projection g x).symm)).mpr points
  refine ⟨D,hD,incTD,closedD,overD,ontoD,?_,points,kernel.1,kernel.2⟩
  intro r
  let s : R := r.enlarge incT overU
  refine ⟨θ s,?_,θowner s⟩
  intro x
  have hx := θext s (r.enlargeDomain incT overU x)
  exact hx.trans (r.enlarge_map incT overU x)

end CCO.Owners.Provider
