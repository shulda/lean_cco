import CCO.RelativeMI.ParametricReadings
import CCO.RelativeMI.OrbitSafe

/-! Construct the safe selector ONCE, then restrict that very selector to
original exact menus. It is never identified with the ordinary selector.
Every independent moved reading of a surviving safe trace remains safe. -/
universe v w t
namespace CCO.RelativeMI
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open OwnerTransversal TransversalAge Selectors SafeReadings HKNReservoir
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))
local notation "T" => TransversalSource.source S H R B
local notation "K" => ResidualData.PacketGroup S H

def JointReading.SafeOn (q : JointReading S H R B hB Δ)
    (safe : ∀ i j, (T).Menu i j) : Prop :=
  ∀ {i j} (D : (T).Menu i j) (hD : StrongExact.Exact T D),
    (D ∩ safe i j).Nonempty → q.selector.choose D hD ∈ safe i j

/-- All augmented gate/source obligations are discharged by the actual
accepted transversal. Only its derived safe system remains to instantiate. -/
theorem exists_safe_jointReading (safe : ∀ i j, (T).Menu i j)
    (hs : SafeSystem T safe)
    (hSafe : SafeInvariant T safe (TransversalPure.subgroupAction S H R B hB Δ)) :
    ∃ q : JointReading S H R B hB Δ, q.SafeOn S H R B hB Δ safe := by
  obtain ⟨h,hCov,hSelect⟩ := TransversalConsumer.exists_safe_selector S H R B hB Δ safe hs hSafe
  refine ⟨⟨h.original T,h.original_covariant T _ _ hCov⟩,?_⟩
  intro i j D hD hmeet
  exact hSelect D (Or.inl hD) hmeet

theorem exists_orbitSafe_jointReading (safe : Set (S.Atom () ()))
    (hs : SafeSystem T (orbitSafe S H R B hB safe)) :
    ∃ q : JointReading S H R B hB Δ,
      q.SafeOn S H R B hB Δ (orbitSafe S H R B hB safe) :=
  exists_safe_jointReading S H R B hB Δ _ hs (orbitSafe_invariant S H R B hB safe Δ)

/-- All u are allowed, at the separately moved endpoint types. -/
theorem parametricReading_orbitSafe (q : JointReading S H R B hB Δ)
    (hΔ : ∀ g, TransversalPure.diagonal S H R B hB g ∈ Δ)
    (safe : Set (S.Atom () ()))
    (hq : q.SafeOn S H R B hB Δ (orbitSafe S H R B hB safe))
    (u : K) {i j : ↥B} (D : (T).Menu i j) (hD : StrongExact.Exact T D)
    (hmeet : (D ∩ orbitSafe S H R B hB safe i j).Nonempty) :
    parametricReading S H R B hB Δ q hΔ u D hD ∈ orbitSafe S H R B hB safe i j := by
  letI := TransversalPure.thinCommGroup S H R
  let Q := TransversalPure.subgroupEndpointGauge S H R B hB Δ hΔ
  have hm : (Q.leftMenu u D ∩
      orbitSafe S H R B hB safe (Q.owner u i) j).Nonempty := by
    obtain ⟨a,ha,hs⟩ := hmeet
    refine ⟨Q.left u a,⟨a,ha,rfl⟩,?_⟩
    exact (orbitSafe_left_iff S H R B hB safe u a).mpr hs
  have hc := hq (Q.leftMenu u D) (Q.left_exact u hD) hm
  have hi := (orbitSafe_left_image S H R B hB safe u i j).symm ▸ hc
  obtain ⟨a,ha,he⟩ := hi
  have hr : reading Q q.selector u D hD = a := by
    apply (Q.left u).injective
    exact (left_reading Q q.selector u D hD).trans he.symm
  change reading Q q.selector u D hD ∈ _
  exact hr.symm ▸ ha

end
end CCO.RelativeMI
