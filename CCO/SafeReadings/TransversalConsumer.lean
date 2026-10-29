import CCO.SafeReadings.Consumer
import CCO.SafeReadings.SourceSelectors
import CCO.SafeReadings.SourcePrimitive
import CCO.SafeReadings.TransversalSAP
import CCO.SafeReadings.TransversalCCO
import CCO.SafeReadings.TransversalEndpoint

/-! Final actual-source consumer. U, its typed source, primitivity, SAP,
CCO, triangle age, pure action and thin endpoint gauge are ALL constructed
from the accepted residual source. Only the safe system is GIVEN. -/
universe v w t z
namespace CCO.SafeReadings.TransversalConsumer
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open OwnerTransversal TransversalSource TransversalPure Selectors StrongExact StrongPC
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)

local instance : MulAction (Motion S H R B) (Σ b : ↥B, Carrier S H R B b) := canonicalSigmaAction S H R B

theorem actual_triangle_age : TriangleAge.{v,0,w,z} (source S H R B) :=
  fun _ D hComplete hTri => triangle_completion S H R B D hComplete hTri

/-- The augmented selector has NO NoReturn, CCO, primitive-sort, source
existence or endpoint provider input left to discharge. -/
theorem exists_safe_selector (Δ : Subgroup (Gamma S H R B))
    (safe : ∀ i j, (source S H R B).Menu i j) (hs : SafeSystem (source S H R B) safe)
    (hSafe : SafeInvariant (source S H R B) safe (subgroupAction S H R B hB Δ)) :
    ∃ h : SelectorOn (source S H R B) (augmentedFamily (source S H R B) safe),
      h.Covariant (subgroupAction S H R B hB Δ)
        (augmentedFamily_invariant (source S H R B) safe (subgroupAction S H R B hB Δ) hSafe) ∧
      ∀ {i j} (D : (source S H R B).Menu i j) (hD),
        (D ∩ safe i j).Nonempty → h.choose D hD ∈ safe i j := by
  letI : Fintype Δ := Fintype.ofFinite _
  let C := augmented_calculus (source S H R B) (canonical_homogeneous S H R B)
    (ageSAP S H R B) (semanticCCO S H R B) hs
  have hNoReturn := source_noReturn (source S H R B) (canonical_homogeneous S H R B)
    (ageSAP S H R B) (sortwise_primitive S H R B) (subgroupAction S H R B hB Δ)
    (subgroup_literalConverse S H R B hB Δ) C.nonempty
  exact exists_safe_covariant_selector (source S H R B) safe (canonical_homogeneous S H R B)
    (ageSAP S H R B) hs C (subgroupAction S H R B hB Δ) hSafe hNoReturn

/-- The SAME actual U supplies safe completion and all three independent
moving readings, with every old record and the literal small boundaries.
The chosen pure subgroup need only contain the actual thin owner action. -/
theorem safe_completion_and_readings
    (Δ : Subgroup (Gamma S H R B)) (hΔ : ∀ g, diagonal S H R B hB g ∈ Δ)
    (safe : ∀ i j, (source S H R B).Menu i j) (hs : SafeSystem (source S H R B) safe)
    (hSafe : SafeInvariant (source S H R B) safe (subgroupAction S H R B hB Δ))
    {V : Type z} (D : PartialDiagram (source S H R B) V) (hComp : D.HasStrongCompletion)
    (g k l : ResidualData.PacketGroup S H) {i j m : ↥B}
    (L : (source S H R B).Menu i j) (M : (source S H R B).Menu j m) (P : (source S H R B).Menu i m)
    (hL : Exact (source S H R B) L) (hM : Exact (source S H R B) M)
    (hP : Exact (source S H R B) P) (hPC : (source S H R B).PC L M P) :
    letI := thinCommGroup S H R
    ∃ h : SelectorOn (source S H R B) (augmentedFamily (source S H R B) safe),
      let E := subgroupEndpointGauge S H R B hB Δ hΔ
      let C := canonicalDiagram (source S H R B) (canonical_homogeneous S H R B)
        (ageSAP S H R B) (semanticCCO S H R B) D hComp h
      C.diagram.HasStrongCompletion ∧
      (∀ x y hxy a, D.edge x y hxy = some a → C.diagram.edge x y hxy = some a) ∧
      (∀ x y hxy, D.edge x y hxy = none →
        ∃ a ∈ safe (D.vertexSort x) (D.vertexSort y), C.diagram.edge x y hxy = some a) ∧
      (Nat.card V ≤ 2 → fixedNetwork D = initial D) ∧
      (source S H R B).Triangle (reading E (h.original _) g L hL)
        (reading E (h.original _) k M hM) (reading E (h.original _) l P hP) := by
  letI := thinCommGroup S H R
  obtain ⟨h,hCov,hSafe'⟩ := exists_safe_selector S H R B hB Δ safe hs hSafe
  exact ⟨h,completion_and_independent_readings (source S H R B) (canonical_homogeneous S H R B)
    (ageSAP S H R B) (semanticCCO S H R B) hs (actual_triangle_age S H R B)
    (subgroupAction S H R B hB Δ) _ h hCov hSafe' D hComp
    (subgroupEndpointGauge S H R B hB Δ hΔ) (subgroup_literalConverse S H R B hB Δ)
    g k l L M P hL hM hP hPC⟩

end
end CCO.SafeReadings.TransversalConsumer
