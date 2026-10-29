import CCO.SafeReadings.TransversalEndpoint
import CCO.SafeReadings.TransversalSAP
import CCO.SafeReadings.TransversalCCO
import CCO.SafeReadings.SourcePrimitive
import CCO.SafeReadings.Consumer
import CCO.FullRows.VertexDomains

/-! Local parametric extraction of moved-type readings. The entire proof
works for the SUPPLIED joint selector, including a safe selector distinct
from the ordinary accepted choice. Three parameters remain independent. -/
universe v w t
namespace CCO.RelativeMI
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open OwnerTransversal TransversalAge Selectors SafeReadings HKNReservoir
open SafeReadings.TransversalSource SafeReadings.TransversalPure
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (Gamma S H R B))

/-- The supplied joint selector is an explicit parameter. In particular it
may be the augmented safe selector restricted to original exact menus. -/
structure JointReading where
  selector : HereditarySelector (source S H R B)
  covariant : selector.Covariant (source S H R B) (subgroupAction S H R B hB Δ)

variable (q : JointReading S H R B hB Δ)

variable (hΔ : ∀ g, diagonal S H R B hB g ∈ Δ)

/-- An actual moved-first-type reading, selected by the constructed joint h. -/
def parametricReading (g : ResidualData.PacketGroup S H) {i j : ↥B}
    (D : (source S H R B).Menu i j) (hD : StrongExact.Exact (source S H R B) D) :
    (source S H R B).Atom i j := by
  letI := thinCommGroup S H R
  exact reading (subgroupEndpointGauge S H R B hB Δ hΔ) q.selector g D hD

theorem parametricReading_member (g : ResidualData.PacketGroup S H) {i j : ↥B}
    (D : (source S H R B).Menu i j) (hD : StrongExact.Exact (source S H R B) D) :
    parametricReading S H R B hB Δ q hΔ g D hD ∈ D := by
  letI := thinCommGroup S H R
  exact reading_member (subgroupEndpointGauge S H R B hB Δ hΔ) q.selector g D hD

theorem parametricReading_heredity (g : ResidualData.PacketGroup S H) {i j : ↥B}
    (D F : (source S H R B).Menu i j) (hD : StrongExact.Exact (source S H R B) D)
    (hF : StrongExact.Exact (source S H R B) F) (hFD : F ⊆ D)
    (hs : parametricReading S H R B hB Δ q hΔ g D hD ∈ F) :
    parametricReading S H R B hB Δ q hΔ g F hF = parametricReading S H R B hB Δ q hΔ g D hD := by
  letI := thinCommGroup S H R
  exact reading_heredity (subgroupEndpointGauge S H R B hB Δ hΔ) q.selector g D F hD hF hFD hs

theorem parametricReading_converse (g : ResidualData.PacketGroup S H) {i j : ↥B}
    (D : (source S H R B).Menu i j) (hD : StrongExact.Exact (source S H R B) D)
    (hO : StrongExact.Exact (source S H R B) ((source S H R B).opposite D)) :
    parametricReading S H R B hB Δ q hΔ g ((source S H R B).opposite D) hO =
      (source S H R B).conv (parametricReading S H R B hB Δ q hΔ g D hD) := by
  letI := thinCommGroup S H R
  exact reading_converse (subgroupEndpointGauge S H R B hB Δ hΔ) q.selector
    q.covariant (subgroup_literalConverse S H R B hB Δ) g D hD hO

theorem parametricReading_covariant (γ : Δ) (g : ResidualData.PacketGroup S H)
    (D : TaggedMenu (source S H R B)) (hD : IsExact (source S H R B) D) :
    (parametricReading S H R B hB Δ q hΔ g ((subgroupAction S H R B hB Δ).act γ D).2.2
      (((subgroupAction S H R B hB Δ).exact γ D).mpr hD)).val =
      (parametricReading S H R B hB Δ q hΔ g D.2.2 hD).val := by
  letI := thinCommGroup S H R
  apply Option.some.inj
  exact reading_covariant (subgroupEndpointGauge S H R B hB Δ hΔ) q.selector
    q.covariant γ g D hD

/-- The source specialization keeps the moved first type in the switch law. -/
theorem parametricReading_switch (u v : ResidualData.PacketGroup S H) {i j : ↥B}
    (D : (source S H R B).Menu i j) (hD : StrongExact.Exact (source S H R B) D) :
    letI := thinCommGroup S H R
    let E := subgroupEndpointGauge S H R B hB Δ hΔ
    parametricReading S H R B hB Δ q hΔ (u*v) (E.leftMenu v D) (E.left_exact v hD) =
      E.left v (parametricReading S H R B hB Δ q hΔ u D hD) := by
  letI := thinCommGroup S H R
  exact reading_switch (subgroupEndpointGauge S H R B hB Δ hΔ) q.selector u v D hD

/-- C11: two independent readings have support in the supplied third
menu. The exact refinement and the joint selector are both explicit. -/
theorem parametricReading_bilateral (g k : ResidualData.PacketGroup S H) {i j m : ↥B}
    (D : (source S H R B).Menu i j) (F : (source S H R B).Menu j m) (P : (source S H R B).Menu i m)
    (hD : StrongExact.Exact (source S H R B) D) (hF : StrongExact.Exact (source S H R B) F)
    (hP : StrongExact.Exact (source S H R B) P)
    (hDF : D ⊆ (source S H R B).product P ((source S H R B).opposite F))
    (hFD : F ⊆ (source S H R B).product ((source S H R B).opposite D) P) :
    ∃ c ∈ P, (source S H R B).Triangle
      (parametricReading S H R B hB Δ q hΔ g D hD)
      (parametricReading S H R B hB Δ q hΔ k F hF) c := by
  letI := thinCommGroup S H R
  letI := canonicalSigmaAction S H R B
  exact reading_bilateral (subgroupEndpointGauge S H R B hB Δ hΔ) q.selector q.covariant
    (exactCalculus_of_SAP_CCO (source S H R B) (canonical_homogeneous S H R B)
      (ageSAP S H R B) (semanticCCO S H R B))
    ((source S H R B).realPointGluing_of_SAP (canonical_homogeneous S H R B) (ageSAP S H R B))
    ((source S H R B).realEdgeGluing_of_SAP (canonical_homogeneous S H R B) (ageSAP S H R B))
    g k D F P hD hF hP hDF hFD

/-- C12: the supplied joint selector supports EVERY original PC triple and ALL
independent g,k,l, including repeated owner labels or repeated menus. -/
theorem parametricReading_triangle (g k l : ResidualData.PacketGroup S H) {i j m : ↥B}
    (D : (source S H R B).Menu i j) (F : (source S H R B).Menu j m) (P : (source S H R B).Menu i m)
    (hD : StrongExact.Exact (source S H R B) D) (hF : StrongExact.Exact (source S H R B) F)
    (hP : StrongExact.Exact (source S H R B) P) (hpc : (source S H R B).PC D F P) :
    (source S H R B).Triangle (parametricReading S H R B hB Δ q hΔ g D hD)
      (parametricReading S H R B hB Δ q hΔ k F hF) (parametricReading S H R B hB Δ q hΔ l P hP) := by
  letI := thinCommGroup S H R
  letI := canonicalSigmaAction S H R B
  exact rectangular_reading_triangle (subgroupEndpointGauge S H R B hB Δ hΔ)
    q.selector q.covariant
    (subgroup_literalConverse S H R B hB Δ)
    (exactCalculus_of_SAP_CCO (source S H R B) (canonical_homogeneous S H R B)
      (ageSAP S H R B) (semanticCCO S H R B))
    ((source S H R B).realPointGluing_of_SAP (canonical_homogeneous S H R B) (ageSAP S H R B))
    ((source S H R B).realEdgeGluing_of_SAP (canonical_homogeneous S H R B) (ageSAP S H R B))
    g k l D F P hD hF hP hpc

end
end CCO.RelativeMI
