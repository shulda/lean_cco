import CCO.SafeReadings.TransversalEndpoint
import CCO.SafeReadings.TransversalSAP
import CCO.SafeReadings.TransversalCCO
import CCO.SafeReadings.SourcePrimitive
import CCO.SafeReadings.SourceSelectors

/-! The actual owner-transversal specialization: all selector, source,
primitivity and endpoint providers are discharged. Only the legitimate
residual-source standing assumptions and the chosen pure subgroup remain. -/
universe v w t
namespace CCO.SafeReadings.TransversalPure
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open OwnerTransversal TransversalAge TransversalSource Selectors
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (Gamma S H R B))

/-- ONE actual joint hereditary selector for the entire chosen pure owner group. -/
theorem exists_joint_selector :
    ∃ h : HereditarySelector (source S H R B), h.Covariant (source S H R B) (subgroupAction S H R B hB Δ) := by
  letI := canonicalSigmaAction S H R B
  letI : Fintype Δ := Fintype.ofFinite _
  exact exists_original_covariant_selector (source S H R B) (canonical_homogeneous S H R B)
    (ageSAP S H R B) (semanticCCO S H R B) (sortwise_primitive S H R B)
    (subgroupAction S H R B hB Δ) (subgroup_literalConverse S H R B hB Δ)

def jointSelector : HereditarySelector (source S H R B) :=
  (exists_joint_selector S H R B hB Δ).choose

theorem jointSelector_covariant :
    (jointSelector S H R B hB Δ).Covariant (source S H R B) (subgroupAction S H R B hB Δ) :=
  (exists_joint_selector S H R B hB Δ).choose_spec

variable (hΔ : ∀ g, diagonal S H R B hB g ∈ Δ)

/-- An actual moved-first-type reading, selected by the constructed joint h. -/
def actualReading (g : ResidualData.PacketGroup S H) {i j : ↥B}
    (D : (source S H R B).Menu i j) (hD : StrongExact.Exact (source S H R B) D) :
    (source S H R B).Atom i j := by
  letI := thinCommGroup S H R
  exact reading (subgroupEndpointGauge S H R B hB Δ hΔ) (jointSelector S H R B hB Δ) g D hD

theorem actualReading_member (g : ResidualData.PacketGroup S H) {i j : ↥B}
    (D : (source S H R B).Menu i j) (hD : StrongExact.Exact (source S H R B) D) :
    actualReading S H R B hB Δ hΔ g D hD ∈ D := by
  letI := thinCommGroup S H R
  exact reading_member (subgroupEndpointGauge S H R B hB Δ hΔ) (jointSelector S H R B hB Δ) g D hD

theorem actualReading_heredity (g : ResidualData.PacketGroup S H) {i j : ↥B}
    (D F : (source S H R B).Menu i j) (hD : StrongExact.Exact (source S H R B) D)
    (hF : StrongExact.Exact (source S H R B) F) (hFD : F ⊆ D)
    (hs : actualReading S H R B hB Δ hΔ g D hD ∈ F) :
    actualReading S H R B hB Δ hΔ g F hF = actualReading S H R B hB Δ hΔ g D hD := by
  letI := thinCommGroup S H R
  exact reading_heredity (subgroupEndpointGauge S H R B hB Δ hΔ) (jointSelector S H R B hB Δ) g D F hD hF hFD hs

theorem actualReading_converse (g : ResidualData.PacketGroup S H) {i j : ↥B}
    (D : (source S H R B).Menu i j) (hD : StrongExact.Exact (source S H R B) D)
    (hO : StrongExact.Exact (source S H R B) ((source S H R B).opposite D)) :
    actualReading S H R B hB Δ hΔ g ((source S H R B).opposite D) hO =
      (source S H R B).conv (actualReading S H R B hB Δ hΔ g D hD) := by
  letI := thinCommGroup S H R
  exact reading_converse (subgroupEndpointGauge S H R B hB Δ hΔ) (jointSelector S H R B hB Δ)
    (jointSelector_covariant S H R B hB Δ) (subgroup_literalConverse S H R B hB Δ) g D hD hO

theorem actualReading_covariant (γ : Δ) (g : ResidualData.PacketGroup S H)
    (D : TaggedMenu (source S H R B)) (hD : IsExact (source S H R B) D) :
    (actualReading S H R B hB Δ hΔ g ((subgroupAction S H R B hB Δ).act γ D).2.2
      (((subgroupAction S H R B hB Δ).exact γ D).mpr hD)).val =
      (actualReading S H R B hB Δ hΔ g D.2.2 hD).val := by
  letI := thinCommGroup S H R
  apply Option.some.inj
  exact reading_covariant (subgroupEndpointGauge S H R B hB Δ hΔ) (jointSelector S H R B hB Δ)
    (jointSelector_covariant S H R B hB Δ) γ g D hD

/-- The source specialization keeps the moved first type in the switch law. -/
theorem actualReading_switch (u v : ResidualData.PacketGroup S H) {i j : ↥B}
    (D : (source S H R B).Menu i j) (hD : StrongExact.Exact (source S H R B) D) :
    letI := thinCommGroup S H R
    let E := subgroupEndpointGauge S H R B hB Δ hΔ
    actualReading S H R B hB Δ hΔ (u*v) (E.leftMenu v D) (E.left_exact v hD) =
      E.left v (actualReading S H R B hB Δ hΔ u D hD) := by
  letI := thinCommGroup S H R
  exact reading_switch (subgroupEndpointGauge S H R B hB Δ hΔ) (jointSelector S H R B hB Δ) u v D hD

/-- C40: the actual source supports EVERY original PC triple and ALL
independent g,k,l, including repeated owner labels or repeated menus. -/
theorem actualReading_triangle (g k l : ResidualData.PacketGroup S H) {i j m : ↥B}
    (D : (source S H R B).Menu i j) (F : (source S H R B).Menu j m) (P : (source S H R B).Menu i m)
    (hD : StrongExact.Exact (source S H R B) D) (hF : StrongExact.Exact (source S H R B) F)
    (hP : StrongExact.Exact (source S H R B) P) (hpc : (source S H R B).PC D F P) :
    (source S H R B).Triangle (actualReading S H R B hB Δ hΔ g D hD)
      (actualReading S H R B hB Δ hΔ k F hF) (actualReading S H R B hB Δ hΔ l P hP) := by
  letI := thinCommGroup S H R
  letI := canonicalSigmaAction S H R B
  exact rectangular_reading_triangle (subgroupEndpointGauge S H R B hB Δ hΔ)
    (jointSelector S H R B hB Δ) (jointSelector_covariant S H R B hB Δ)
    (subgroup_literalConverse S H R B hB Δ)
    (exactCalculus_of_SAP_CCO (source S H R B) (canonical_homogeneous S H R B)
      (ageSAP S H R B) (semanticCCO S H R B))
    ((source S H R B).realPointGluing_of_SAP (canonical_homogeneous S H R B) (ageSAP S H R B))
    ((source S H R B).realEdgeGluing_of_SAP (canonical_homogeneous S H R B) (ageSAP S H R B))
    g k l D F P hD hF hP hpc

end
end CCO.SafeReadings.TransversalPure
