import CCO.RelativeMI.RecordedDecoder
import CCO.FullRows.ZeroRowRequests

/-! EVERY actual structural automorphism and EVERY legal correction
preserve the SAME fixed decoded fine colouring. -/
universe v w t y
namespace CCO.RelativeMI
noncomputable section
open AllThoseEPPA HKNReservoir ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
open SafeReadings Selectors FullRows
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))
variable (readingData : JointReading S H R B hB Δ)
variable (hΔ : ∀ g, TransversalPure.diagonal S H R B hB g ∈ Δ)
variable (A : Set (SourceCarrier S H R B))
variable (hA : (sourceStructure S H R B hB).IsClosed A)
variable {Z : Type y} [Finite Z]
variable (E : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) Z)
variable (hLocal : LocallyInSource (sourceTag S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) E)
variable (c : PacketCertificate S H R B hB Δ A hA E hLocal)
set_option quotPrecheck false
local notation "K" => ResidualData.PacketGroup S H
local notation "I" => PacketRecovery.PacketIndex E
local notation "J" => Packet I K
local notation "U₀" => TransversalSource.source S H R B
local notation "act" => sourceAction S H R B Δ

theorem decodedColour_lift (s₀ : Structure.Automorphism act E) (C : Matrix I K)
    (hC : Legal (recordedPairs S H R B hB Δ A hA E hLocal) C) (x y : Vertex I K) :
    letI := TransversalPure.thinCommGroup S H R
    decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c
      (lift (rowStructural S H R B hB Δ A hA E hLocal s₀) C x)
      (lift (rowStructural S H R B hB Δ A hA E hLocal s₀) C y) =
      decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c x y := by
  classical
  letI := TransversalPure.thinCommGroup S H R
  let Q := TransversalPure.subgroupEndpointGauge S H R B hB Δ hΔ
  let h := readingData.selector
  let P₀ := TransversalPure.subgroupAction S H R B hB Δ
  let s := rowStructural S H R B hB Δ A hA E hLocal s₀
  let α := rowVertexEquiv S H R B hB Δ A hA E hLocal s₀ C
  have hsquare (g : K) : g*g=1 := translation_square S (finitePacket S H) H (R.packet_thin S H) g
  change decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c (α x) (α y) = _
  by_cases hxy : x.1 = y.1
  · have hα : (α x).1 = (α y).1 := (same_packet_lift_iff s C x y).mpr hxy
    rw [decodedColour_internal S H R B hB Δ readingData hΔ A hA E hLocal c (α x) (α y) hα,
      decodedColour_internal S H R B hB Δ readingData hΔ A hA E hLocal c x y hxy]
    rcases x with ⟨p,g⟩
    rcases y with ⟨q,k⟩
    cases hxy
    change switchColour S (finitePacket S H) ((g*s.offset p.1)*(k*s.offset p.1)) none =
      switchColour S (finitePacket S H) (g*k) none
    have he : (g*s.offset p.1)*(k*s.offset p.1) = g*k := by
      calc
        _ = (g*k)*(s.offset p.1*s.offset p.1) := mul_mul_mul_comm _ _ _ _
        _ = _ := by rw [hsquare,mul_one]
    exact congrArg (fun a => switchColour S (finitePacket S H) a none) he
  · have hα := rowVertexEquiv_packet_ne S H R B hB Δ A hA E hLocal s₀ C x y hxy
    let D₀ : TaggedMenu U₀ := ⟨vertexOwner S H R B hB Δ A hA E hLocal x,
      vertexOwner S H R B hB Δ A hA E hLocal y,
      vertexDomain S H R B hB Δ hΔ A hA E hLocal x y hxy⟩
    let F₀ : TaggedMenu U₀ := ⟨vertexOwner S H R B hB Δ A hA E hLocal (α x),
      vertexOwner S H R B hB Δ A hA E hLocal (α y),
      vertexDomain S H R B hB Δ hΔ A hA E hLocal (α x) (α y) hα⟩
    have hD : IsExact U₀ D₀ := vertexDomain_exact S H R B hB Δ hΔ A hA E hLocal c x y hxy
    have hF : IsExact U₀ F₀ := vertexDomain_exact S H R B hB Δ hΔ A hA E hLocal c (α x) (α y) hα
    have hn : names U₀ P₀.label F₀ = names U₀ P₀.label D₀ :=
      vertexDomain_raw_covariant S H R B hB Δ hΔ A hA E hLocal s₀ C x y hxy
    have hv : readingName Q h (parameter (α x) (α y)) F₀ hF = readingName Q h (parameter x y) D₀ hD := by
      by_cases hr : recordedPairs S H R B hB Δ A hA E hLocal x.1.1 y.1.1
      · obtain ⟨a,ha⟩ := hr
        obtain ⟨b,hb⟩ := recorded_vertexDomain_singleton S H R B hB Δ hΔ A hA E hLocal c x y hxy a ha
        have hsingle : names U₀ P₀.label D₀ = {some b.val} := by
          change (fun a => some a.val) '' vertexDomain S H R B hB Δ hΔ A hA E hLocal x y hxy = _
          rw [hb]
          exact Set.image_singleton
        exact (readingName_singleton Q h _ F₀ hF _ (hn.trans hsingle)).trans
          (readingName_singleton Q h _ D₀ hD _ hsingle).symm
      · have hp : parameter (α x) (α y) = parameter x y := by
          by_cases hi : x.1.1 = y.1.1
          · exact parameter_lift_same_index hsquare s C x y hi
          · exact parameter_lift_unrecorded hsquare s _ C hC x y hi hr
        have hc := readingName_covariant_of_names Q h
          (readingData.covariant) s₀.lang (parameter x y)
          D₀ F₀ hD hF
          (rowVertexEquiv_owner S H R B hB Δ A hA E hLocal s₀ C x)
          (rowVertexEquiv_owner S H R B hB Δ A hA E hLocal s₀ C y) hn
        exact (congrArg (fun g => readingName Q h g F₀ hF) hp).trans hc
    rw [decodedColour_eq_reading S H R B hB Δ readingData hΔ A hA E hLocal c (α x) (α y) hα,
      decodedColour_eq_reading S H R B hB Δ readingData hΔ A hA E hLocal c x y hxy]
    exact hv
end
end CCO.RelativeMI
