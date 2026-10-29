import CCO.HKNReservoir.Reservoir
import CCO.HKNReservoir.ShortCycle
import CCO.HKNReservoir.ActualPacketCompletion
import CCO.HKNReservoir.FinalAlignment
import CCO.HKNReservoir.CertificateCompletion

/-! Actual end-to-end consumer. Both external providers, normalization,
closed-SAP tree realization, vertex-counted chord-complete short cycles,
long-cycle locality, WHOLE-diagram typed CCO and collision repair are
all discharged here; none is an opaque provider input to the conclusion. -/
universe v w t
namespace CCO.HKNReservoir
noncomputable section
open AllThoseEPPA ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))
variable (A : Set (SourceCarrier S H R B))
variable (hA : (sourceStructure S H R B hB).IsClosed A)

/-- The required number of CLOSED vertices, including all translations
in every packet of a short origin cycle. -/
def reservoirThreshold : Nat := packetThreshold S H
  (Locality.cycleBound (SafeReadings.TransversalSource.source S H R B))

/-- The finite actual structural reservoir with a separate injective
complete certificate, fixing its literal old source, and retaining ALL
original compatible partial-map components, including empty domains. -/
theorem completable_reservoir [Finite A] (hne : A.Nonempty) :
    Nonempty (CompletableReservoir S H R B hB Δ A hA (reservoirThreshold S H R B)) := by
  classical
  let b := Locality.cycleBound (SafeReadings.TransversalSource.source S H R B)
  have hb : 3 ≤ b := Nat.le_max_left _ _
  obtain ⟨_,_,⟨W⟩⟩ := actual_staged_witness S H R B hB Δ A hA b hb
  letI := W.finiteNew
  let hLocal := locallyInSource_of_faithful (sourceTag S H R B Δ) W.inclusion W.faithful
  have hshort : ∀ C : SimpleCycle (sourceOriginDiagram S H R B hB Δ A hA W.model hLocal),
      C.length ≤ b → CycleHom C :=
    fun C hC => short_origin_cycle S H R B hB Δ A hA W.model hLocal b W.localTrees C hC
  obtain ⟨f⟩ := whole_origin_certificate S H R B hB Δ A hA W.model hLocal hshort
  obtain ⟨c⟩ := completion_from_origin_map S H R B hB Δ A hA W.model hLocal f
  obtain ⟨k,hk⟩ := align_source_certificate S H R B hB A Δ hA W.model hLocal c W.inclusion W.inclusion_lang
  refine ⟨⟨W,c.namedMotion k,?_⟩⟩
  intro a
  simpa only [W.inclusion_apply] using hk a

end
end CCO.HKNReservoir
