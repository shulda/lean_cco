import CCO.HKNReservoir.ExternalWitness
import CCO.HKNReservoir.Certificate
import CCO.HKNReservoir.WholeOrigins

/-! Structural automorphisms act on the unchanged partial reservoir B₀.
C₀ is an existential complete certificate on the SAME carrier, with an
actual injective source embedding. Its unrecorded holes are not choices
transported by the structural automorphisms. -/
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

/-- C31: the reservoir retains BOTH actual external stages, all original
partial records and request extensions, plus a separate complete source
certificate fixing the literal source A pointwise. -/
structure CompletableReservoir (n : Nat) where
  stage : StagedWitness (sourceAction S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) n
  certificate : PacketCertificate S H R B hB Δ A hA stage.model
    (locallyInSource_of_faithful (sourceTag S H R B Δ) stage.inclusion stage.faithful)
  fixes_source : ∀ a : A, certificate.point (Sum.inl a) = a.val.down

namespace CompletableReservoir
variable {S H R B hB Δ A hA} {n : Nat}
variable (r : CompletableReservoir S H R B hB Δ A hA n)

/-- No choice is needed to state the actual exact certificate on C₀. -/
def completeStructure := encode r.certificate.completionData

def completeEmbedding : Structure.Embedding (sourceAction S H R B Δ)
    r.completeStructure (sourceStructure S H R B hB) := r.certificate.embedding

theorem completeEmbedding_source (a : A) : r.completeEmbedding (Sum.inl a) = a.val := by
  apply ULift.ext
  exact r.fixes_source a

/-- Every ORIGINAL compatible partial map, before packet saturation,
extends on B₀ with its exact ENTIRE prescribed owner component. -/
theorem extends_original [Finite A]
    (p : Request (sourceTag S H R B Δ) (finiteSourceData S H R B hB A hA)) :
    ∃ g : Structure.Automorphism (sourceAction S H R B Δ) r.stage.model,
      g.lang = p.lang ∧ ∀ x, x ∈ p.point.source → g (Sum.inl x) = Sum.inl (p.point x) :=
  actual_original_request_extensions S H R B hB Δ A hA r.stage p

theorem every_language_component (γ : Δ) :
    ∃ g : Structure.Automorphism (sourceAction S H R B Δ) r.stage.model, g.lang = γ :=
  all_language_components S H R B hB Δ A hA r.stage γ

/-- All original fine records, including complete matrices of every
recorded packet pair, occur in the actual completion certificate. -/
theorem retains_original_record (x y) (a : S.Atom () ())
    (ha : r.stage.model.rel (.fine a) (![x,y])) :
    r.certificate.completionData.fine a x y := r.certificate.fine a x y ha

end CompletableReservoir
end
end CCO.HKNReservoir
