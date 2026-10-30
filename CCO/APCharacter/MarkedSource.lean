import CCO.APCharacter.ParitySource
import CCO.APCharacter.SeedSource
import CCO.APCharacter.PhaseWitnesses
import CCO.APCharacter.PathNormalForm
import CCO.APCharacter.MaskReadout
import CCO.APCharacter.Completion.Source
import CCO.APCharacter.Age.Realized

/-! Actual maximal-character marked completion and the genuine homogeneous
marked age. Every generic algebra, finite seed, folding and completion
provider is instantiated from the original source. -/
universe u v w t
namespace CCO.APCharacter
open RigidGroupoid.Geometry
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}
namespace SourcePhase
variable (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)

include cco in
/-- Actual source instance: the old-cycle folding law is proved, the
phase mask calculus comes from original maximality, and all finite seed
pair tests come from the actual rigid groupoid. -/
theorem completion_property : Age.CompletionProperty S P.masks :=
  Completion.marked_completion_small P.masks H (P.calculus cco) P.finite_seed_extension cco

abbrev MarkedLimit := Age.Limit S H (P.completion_property cco)
noncomputable abbrev markedCoding := Age.limitCoding S H (P.completion_property cco)

/-- The WHOLE actual constructed marked expansion is homogeneous. This is
not a statement about one arbitrarily chosen global orbit-seed marking. -/
theorem marked_homogeneous : (Age.Language S).IsUltrahomogeneous (P.MarkedLimit cco) :=
  Age.homogeneous S H (P.completion_property cco)

/-- Semantic marked CCO is transferred through actual finite old-age charts,
allowing unrelated cycle witnesses and legitimate AP collisions. -/
theorem marked_cco {V : Type} (D : PartialDiagram S V) (bits : V → Bit)
    (legal : P.masks.LocalLegal D bits)
    (cycles : ∀ K : SimpleCycle D, Age.CycleRealizes S H (P.completion_property cco) D bits K) :
    Age.DiagramRealizes S H (P.completion_property cco) D bits :=
  Age.marked_cco S H (P.completion_property cco) D bits legal cycles

end SourcePhase
end
end CCO.APCharacter
