import CCO.APCharacter.SourceAge.Reduct
import CCO.APCharacter.SourceAge.UnarySource
import CCO.APCharacter.MarkedSource

/-! The old-reduct identification used by the actual unary source is
constructed from genuine reasonableness and countable back-and-forth.
It is not a homogeneous-marking or principal-isomorphism hypothesis. -/
universe u v w t
namespace CCO.APCharacter.SourceAge
open RigidGroupoid.Geometry
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}
variable (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
variable [∀ i, Countable (X i)]

def actualIdentification : UnarySource.Identification S H (P.completion_property cco) := by
  let h := old_reduct_equiv S H (P.completion_property cco) P.finite_seed_extension
  exact ⟨Classical.choose h,(Classical.choose_spec h).1,(Classical.choose_spec h).2⟩

end
end CCO.APCharacter.SourceAge
