import CCO.RankInduction.Basis
import CCO.StrongExact.TriangleFullness

/-! The original source's triangle-definedness is a proved standing-source
consequence. It is not a new callback added to the rank construction. -/

universe v w t z
namespace CCO.RankInduction
open RawExact

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] [Countable M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)

include H cco in
omit [Countable M] in
theorem original_triangle_defined {V : Type z} [Finite V]
    (A : CompleteDiagram (S := S) V) (small : A.SmallRealizable) :
    ∃ f : DiagramHom A.diagram, f.IsInjective :=
  A.triangleFullness_of_homogeneous_CCO H (semanticCCO_change_universe S cco) small

end CCO.RankInduction
