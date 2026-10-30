import CCO.RankInduction.ComponentConstruction
import CCO.RankInduction.JointAssembly
import CCO.RankInduction.OneDirection
import CCO.RankInduction.DirectionCases

/-! The normalized rank constructor has no stage, factor, master, HKN or
decoder provider input. All actual components are constructed from the
bound STRICT lower conclusions before their full original assembly. -/

universe v w t
namespace CCO.RankInduction
noncomputable section
open RawExact RealClosure.Bounds FinitePackets.Normalization

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] [Countable M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)

theorem normalized_constructor [Infinite M] (normalized : NoFiniteExactKernel S)
    (lower : Lower S G H cco) : ClosedRooted S G := by
  classical
  intro safe hs A0 finiteA nonemptyA
  rcases direction_cases S with ⟨D,unique⟩ | many
  · exact one_direction_under_lower S H cco normalized D unique lower
      safe hs A0 finiteA nonemptyA
  · obtain ⟨F⟩ := Factors.exists_source_stage S H cco lower normalized many safe hs A0 finiteA nonemptyA
    exact Factors.joint_stage_exists S H cco normalized F finiteA many hs

end
end CCO.RankInduction
