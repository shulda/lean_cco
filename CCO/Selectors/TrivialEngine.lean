import CCO.Selectors.Engine
import CCO.Selectors.PureCovariance

universe u v w
namespace CCO.Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

theorem generated_trivial_iff (seed D : TaggedMenu S) :
    ActionGenerated S (PureTagAction.trivial (S := S)) seed D ↔ Generated S seed D := by
  constructor
  · intro h
    induction h with
    | seed => exact Generated.seed
    | opposite h ih => exact Generated.opposite ih
    | left P hP h ih => exact Generated.left P hP ih
    | right P hP h ih => exact Generated.right P hP ih
    | action g h ih => exact ih
  · intro h
    induction h with
    | seed => exact ActionGenerated.seed
    | opposite h ih => exact ActionGenerated.opposite ih
    | left P hP h ih => exact ActionGenerated.left P hP ih
    | right P hP h ih => exact ActionGenerated.right P hP ih

/-- The unconditional named-sort route discharges the engine's sole no-return premise. -/
theorem pureNoReturn_trivial (C : ExactCalculus S) (hNR : FullNoReturn S) :
    PureNoReturn S (PureTagAction.trivial (S := S)) := by
  intro seed hs D E hD hE hParallel hEq
  have hDE := generated_exact S C (PureTagAction.trivial (S := S)) hs hD
  have hEE := generated_exact S C (PureTagAction.trivial (S := S)) hs hE
  rcases D with ⟨i,j,D⟩
  rcases E with ⟨i',j',E⟩
  rcases hParallel with ⟨hi,hj⟩
  cases hi; cases hj
  have hMenu : D = E := hNR D E hDE hEE (by
    intro T
    have h := Set.ext_iff.mp hEq T
    simpa only [generatedFamily, Set.mem_setOf_eq, generated_trivial_iff S] using h)
  cases hMenu
  rfl

end CCO.Selectors
