import CCO.PairSafeSplit.SAP.Gates
import CCO.PairSafeSplit.Infinity.MarkedFibres

/-! The old SAP/type-gate argument applies inside any ONE actual global
character marking. The marking is not assumed homogeneous. -/

universe u v w t
namespace CCO.PairSafeSplit.SAP
open APCharacter RigidGroupoid.Geometry
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}

theorem marked_fibre_infinite (P : SourcePhase S H C A) (sap : AgeSAP S)
    (mark : Sigma X → Bit) (hm : P.masks.GlobalMarking mark)
    (B : FiniteInduced (X := X)) {i : ι} (x : X i)
    (hx : (⟨i,x⟩ : Sigma X) ∉ B.vertices) :
    (Infinity.markedTypeFibre S B (fun y : X i => mark ⟨i,y⟩) x).Infinite := by
  by_cases hi : Nonempty (Bridge S A i)
  · let b : Reached S A := ⟨i,hi⟩
    exact Infinity.markedTypeFibre_infinite S H sap (reachedKernelEq P b)
      (reached_kernel_gt_bot P sap b) B _
      (fun a c hac => (marking_gate_eq P mark hm b a c hac).symm) x hx
  · exact Infinity.constant_markedTypeFibre_infinite S H sap B _ x
      (fun y => (hm.1 ⟨i,y⟩ hi).trans (hm.1 ⟨i,x⟩ hi).symm) hx

end
end CCO.PairSafeSplit.SAP
