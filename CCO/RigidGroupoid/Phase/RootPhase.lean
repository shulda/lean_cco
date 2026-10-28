import CCO.RigidGroupoid.Phase.ActualPhase

/-! The distinguished source arrow may be supplied literally at the
original chosen root gate A. Reached.root has exactly that gate by the
accepted path-uniqueness theorem; this equality transports types only and
does not alter the represented old relation. -/

universe u v w t
namespace CCO.RigidGroupoid.Phase
open Geometry

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

def kernelLoopCast {i : ι} {A B : Kernel S i} (e : A = B)
    (R : Arrow S A A) : Arrow S B B := e ▸ R

theorem kernelLoopCast_rel {i : ι} {A B : Kernel S i} (e : A = B)
    (R : Arrow S A A) : (kernelLoopCast S e R).rel = R.rel := by
  cases e
  rfl

theorem kernelLoopCast_nonidentity {i : ι} {A B : Kernel S i} (e : A = B)
    (R : Arrow S A A) (hne : R ≠ Arrow.id A) :
    kernelLoopCast S e R ≠ Arrow.id B := by
  cases e
  exact hne

variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G) (C : ExactCalculus S)

theorem actual_root_phase {i : ι} (A : Kernel S i) (t : Arrow S A A)
    (ht : t ≠ Arrow.id A) :
    let e := Reached.root_kernel H C (A := A)
    let t₀ := kernelLoopCast S e.symm t
    letI := Reached.groupoid H C (A := A)
    ∃ χ : Abstract.Character (Reached S A), χ.value t₀ = 1 ∧
      ∃ mark, Abstract.IsMarking (Reached.pointFunctor H C A) χ mark := by
  exact actual_source_phase S H C A (Reached.root A)
    (kernelLoopCast S (Reached.root_kernel H C (A := A)).symm t)
    (kernelLoopCast_nonidentity S _ t ht)

/-- Standing original source consumer with the LITERAL original root input.
The exact calculus and the actual finite free quotient action are produced,
while the distinguished nonidentity remains the explicitly required data. -/
theorem standing_root_phase (cco : SemanticCCO.{u,v,max u v,w} S)
    (_countableSorts : ∀ j, Countable (X j)) {i : ι} (A : Kernel S i)
    (t : Arrow S A A) (ht : t ≠ Arrow.id A) :
    let C := exactCalculus_of_homogeneous_CCO S H cco
    let e := Reached.root_kernel H C (A := A)
    let t₀ := kernelLoopCast S e.symm t
    letI := Reached.groupoid H C (A := A)
    ∃ χ : Abstract.Character (Reached S A), χ.value t₀ = 1 ∧
      ∃ mark, Abstract.IsMarking (Reached.pointFunctor H C A) χ mark :=
  actual_root_phase S H (exactCalculus_of_homogeneous_CCO S H cco) A t ht

end CCO.RigidGroupoid.Phase
