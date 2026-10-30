import CCO.CloneSAP.CCO.Lift
import Mathlib.Basic.Countable.Basic
import Lean.Elab.Tactic.Omega

universe u v w z
namespace CCO.CloneSAP
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

/-- Countability is inherited literally; a finite or singleton old source
is allowed and does not make the new clone fibres finite. -/
theorem countable_carrier (i : ι) [Countable (X i)] : Countable (Carrier X i) := inferInstance

theorem countable_real_points [Countable (Sigma X)] : Countable (Sigma (Carrier X)) :=
  pointEquiv.injective.countable

include S in
/-- All named sorts retain their real witnesses; no unrealized sort is added. -/
theorem nonempty_carrier (i : ι) : Nonempty (Carrier X i) := (source S).nonemptySort i

/-- Even a singleton old sort has an actual c,c,c diversity triangle. -/
theorem clone_triangle (i : ι) :
    (source S).Triangle (.inr ⟨rfl⟩ : (source S).Atom i i)
      (.inr ⟨rfl⟩) (.inr ⟨rfl⟩) := by
  obtain ⟨q⟩ := S.nonemptySort i
  refine ⟨(q,0),(q,1),(q,2),?_,?_,?_⟩
  · exact (source_clone_iff S _ _).mpr ⟨rfl,Nat.zero_ne_one⟩
  · exact (source_clone_iff S _ _).mpr ⟨rfl,by omega⟩
  · exact (source_clone_iff S _ _).mpr ⟨rfl,by omega⟩

/-- C36: the empty partial diagram and arbitrary isolated typed vertices
have actual injective realizations, independently of CCO. -/
theorem isolated_realization {V : Type z} (D : PartialDiagram (source S) V)
    (missing : ∀ x y h, D.edge x y h = none) :
    ∃ f : DiagramHom D, f.IsInjective := by
  classical
  let p : ∀ x : V, X (D.vertexSort x) := fun x => Classical.choice (S.nonemptySort _)
  apply CCO.lift_owner_assignment S D p
  · intro x y h a ha
    rw [missing] at ha
    cases ha
  · intro x y h e he
    rw [missing] at he
    cases he

end CCO.CloneSAP
