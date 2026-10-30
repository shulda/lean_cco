import CCO.SimultaneousQuotients.Source
import CCO.SimultaneousQuotients.CCOBranch.Semantics
import CCO.SimultaneousQuotients.Towers.ExactKernel
import CCO.SimultaneousQuotients.Towers.CanonicalRank
import CCO.SimultaneousQuotients.Towers.AtomicIso

/-! Finite CURRENT-stage exact towers with all standing source properties
proved at every step. Each constructor invokes the actual simultaneous
quotient theorems. Safe upward pullback gives an explicit initial exact
presentation for every final word/menu and for each total initial kernel. -/

universe u v t z
namespace CCO.SimultaneousQuotients.Towers
open RawExact

/-- Data of an actual current source. These properties are preserved by
`Stage.quotient`, not demanded anew from a tower's caller at every stage. -/
structure Stage (ι : Type u) (G : Type t) [Group G] where
  X : ι → Type v
  source : AtomicSource.{u,v,v} ι X
  action : ∀ i, MulAction G (X i)
  homogeneous : letI := action; HomogeneousSource source G
  cycles : SemanticCCO.{u,v,max u v,v} source
  countable : ∀ i, Countable (X i)

variable {ι : Type u} {G : Type t} [Group G]

structure StepData (P : Stage.{u,v,t} ι G) where
  kernel : ∀ i, Setoid (P.X i)
  exact : ∀ i, NonemptyExact P.source i i
  represents : ∀ i, evaluate P.source (exact i).words = (kernel i).r

namespace Stage

@[reducible] noncomputable def quotient (P : Stage.{u,v,t} ι G) (D : StepData P) : Stage.{u,v,t} ι G := by
  letI := P.action
  letI := P.countable
  exact {
    X := Carrier D.kernel
    source := SimultaneousQuotients.source P.source P.homogeneous D.kernel D.exact D.represents
    action := SimultaneousQuotients.action P.source P.homogeneous D.kernel D.exact D.represents
    homogeneous := SimultaneousQuotients.homogeneous P.source P.homogeneous D.kernel D.exact D.represents P.cycles
    cycles := canonical_semanticCCO P.source P.homogeneous P.cycles D.kernel D.exact D.represents
    countable := countable_carrier D.kernel
  }

end Stage

/-- Only concrete current exact kernels are chosen at a step. No later
homogeneity, CCO, AP, exact-descent or rank provider is a constructor field. -/
inductive ExactTower : Stage.{u,v,t} ι G → Type (max (u+1) (v+1) (t+1)) where
  | nil (P : Stage.{u,v,t} ι G) : ExactTower P
  | step {P : Stage.{u,v,t} ι G} (D : StepData P)
      (tail : ExactTower (P.quotient D)) : ExactTower P

namespace ExactTower

variable {P : Stage.{u,v,t} ι G}

noncomputable def length : {P : Stage.{u,v,t} ι G} → ExactTower P → Nat
  | _, .nil _ => 0
  | _, .step _ tail => tail.length + 1

@[reducible] noncomputable def finalStage : {P : Stage.{u,v,t} ι G} → ExactTower P → Stage.{u,v,t} ι G
  | P, .nil _ => P
  | _, .step _ tail => tail.finalStage

@[reducible] noncomputable def project : {P : Stage.{u,v,t} ι G} → (C : ExactTower P) → ∀ i, P.X i → C.finalStage.X i
  | _, .nil _, _, x => x
  | _, .step _ tail, i, x => tail.project i (Quotient.mk'' x)

theorem project_surjective (C : ExactTower P) (i : ι) : Function.Surjective (C.project i) := by
  induction C with
  | nil P => exact Function.surjective_id
  | @step P D tail ih => exact ih.comp Quotient.mk''_surjective

/-- Safe upward pullback iterated through exactly the current stages. -/
noncomputable def pullExact : {P : Stage.{u,v,t} ι G} → (C : ExactTower P) →
    {i j : ι} → NonemptyExact C.finalStage.source i j → NonemptyExact P.source i j
  | _, .nil _, _, _, B => B
  | P, .step D tail, _, _, B =>
    letI := P.action
    ExactCRT.CanonicalTyped.exactPullback P.source P.homogeneous D.kernel D.exact D.represents
      P.cycles (tail.pullExact B)

theorem pullExact_relation (C : ExactTower P) {i j : ι}
    (B : NonemptyExact C.finalStage.source i j) :
    evaluate P.source (C.pullExact B).words =
      GroupActions.pullback (C.project i) (C.project j)
        (evaluate C.finalStage.source B.words) := by
  induction C with
  | nil P => rfl
  | @step P D tail ih =>
    letI := P.action
    dsimp only [finalStage] at B ⊢
    change evaluate P.source
      (ExactCRT.CanonicalTyped.exactPullback P.source P.homogeneous D.kernel D.exact D.represents
        P.cycles (tail.pullExact B)).words = _
    rw [ExactCRT.CanonicalTyped.exactPullback_relation,ih B]
    rfl

/-- Every first current kernel is contained in the whole pulled-back
initial kernel of the finite tower. -/
theorem step_le_total {P : Stage.{u,v,t} ι G} (D : StepData P)
    (tail : ExactTower (P.quotient D)) (i : ι) :
    D.kernel i ≤ Setoid.ker ((ExactTower.step D tail).project i) := by
  intro x y hxy
  exact congrArg (tail.project i) (Quotient.sound hxy)

/-- The total initial kernel is defined from the final ACTUAL projection. -/
noncomputable def totalKernel (C : ExactTower P) (i : ι) : Setoid (P.X i) :=
  Setoid.ker (C.project i)

/-- An explicit initial exact presentation, obtained by pulling back the
final equality word. Old and current equality are never conflated. -/
noncomputable def totalExact (C : ExactTower P) (i : ι) : NonemptyExact P.source i i :=
  C.pullExact (exactIdentityAtom C.finalStage.source i)

theorem totalExact_represents (C : ExactTower P) (i : ι) :
    evaluate P.source (C.totalExact i).words = (C.totalKernel i).r := by
  rw [totalExact,pullExact_relation,exactIdentityAtom_relation]
  rfl

noncomputable def flatten (C : ExactTower P) (i : ι) :
    C.finalStage.X i ≃ Quotient (C.totalKernel i) :=
  (Setoid.quotientKerEquivOfSurjective (C.project i) (C.project_surjective i)).symm

@[simp] theorem flatten_project (C : ExactTower P) (i : ι) (x : P.X i) :
    C.flatten i (C.project i x) = (Quotient.mk'' x : Quotient (C.totalKernel i)) := by
  apply (C.flatten i).symm.injective
  rw [Equiv.symm_apply_apply]
  rfl

/-- Zero-stage source, projection, and genuine identity kernel. -/
theorem zero_source : (ExactTower.nil P).finalStage = P := rfl

theorem zero_project (i : ι) : (ExactTower.nil P).project i = id := rfl

theorem zero_kernel (i : ι) : (ExactTower.nil P).totalKernel i = ⊥ := by
  apply Setoid.ext
  intro x y
  rfl

/-- Every stage source retains countable homogeneity and semantic HOM CCO;
these are actual fields constructed by repeated proved quotient inheritance. -/
theorem final_properties (C : ExactTower P) :
    (∀ i, Countable (C.finalStage.X i)) ∧
    (letI := C.finalStage.action; HomogeneousSource C.finalStage.source G) ∧
    SemanticCCO.{u,v,max u v,v} C.finalStage.source :=
  ⟨C.finalStage.countable,C.finalStage.homogeneous,C.finalStage.cycles⟩

/-- Formal finite vertex universes are unrestricted. -/
theorem final_cycles_general (C : ExactTower P) :
    SemanticCCO.{u,v,z,v} C.finalStage.source :=
  semanticCCO_change_universe C.finalStage.source C.finalStage.cycles

end ExactTower
end CCO.SimultaneousQuotients.Towers
