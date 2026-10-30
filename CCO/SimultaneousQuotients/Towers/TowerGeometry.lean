import CCO.SimultaneousQuotients.Towers.ExactTower
import CCO.SimultaneousQuotients.Towers.SourceIso

/-! The actual finite tower loses diversity rank at every nonidentity step,
and its final projection canonically identifies complete orbital structures. -/

universe u v t
namespace CCO.SimultaneousQuotients.Towers
open RawExact

variable {ι : Type u} {G : Type t} [Group G]

namespace Stage

theorem quotient_rank_le (P : Stage.{u,v,t} ι G) (D : StepData P) :
    diversityRank (P.quotient D).source ≤ diversityRank P.source := by
  letI := P.action
  exact canonicalRank_le P.source P.homogeneous D.kernel D.exact D.represents

theorem quotient_rank_lt (P : Stage.{u,v,t} ι G) (D : StepData P)
    (h : ∃ i, ∃ x y : P.X i, x ≠ y ∧ D.kernel i x y) :
    diversityRank (P.quotient D).source < diversityRank P.source := by
  letI := P.action
  exact canonicalRank_lt P.source P.homogeneous D.kernel D.exact D.represents h

end Stage
namespace ExactTower
variable {P : Stage.{u,v,t} ι G}

theorem rank_le (C : ExactTower P) :
    diversityRank C.finalStage.source ≤ diversityRank P.source := by
  induction C with
  | nil P => exact le_refl _
  | @step P D tail ih => exact ih.trans (P.quotient_rank_le D)

/-- A real nonidentity kernel occurs at some CURRENT stage. -/
def HasNonidentity : {P : Stage.{u,v,t} ι G} → ExactTower P → Prop
  | _, .nil _ => False
  | P, .step D tail =>
      (∃ i, ∃ x y : P.X i, x ≠ y ∧ D.kernel i x y) ∨ tail.HasNonidentity

theorem rank_lt (C : ExactTower P) (h : C.HasNonidentity) :
    diversityRank C.finalStage.source < diversityRank P.source := by
  induction C with
  | nil P => exact False.elim h
  | @step P D tail ih =>
    rcases h with h | h
    · exact lt_of_le_of_lt tail.rank_le (P.quotient_rank_lt D h)
    · exact lt_of_lt_of_le (ih h) (P.quotient_rank_le D)

theorem project_equivariant (C : ExactTower P) :
    letI := P.action
    letI := C.finalStage.action
    ∀ i (g : G) x, C.project i (g • x) = g • C.project i x := by
  induction C with
  | nil P => intro i g x; rfl
  | @step P D tail ih =>
    letI := P.action
    letI := tail.finalStage.action
    intro i g x
    exact ih i g (Quotient.mk'' x)

/-- The direct original quotient structure by the total exact kernels. -/
@[reducible] noncomputable def directSource (C : ExactTower P) :
    AtomicSource ι (fun i => Quotient (C.totalKernel i)) := by
  letI := P.action
  exact SimultaneousQuotients.source P.source P.homogeneous C.totalKernel C.totalExact
    C.totalExact_represents

@[reducible] noncomputable def directAction (C : ExactTower P) :
    ∀ i, MulAction G (Quotient (C.totalKernel i)) := by
  letI := P.action
  exact SimultaneousQuotients.action P.source P.homogeneous C.totalKernel C.totalExact
    C.totalExact_represents

theorem flatten_equivariant (C : ExactTower P) :
    letI := C.finalStage.action
    letI := C.directAction
    ∀ i (g : G) q, C.flatten i (g • q) = g • C.flatten i q := by
  letI := P.action
  letI := C.finalStage.action
  letI := C.directAction
  intro i g q
  obtain ⟨x,rfl⟩ := C.project_surjective i q
  rw [←C.project_equivariant i g x,flatten_project,flatten_project]
  rfl

/-- Every complete named binary orbital is preserved and reflected by
finite-tower class flattening. Equality and all cross-sort blocks are included. -/
theorem flatten_orbitals (C : ExactTower P) :
    letI := C.finalStage.action
    letI := C.directAction
    ∀ i j (a x : C.finalStage.X i) (b y : C.finalStage.X j),
      GroupActions.orbital (G := G) a b x y ↔
      GroupActions.orbital (G := G) (C.flatten i a) (C.flatten j b)
        (C.flatten i x) (C.flatten j y) := by
  letI := C.finalStage.action
  letI := C.directAction
  intro i j a x b y
  exact equiv_orbital_iff C.flatten C.flatten_equivariant a x b y

/-- C46-C47: a complete typed atomic structure isomorphism, with canonical
bijections of atom names and actual optional colour preservation. -/
noncomputable def structureIso (C : ExactTower P) :
    AtomicIso C.finalStage.source C.directSource := by
  letI := P.action
  letI := C.finalStage.action
  letI := C.directAction
  apply atomicIso C.finalStage.source C.directSource C.flatten
  intro i j x x' y y'
  have hFinal : C.finalStage.source.colour x y = C.finalStage.source.colour x' y' ↔
      GroupActions.orbital (G := G) x y x' y' := by
    constructor
    · exact (C.finalStage.source.pair_homogeneous_of_homogeneous C.finalStage.homogeneous) x x' y y'
    · rintro ⟨g,rfl,rfl⟩
      exact (C.finalStage.source.colourInvariant_of_homogeneous C.finalStage.homogeneous g x y).symm
  exact hFinal.trans ((C.flatten_orbitals i j x x' y y').trans
    ((SimultaneousQuotients.actual_colours P.source P.homogeneous C.totalKernel C.totalExact
      C.totalExact_represents) (C.flatten i x) (C.flatten j y)
        (C.flatten i x') (C.flatten j y')).symm)

end ExactTower
end CCO.SimultaneousQuotients.Towers
