import CCO.SimultaneousQuotients.Towers.TowerGeometry

/-! Entry to finite towers from an original source with ANY atom universe.
The first quotient has the actual orbital palette; all later stages are
`ExactTower`. Thus no universe restriction is imposed on the original source. -/

universe u v w t
namespace CCO.SimultaneousQuotients.Towers
open RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)] [∀ i, Countable (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (J : ∀ i, Setoid (X i)) (E : ∀ i, NonemptyExact S i i)
variable (represents : ∀ i, evaluate S (E i).words = (J i).r)

@[reducible] noncomputable def firstStage : Stage.{u,v,t} ι G where
  X := Carrier J
  source := SimultaneousQuotients.source S H J E represents
  action := SimultaneousQuotients.action S H J E represents
  homogeneous := SimultaneousQuotients.homogeneous S H J E represents cco
  cycles := canonical_semanticCCO S H cco J E represents
  countable := countable_carrier J

variable (C : ExactTower (firstStage S H cco J E represents))

noncomputable def initialProject (i : ι) : X i → C.finalStage.X i :=
  fun x => C.project i (Quotient.mk'' x)

theorem initialProject_surjective (i : ι) :
    Function.Surjective (initialProject S H cco J E represents C i) :=
  (C.project_surjective i).comp Quotient.mk''_surjective

/-- Every total initial kernel of a finite current-stage tower is FULL
exact in the INITIAL source, by repeated safe upward pullback. -/
noncomputable def initialTotalExact (i : ι) : NonemptyExact S i i :=
  ExactCRT.CanonicalTyped.exactPullback S H J E represents cco (C.totalExact i)

theorem initialTotalExact_represents (i : ι) :
    evaluate S (initialTotalExact S H cco J E represents C i).words =
      (Setoid.ker (initialProject S H cco J E represents C i)).r := by
  rw [initialTotalExact,ExactCRT.CanonicalTyped.exactPullback_relation,
    C.totalExact_represents i]
  rfl

theorem initial_le_total (i : ι) :
    J i ≤ Setoid.ker (initialProject S H cco J E represents C i) := by
  intro x y hxy
  exact congrArg (C.project i) (Quotient.sound hxy)

noncomputable def initialFlatten (i : ι) :
    C.finalStage.X i ≃ Quotient (Setoid.ker (initialProject S H cco J E represents C i)) :=
  (Setoid.quotientKerEquivOfSurjective _
    (initialProject_surjective S H cco J E represents C i)).symm

@[simp] theorem initialFlatten_projection (i : ι) (x : X i) :
    initialFlatten S H cco J E represents C i (initialProject S H cco J E represents C i x) =
      (Quotient.mk'' x : Quotient (Setoid.ker (initialProject S H cco J E represents C i))) := by
  apply (initialFlatten S H cco J E represents C i).symm.injective
  rw [Equiv.symm_apply_apply]
  rfl

/-- Strict loss at ANY nonidentity current step, including the first. -/
theorem initial_rank_lt
    (h : (∃ i, ∃ x y : X i, x ≠ y ∧ J i x y) ∨ C.HasNonidentity) :
    diversityRank C.finalStage.source < diversityRank S := by
  rcases h with h | h
  · exact lt_of_le_of_lt C.rank_le (canonicalRank_lt S H J E represents h)
  · exact lt_of_lt_of_le (C.rank_lt h) (canonicalRank_le S H J E represents)

theorem initialProject_equivariant :
    letI := C.finalStage.action
    ∀ i (g : G) x, initialProject S H cco J E represents C i (g • x) =
      g • initialProject S H cco J E represents C i x := by
  letI := C.finalStage.action
  intro i g x
  exact C.project_equivariant i g (Quotient.mk'' x)

@[reducible] noncomputable def initialDirectSource :
    AtomicSource ι (fun i => Quotient (Setoid.ker (initialProject S H cco J E represents C i))) :=
  SimultaneousQuotients.source S H
    (fun i => Setoid.ker (initialProject S H cco J E represents C i))
    (initialTotalExact S H cco J E represents C)
    (initialTotalExact_represents S H cco J E represents C)

@[reducible] noncomputable def initialDirectAction :
    ∀ i, MulAction G (Quotient (Setoid.ker (initialProject S H cco J E represents C i))) :=
  SimultaneousQuotients.action S H
    (fun i => Setoid.ker (initialProject S H cco J E represents C i))
    (initialTotalExact S H cco J E represents C)
    (initialTotalExact_represents S H cco J E represents C)

theorem initialFlatten_equivariant :
    letI := C.finalStage.action
    letI := initialDirectAction S H cco J E represents C
    ∀ i (g : G) q, initialFlatten S H cco J E represents C i (g • q) =
      g • initialFlatten S H cco J E represents C i q := by
  letI := C.finalStage.action
  letI := initialDirectAction S H cco J E represents C
  intro i g q
  obtain ⟨x,rfl⟩ := initialProject_surjective S H cco J E represents C i q
  rw [←initialProject_equivariant S H cco J E represents C i g x,
    initialFlatten_projection,initialFlatten_projection]
  rfl

/-- The canonical finite-tower isomorphism preserves actual optional atomic
colours with a bijection of canonical atom names in every typed palette. -/
noncomputable def initialStructureIso :
    AtomicIso C.finalStage.source (initialDirectSource S H cco J E represents C) := by
  letI := C.finalStage.action
  letI := initialDirectAction S H cco J E represents C
  apply atomicIso C.finalStage.source (initialDirectSource S H cco J E represents C)
    (initialFlatten S H cco J E represents C)
  intro i j x x' y y'
  have hFinal : C.finalStage.source.colour x y = C.finalStage.source.colour x' y' ↔
      GroupActions.orbital (G := G) x y x' y' := by
    constructor
    · exact (C.finalStage.source.pair_homogeneous_of_homogeneous C.finalStage.homogeneous) x x' y y'
    · rintro ⟨g,rfl,rfl⟩
      exact (C.finalStage.source.colourInvariant_of_homogeneous C.finalStage.homogeneous g x y).symm
  exact hFinal.trans ((equiv_orbital_iff
    (initialFlatten S H cco J E represents C)
    (initialFlatten_equivariant S H cco J E represents C) x x' y y').trans
    ((SimultaneousQuotients.actual_colours S H
      (fun i => Setoid.ker (initialProject S H cco J E represents C i))
      (initialTotalExact S H cco J E represents C)
      (initialTotalExact_represents S H cco J E represents C))
        (initialFlatten S H cco J E represents C i x)
        (initialFlatten S H cco J E represents C j y)
        (initialFlatten S H cco J E represents C i x')
        (initialFlatten S H cco J E represents C j y')).symm)

end CCO.SimultaneousQuotients.Towers
