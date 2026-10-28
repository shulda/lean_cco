import CCO.StrongExact.CycleCompletion
import CCO.DiagramAction
import Mathlib.Data.Fintype.EquivFin

/-!
# C06: prescribe a complete old base in ANY finite diagram universe

The accepted homogeneous-tuple API indexes tuples in Type(max u v).
A finite formal base in an arbitrary Type z is reindexed by an actual
ULift(Fin(card base)) equivalence before applying that API. No extra source
premise or source/API change is used. The original natural-universe
PrescribedBase export remains unchanged as a specialization.
-/

universe u v w z

namespace CCO.PartialDiagram

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u, v, w} ι X}
variable {V : Type z}

/-- C06 with all original prescribed-complete-base quantifiers and arbitrary
formal universe z. Both the finite base and every literal target point are
preserved; old source homogeneity is invoked only after finite reindexing. -/
theorem strongCompletion_prescribed_base_any_universe_of_SAP_CCO
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u, v, z, w} S)
    (D : PartialDiagram S V) (base : Set V)
    (hComplete : ∀ x ∈ base, ∀ y ∈ base, ∀ hxy : x ≠ y,
      ∃ a : S.Atom (D.vertexSort x) (D.vertexSort y),
        D.edge x y hxy = some a)
    (target : ∀ x : V, X (D.vertexSort x))
    (hTarget : ∀ x ∈ base, ∀ y ∈ base, ∀ (hxy : x ≠ y)
      (a : S.Atom (D.vertexSort x) (D.vertexSort y)),
      D.edge x y hxy = some a →
        S.colour (target x) (target y) = some a)
    (hCycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∃ f : DiagramHom D, f.IsInjective ∧
      ∀ x ∈ base, f.point x = target x := by
  classical
  obtain ⟨f⟩ := cco V D hCycles
  let : Finite V := D.finite_type
  let : Finite ↥base := inferInstance
  let oldBase : ↥base → Sigma X := fun p => f.image p.val
  let newBase : ↥base → Sigma X :=
    fun p => ⟨D.vertexSort p.val, target p.val⟩
  have hColour : ∀ p q : ↥base,
      taggedColour S (oldBase p) (oldBase q) =
      taggedColour S (newBase p) (newBase q) := by
    intro p q
    by_cases hEq : p.val = q.val
    · have hpq : p = q := Subtype.ext hEq
      subst q
      have hOld : S.colour (f.point p.val) (f.point p.val) = none :=
        (S.colour_none_iff _ _).2 rfl
      have hNew : S.colour (target p.val) (target p.val) = none :=
        (S.colour_none_iff _ _).2 rfl
      simp [taggedColour, oldBase, newBase, DiagramHom.image, hOld, hNew]
    · obtain ⟨a, ha⟩ :=
        hComplete p.val p.property q.val q.property hEq
      have hf := f.preserves_edge p.val q.val hEq a ha
      have ht :=
        hTarget p.val p.property q.val q.property hEq a ha
      simp [taggedColour, oldBase, newBase, DiagramHom.image, hf, ht]
  let : Fintype ↥base := Fintype.ofFinite ↥base
  let e := Fintype.equivFin ↥base
  let Index := ULift.{max u v,0} (Fin (Fintype.card ↥base))
  let oldTuple : Index → Sigma X := fun q => oldBase (e.symm q.down)
  let newTuple : Index → Sigma X := fun q => newBase (e.symm q.down)
  have hTupleColour : ∀ p q : Index,
      taggedColour S (oldTuple p) (oldTuple q) =
        taggedColour S (newTuple p) (newTuple q) :=
    fun p q => hColour (e.symm p.down) (e.symm q.down)
  obtain ⟨g,hgTuple⟩ :=
    H.extends_finite_diagram oldTuple newTuple hTupleColour
  have hg (p : ↥base) : g • oldBase p = newBase p := by
    have h := hgTuple (ULift.up (e p))
    dsimp only [oldTuple,newTuple] at h
    simpa only [e.symm_apply_apply] using h
  let aligned : DiagramHom D := DiagramHom.transport H g f
  have hAligned : ∀ x ∈ base,
      aligned.image x =
        (⟨D.vertexSort x, target x⟩ : Sigma X) := by
    intro x hx
    have hh := hg ⟨x, hx⟩
    change g • f.image x =
      (⟨D.vertexSort x, target x⟩ : Sigma X) at hh
    calc
      aligned.image x = g • f.image x :=
        DiagramHom.transport_image H g f x
      _ = _ := hh
  have hPin : ∀ x ∈ base, ∀ y ∈ base,
      aligned.image x = aligned.image y → x = y := by
    intro x hx y hy hEqual
    by_contra hNe
    obtain ⟨a, ha⟩ := hComplete x hx y hy hNe
    have hCol : S.atomRel a (target x) (target y) :=
      hTarget x hx y hy hNe a ha
    have hTag : (⟨D.vertexSort x, target x⟩ : Sigma X) =
        (⟨D.vertexSort y, target y⟩ : Sigma X) := by
      calc
        (⟨D.vertexSort x, target x⟩ : Sigma X) =
            aligned.image x := (hAligned x hx).symm
        _ = aligned.image y := hEqual
        _ = _ := hAligned y hy
    exact (S.atomRel_ne hCol) hTag
  obtain ⟨f', hf', hKeep⟩ :=
    D.strongCompletion_fixed_base_of_SAP H sap aligned base hPin
  refine ⟨f', hf', ?_⟩
  intro x hx
  have hTag : f'.image x =
      (⟨D.vertexSort x, target x⟩ : Sigma X) :=
    (hKeep x hx).trans (hAligned x hx)
  simpa only [DiagramHom.image, Sigma.mk.injEq,
    heq_eq_eq, true_and] using hTag

end CCO.PartialDiagram
