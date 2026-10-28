import CCO.StrongExact.CycleCompletion
import CCO.DiagramAction

/-!
# STRONG C06: prescribe the literal image of a complete old base

For a finite *complete* displayed base, a CCO homomorphism gives an
induced copy. Full original-source finite homogeneity aligns that copy
with the prescribed literal real tuple. B001 SAP injectivization then
fixes the aligned tuple while splitting all remaining collisions.

The chosen finite vertex type here lives in the sort/carrier universe
used by the accepted homogeneous tuple extension API. This is a
universe-level specialization, not an additional mathematical premise.
-/

universe u v w

namespace CCO.PartialDiagram

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u, v, w} ι X}
variable {V : Type (max u v)}

/-- Complete literal old base, including its genuine specified
colours on ALL pairs of distinct formal base vertices. -/
def CompleteOn (D : PartialDiagram S V) (base : Set V) : Prop :=
  ∀ x ∈ base, ∀ y ∈ base, ∀ hxy : x ≠ y,
    ∃ a : S.Atom (D.vertexSort x) (D.vertexSort y),
      D.edge x y hxy = some a

/-- C06 complete-base strengthening at the natural finite-diagram
universe. The new target tuple realizes every displayed base edge
in the actual original source; no assumption of global injectivity of
the original homomorphism is made. In particular, the target sorts
and **literal** points are prescribed, not merely orbit types. -/
theorem strongCompletion_prescribed_base_of_SAP_CCO
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u, v, max u v, w} S)
    (D : PartialDiagram S V) (base : Set V)
    (hComplete : D.CompleteOn base)
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
  letI : Finite V := D.finite_type
  letI : Finite ↥base := inferInstance
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
  obtain ⟨g, hg⟩ :=
    H.extends_finite_diagram oldBase newBase hColour
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
