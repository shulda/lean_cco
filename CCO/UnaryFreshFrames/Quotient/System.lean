import CCO.UnaryFreshFrames.Quotient.NamedAvoidance

/-! Actual existing named quotient projections. The family is data of named
terms, never a family of arbitrary equivariant maps or completion providers. -/
universe u v
namespace CCO.UnaryFreshFrames.Structure
variable {L : Language.{u}} {V : Type v} (H : Structure L V)

structure NamedProjection where
  source : L.Sorts
  target : L.Sorts
  term : Term L source target
  surjective : Function.Surjective (H.typedEval term)
  strict : ¬ Function.Injective (H.typedEval term)

namespace NamedProjection

/-- Every target really is the quotient by the ACTUAL kernel of its named
projection; this is not an assumed abstract quotient presentation. -/
noncomputable def quotientEquiv (p : H.NamedProjection) :
    Quotient (Setoid.ker (H.typedEval p.term)) ≃ H.Carrier p.target :=
  Setoid.quotientKerEquivOfSurjective _ p.surjective

end NamedProjection

structure NamedQuotientSystem (real : Set L.Sorts) where
  Index : Type u
  projection : Index → H.NamedProjection
  source_real : ∀ q, (projection q).source ∈ real
  represents : ∀ b : V, H.sort b ∉ real → ∃ q, H.sort b = (projection q).target

namespace NamedQuotientSystem
variable {H}

def KernelClauses {real : Set L.Sorts} (S : H.NamedQuotientSystem real) : Prop :=
  ∀ q, H.ForcedNamedFactors (S.projection q).term ∧
    H.InfiniteUnforcedIndex (S.projection q).term

def SourceTransitive {real : Set L.Sorts} (S : H.NamedQuotientSystem real)
    (G : Subgroup H.Aut) : Prop :=
  ∀ q, Quotient.Transitive (G := G) (M := H.Carrier (S.projection q).source)

/-- Actual A11 representation plus the proved fibre theorem supplies a fresh
real generator for ANY nonreal point and ANY finite forbidden set. -/
theorem representative {real : Set L.Sorts} (S : H.NamedQuotientSystem real)
    (G : Subgroup H.Aut) (ht : S.SourceTransitive G)
    (hfinite : ∀ x : V, (H.closureAt x).Finite) (hkernel : S.KernelClauses)
    (b : V) (hb : H.sort b ∉ real) (Z : Set V) (hZ : Z.Finite) :
    ∃ x : V, H.sort x ∈ real ∧ b ∈ H.closureAt x ∧
      H.closureAt x ∩ Z = H.closureAt b ∩ Z ∧ x ∉ Z := by
  obtain ⟨q, hq⟩ := S.represents b hb
  let p := S.projection q
  let b' : H.Carrier p.target := ⟨b, hq⟩
  obtain ⟨x, hx, hcl, hfresh, _⟩ := H.named_fibre_avoidance G (ht q) p.term
    p.surjective p.strict hfinite (hkernel q).1 (hkernel q).2 b' Z hZ
  have hbcl : b ∈ H.closureAt x.val := by
    have h := H.typedEval_mem_closureAt p.term x
    rw [hx] at h
    exact h
  exact ⟨x.val, x.property.symm ▸ S.source_real q, hbcl, hcl, hfresh⟩

end NamedQuotientSystem
end CCO.UnaryFreshFrames.Structure
