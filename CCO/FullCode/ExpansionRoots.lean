import CCO.FullCode.ExpansionSetting
import CCO.FullCode.CodeTransport

/-! Actual code readout on a root carrier fixed in the OLD language before
any competing expansion is chosen. -/

universe u v w a
namespace CCO.FullCode
variable {L₀ L₁ : Language.{u}} {V : Type v}

def Root.changeStructure {L : Language.{u}} {C D : Structure L V}
    {S : RootScheme L} (h : C = D) (r : Root C S) : Root D S where
  tag := r.tag
  coordinate := r.coordinate
  sorted j := by rw [← h]; exact r.sorted j
  valid := by rw [← h]; exact r.valid

def Root.structureEquiv {L : Language.{u}} {C D : Structure L V}
    (h : C = D) (S : RootScheme L) : Root C S ≃ Root D S where
  toFun := Root.changeStructure h
  invFun := Root.changeStructure h.symm
  left_inv r := by cases r; rfl
  right_inv r := by cases r; rfl

namespace ExpansionOn
variable {H₁ : FiniteHidden.{u,v} L₁ → Prop} {D : FiniteHidden.{u,v} L₀}

def rootCarrierEquiv (ρ : LanguageExpansion L₀ L₁) (S : RootScheme L₀)
    (b : ExpansionOn ρ.toReduct H₁ D) :
    Root b.model (S.lift ρ) ≃ Root D.model S :=
  (Root.expansionEquiv ρ b.model S).trans (Root.structureEquiv b.reduct_eq S)

def rootObject (ρ : LanguageExpansion L₀ L₁) (S : RootScheme L₀)
    (b : ExpansionOn ρ.toReduct H₁ D) : Object b.model (S.lift ρ) (Root D.model S) :=
  mappedOldRoots ρ S D.model b.model
    ((Structure.Embedding.id D.model).targetCongr b.reduct_eq.symm)

@[simp] theorem rootObject_rootCarrierEquiv (ρ : LanguageExpansion L₀ L₁)
    (S : RootScheme L₀) (b : ExpansionOn ρ.toReduct H₁ D)
    (r : Root b.model (S.lift ρ)) :
    (b.rootObject ρ S).root (b.rootCarrierEquiv ρ S r) = r := by
  cases r
  rfl

@[simp] theorem rootObject_coordinates (ρ : LanguageExpansion L₀ L₁)
    (S : RootScheme L₀) (b : ExpansionOn ρ.toReduct H₁ D) :
    (b.rootObject ρ S).coordinates = (Object.full D.model S).coordinates := rfl

/-- The complete expanded code is transported on the same old root set. -/
def rootReindex (ρ : LanguageExpansion L₀ L₁) (S : RootScheme L₀)
    (N : NormalForms L₁) (b : ExpansionOn ρ.toReduct H₁ D) :
    Object.Embedding N (Object.full b.model (S.lift ρ)) (b.rootObject ρ S) where
  point := b.rootCarrierEquiv ρ S
  injective := (b.rootCarrierEquiv ρ S).injective
  tag_eq r := congrArg Root.tag (b.rootObject_rootCarrierEquiv ρ S r)
  equality_iff r s p q := by
    change EqualityCode N ((b.rootObject ρ S).root (b.rootCarrierEquiv ρ S r))
      ((b.rootObject ρ S).root (b.rootCarrierEquiv ρ S s)) p q ↔ EqualityCode N r s p q
    rw [rootObject_rootCarrierEquiv, rootObject_rootCarrierEquiv]
  unary_iff U r p := by
    change UnaryCode N U ((b.rootObject ρ S).root (b.rootCarrierEquiv ρ S r)) p ↔
      UnaryCode N U r p
    rw [rootObject_rootCarrierEquiv]
  binary_iff R r s p q := by
    change BinaryCode N R ((b.rootObject ρ S).root (b.rootCarrierEquiv ρ S r))
      ((b.rootObject ρ S).root (b.rootCarrierEquiv ρ S s)) p q ↔ BinaryCode N R r s p q
    rw [rootObject_rootCarrierEquiv, rootObject_rootCarrierEquiv]

def fromHiddenOnOldRoots (ρ : LanguageExpansion L₀ L₁) (S : RootScheme L₀)
    (N : NormalForms L₁) (b : ExpansionOn ρ.toReduct H₁ D)
    {W : Type w} {C : Structure L₁ W} {A : Type a}
    (O : Object C (S.lift ρ) A) (f : Structure.Embedding O.supportStructure b.model) :
    Object.Embedding N O (b.rootObject ρ S) :=
  (b.rootReindex ρ S N).comp (Object.fromHidden N O f)

end ExpansionOn
end CCO.FullCode
