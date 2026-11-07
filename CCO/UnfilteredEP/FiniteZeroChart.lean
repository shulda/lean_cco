import CCO.UnfilteredEP.FiniteTerminalTags
import CCO.FullCode.Roots

/-! B064 C98--C100: the actual finite terminal recipe has no proper
imaginary coordinates. Its root scheme has one genuine terminal tag
and ZERO coordinates; the domain is true and every generated support
is empty. No proper MI above Top is invented. -/

universe u v w a
namespace CCO.UnfilteredEP
open FullCode
noncomputable section

/-- The proper-imaginary signature after its actual MI family is empty. -/
def finiteEmptyHiddenLanguage : Language.{u} where
  Sorts := PEmpty
  Func := PEmpty
  Unary := PEmpty
  Binary := PEmpty
  input := PEmpty.elim
  output := PEmpty.elim
  unarySort := PEmpty.elim
  leftSort := PEmpty.elim
  rightSort := PEmpty.elim
  finiteSort := inferInstance
  finiteFunc := inferInstance
  finiteUnary := inferInstance
  finiteBinary := inferInstance

def finiteEmptyHiddenStructure : Structure finiteEmptyHiddenLanguage.{u} PEmpty.{u+1} where
  sort := PEmpty.elim
  func := PEmpty.elim
  functional F := PEmpty.elim F
  func_sorted F := PEmpty.elim F
  unary := PEmpty.elim
  unary_sorted U := PEmpty.elim U
  binary := PEmpty.elim
  binary_sorted R := PEmpty.elim R

/-- No unary functions exist in the actual empty proper signature. -/
def finiteEmptyNormalForms : NormalForms finiteEmptyHiddenLanguage.{u} where
  count s := PEmpty.elim s
  form s := PEmpty.elim s
  normalize {s} := PEmpty.elim s

variable (D : FiniteOwnerStage.{u,v,w})

/-- Actual endpoint tags remain even though the proper chart is empty. -/
def finiteZeroRootScheme : RootScheme finiteEmptyHiddenLanguage.{u} where
  Tag := D.Sorts
  finiteTag := by letI := D.source.finiteSort; infer_instance
  arity _ := 0
  coordinateSort _ := Fin.elim0
  delta _ := .truth

def finiteZeroRoot (tag : D.Sorts) :
    Root finiteEmptyHiddenStructure (finiteZeroRootScheme D) where
  tag := tag
  coordinate := Fin.elim0
  sorted j := Fin.elim0 j
  valid := trivial

/-- Zero-coordinate roots are exactly the actual terminal tags. -/
def finiteZeroRootEquiv :
    Root finiteEmptyHiddenStructure (finiteZeroRootScheme D) ≃ D.Sorts where
  toFun r := r.tag
  invFun := finiteZeroRoot D
  left_inv r := by
    rcases r with ⟨tag,coordinate,sorted,valid⟩
    have hc : coordinate = Fin.elim0 := funext (fun j => Fin.elim0 j)
    cases hc
    rfl
  right_inv _ := rfl

/-- Every object in the zero chart has literally empty unary support. -/
theorem finiteZeroSupport_empty {A : Type a}
    (O : Object finiteEmptyHiddenStructure (finiteZeroRootScheme D) A) :
    O.support = ∅ := by
  have hc : O.coordinates = ∅ := by
    ext x
    constructor
    · rintro ⟨y,j,_⟩
      exact Fin.elim0 j
    · intro h
      exact h.elim
  change finiteEmptyHiddenStructure.closure O.coordinates = ∅
  rw [hc]
  exact finiteEmptyHiddenStructure.closure_eq
    (fun F => PEmpty.elim F)

/-- No term presentation or order-comparison position survives the
zero chart. Thus there are no extra free same-root or cross-root codes. -/
theorem finiteZeroPresentation_isEmpty :
    IsEmpty (Presentation finiteEmptyNormalForms (finiteZeroRootScheme D)) :=
  ⟨fun p => Fin.elim0 p.1.2⟩

/-- C98: the empty chart reflects the actual endpoint, whose entire
proper nonidentity FULL MI family is empty on every named clone sort. -/
theorem finiteZeroChart_actual (terminal : D.Terminal) :
    (∀ i, IsEmpty (CloneTupleGeometry.FullCloneProperMI D.source i)) ∧
      (∀ tag, (finiteZeroRootScheme D).arity tag = 0) :=
  ⟨D.terminalProperMI_isEmpty terminal,fun _ => rfl⟩

end
end CCO.UnfilteredEP
