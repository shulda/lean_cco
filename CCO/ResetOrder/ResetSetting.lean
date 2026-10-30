import CCO.ResetOrder.ResetEP

/-! The source-facing theorem retains the stated hereditary/reasonable/
precompact/reduct-surjective hypotheses. The combinatorial core is stronger. -/
universe u v
namespace CCO.ResetOrder.Unary
open CCO.ResetOrder.Unary.Primitive
variable {L : Signature.{u}} {P : Fibres.{u,v} L} {X : ExtraLanguage L}

def TaskHereditary (U : TaskAge P) : Prop := ∀{A B}, U A → Nonempty (TaskHom B A) → U B

def TaskReasonable (U1 : TaskAge P) (U0 : Age.{u,v} L) : Prop :=
  ∀A, U1 A → ∀B, U0 B → ∀f : A.old.Emb B,
    ∃o : FibreOrder P B, U1 ⟨B,o⟩ ∧ ∃g : TaskHom A ⟨B,o⟩, ∀x, g.old.point x = f.point x

def TaskPrecompact (U1 : TaskAge P) (U0 : Age.{u,v} L) : Prop :=
  ∀B, U0 B → Finite {o : FibreOrder P B // U1 ⟨B,o⟩}

structure ResetSetting (R : FullAge P X) (U1 : TaskAge P) (U0 : Age.{u,v} L) where
  full_hereditary : FullHereditary R
  upper_hereditary : TaskHereditary U1
  lower_hereditary : Hereditary U0
  reasonable : TaskReasonable U1 U0
  precompact : TaskPrecompact U1 U0
  reduct : ∀A, U1 A → U0 A.old
  onto : ∀B, U0 B → ∃o : FibreOrder P B, U1 ⟨B,o⟩
  full_reduct : ∀F, R F → U1 F.task
  full_lift : ∀A, U1 A → ∃F, R F ∧ F.task = A
  reversal : ∀A, U1 A → U1 (reverse A)

/-- `thm:abstract-reset-order-EP`: fixed host before ALL exact-carrier competitors. -/
theorem abstract_reset_order_EP {R : FullAge P X} {U1 : TaskAge P} {U0 : Age.{u,v} L}
    (S : ResetSetting R U1 U0) (jep : FullJEP R) (ramsey : FullRamsey R)
    (schema : MidpointSchema R) (edgeType : CompleteResetEdgeType R) : TaskEP U1 U0 := by
  apply reset_expansion_property S.full_reduct S.reduct _ S.reversal jep ramsey schema edgeType
  intro A hA
  obtain ⟨F,hF,he⟩ := S.full_lift A hA
  refine ⟨F,hF,?_⟩
  rw [he]
  exact ⟨taskIdentity A⟩

end CCO.ResetOrder.Unary
