import CCO.UnfilteredEP.FiniteCoreCriterion

/-! B064 C110: a free two-label partition of the finite age of a pure
infinite set fails unary EP. On EVERY proposed old host the legal constant
marking omits the other singleton. This elementary boundary is independent
of terminalization, Ramsey providers and all actual source constructions. -/

namespace CCO.UnfilteredEP

/-- Every original off-diagonal atom permits every label pair. -/
def freeTwoLabelTemplate : FiniteTemplate Unit Unit Bool where
  sort _ := ()
  rel _ _ _ := True

/-- Precisely the finite complete one-atom pure-set objects. -/
abbrev pureFiniteAge : FiniteAge.{0,0,0,0} Unit Unit where
  Obj := Nat
  Point n := Fin n
  finitePoint _ := inferInstance
  sort _ _ := ()
  colour _ x y := if x = y then none else some ()
  diagonal _ x y := by
    by_cases h : x = y <;> simp [h]

def constantFreeMarking (n : Nat) (label : Bool) :
    pureFiniteAge.Marking freeTwoLabelTemplate n where
  label _ := label
  sorted _ := rfl
  pairs _ _ _ _ := True.intro

/-- The constant false endomorphism is not a permutation. -/
theorem free_two_label_template_not_core : ¬ freeTwoLabelTemplate.Core := by
  intro h
  have endo : freeTwoLabelTemplate.Endomorphism (fun _ => false) :=
    ⟨fun _ => rfl,fun _ _ _ _ => True.intro⟩
  have onto := (h _ endo).1.2
  obtain ⟨x,hx⟩ := onto true
  exact Bool.false_ne_true hx

/-- Every old finite set has legal constant markings. -/
theorem free_two_label_reduct_surjective :
    pureFiniteAge.ReductSurjective freeTwoLabelTemplate :=
  fun n => ⟨constantFreeMarking n false⟩

/-- A proposed host's constant false marking misses the true singleton,
regardless of the size of that fixed original host. -/
theorem free_two_label_unary_EP_fails :
    ¬ pureFiniteAge.UnaryEP freeTwoLabelTemplate := by
  intro ep
  obtain ⟨n,hn⟩ := ep 1 (constantFreeMarking 1 true)
  obtain ⟨e⟩ := hn (constantFreeMarking n false)
  have hx := e.labels (0 : Fin 1)
  exact Bool.false_ne_true hx

end CCO.UnfilteredEP
