import CCO.FullCode.EmbeddingBijection
import CCO.FullCode.StructureTransport

/-! Concrete finite scope boundaries for C44--C47. These distinguish omitted
code and misplaced quantifiers; they are not counterexamples satisfying all
of the positive transfer hypotheses. -/
namespace CCO.FullCode.Boundaries

abbrev tiny : Language where
  Sorts := Unit
  Func := Unit
  Unary := Unit
  Binary := Unit
  input _ := ()
  output _ := ()
  unarySort _ := ()
  leftSort _ := ()
  rightSort _ := ()
  finiteSort := inferInstance
  finiteFunc := inferInstance
  finiteUnary := inferInstance
  finiteBinary := inferInstance

abbrev model {V : Type} (F : V → Set V)
    (hF : ∀ x y z, y ∈ F x → z ∈ F x → y = z)
    (U : V → Prop) (R : V → V → Prop) : Structure tiny V where
  sort _ := ()
  func _ := F
  functional _ := hF
  func_sorted _ _ _ _ := ⟨rfl, rfl⟩
  unary _ := U
  unary_sorted _ _ _ := rfl
  binary _ := R
  binary_sorted _ _ _ _ := ⟨rfl, rfl⟩

abbrev emptyFunction {V : Type} (U : V → Prop) (R : V → V → Prop) : Structure tiny V :=
  model (fun _ => ∅) (fun _ _ _ h => False.elim h) U R

def undefinedSingleton : Structure tiny Unit := emptyFunction (fun _ => True) (fun _ _ => False)

def fixedSingleton : Structure tiny Unit :=
  model (fun x => {x}) (fun _ _ _ hy hz => hy.trans hz.symm)
    (fun _ => True) (fun _ _ => False)

abbrev functionTerm : Term tiny () () := .app () (Term.id (L := tiny) ())

theorem undefined_vs_fixed_domain :
    ¬ (functionTerm.eval undefinedSingleton ()).Nonempty ∧
      (functionTerm.eval fixedSingleton ()).Nonempty := by
  constructor
  · rintro ⟨y, z, _, hy⟩; exact hy
  · exact ⟨(), (), rfl, rfl⟩

theorem no_domain_reflecting_singleton_map :
    ¬ Nonempty (Structure.Embedding undefinedSingleton fixedSingleton) := by
  rintro ⟨f⟩
  have hv : () ∈ fixedSingleton.func () (f.point ()) := by
    change () = f.point ()
    exact Subsingleton.elim _ _
  obtain ⟨_, hz, _⟩ := f.reflect_func () () () hv
  exact hz

abbrev nfForm (s t : Unit) (i : Fin 2) : Term tiny s t := by
  cases s; cases t
  exact if i.val = 0 then Term.id (L := tiny) () else functionTerm

abbrev twoForms : NormalForms tiny where
  count _ _ := 2
  form := nfForm
  normalize q := match q with
    | .id _ => 0
    | .app _ _ => 1

abbrev tupleScheme (n : ℕ) : RootScheme tiny where
  Tag := Unit
  finiteTag := inferInstance
  arity _ := n
  coordinateSort _ _ := ()
  delta _ := .truth

abbrev tupleRoot {V : Type} (C : Structure tiny V) (n : ℕ) (xs : Fin n → V)
    (sorted : ∀ x, C.sort x = ()) : Root C (tupleScheme n) where
  tag := ()
  coordinate := xs
  sorted j := sorted (xs j)
  valid := trivial

abbrev identityPresentation (n : ℕ) (j : Fin n) : Presentation twoForms (tupleScheme n) :=
  ⟨⟨(), j⟩, (), 0⟩

abbrev functionPresentation (n : ℕ) (j : Fin n) : Presentation twoForms (tupleScheme n) :=
  ⟨⟨(), j⟩, (), 1⟩

theorem diagonal_code_detects_undefined :
    ¬ EqualityCode twoForms
      (tupleRoot undefinedSingleton 1 (fun _ => ()) (fun _ => rfl))
      (tupleRoot undefinedSingleton 1 (fun _ => ()) (fun _ => rfl))
      (functionPresentation 1 0) (functionPresentation 1 0) := by
  rintro ⟨x, ⟨z, _, _, _, hz⟩, _⟩
  exact hz

theorem diagonal_code_detects_fixed :
    EqualityCode twoForms
      (tupleRoot fixedSingleton 1 (fun _ => ()) (fun _ => rfl))
      (tupleRoot fixedSingleton 1 (fun _ => ()) (fun _ => rfl))
      (functionPresentation 1 0) (functionPresentation 1 0) := by
  refine ⟨(), ?_, ?_⟩ <;> exact ⟨(), ⟨rfl, rfl⟩, (), rfl, rfl⟩

def boolEmpty : Structure tiny Bool := emptyFunction (fun _ => True) (fun _ _ => False)

def distinctPair : Root boolEmpty (tupleScheme 2) :=
  tupleRoot boolEmpty 2 (fun j => j.val == 1) (fun _ => rfl)

def repeatedPair : Root boolEmpty (tupleScheme 2) :=
  tupleRoot boolEmpty 2 (fun _ => false) (fun _ => rfl)

theorem same_root_equality_essential :
    ¬ EqualityCode twoForms distinctPair distinctPair
      (identityPresentation 2 0) (identityPresentation 2 1) ∧
    EqualityCode twoForms repeatedPair repeatedPair
      (identityPresentation 2 0) (identityPresentation 2 1) := by
  constructor
  · rintro ⟨x, ⟨y, ⟨_, hy⟩, hxy⟩, ⟨z, ⟨_, hz⟩, hxz⟩⟩
    have hf : x = false := hxy.trans hy.symm
    have ht : x = true := hxz.trans hz.symm
    exact Bool.noConfusion (hf.symm.trans ht)
  · exact ⟨false, ⟨false, ⟨rfl, rfl⟩, rfl⟩, ⟨false, ⟨rfl, rfl⟩, rfl⟩⟩

def threeEmpty : Structure tiny (Fin 3) := emptyFunction (fun _ => True) (fun _ _ => False)
def fourEmpty : Structure tiny (Fin 4) := emptyFunction (fun _ => True) (fun _ _ => False)
def sharedLeft : Root threeEmpty (tupleScheme 2) :=
  tupleRoot threeEmpty 2 (fun j => ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩) (fun _ => rfl)
def sharedRight : Root threeEmpty (tupleScheme 2) :=
  tupleRoot threeEmpty 2 (fun j => ⟨j.val + 1, Nat.add_lt_add_right j.isLt 1⟩) (fun _ => rfl)
def disjointLeft : Root fourEmpty (tupleScheme 2) :=
  tupleRoot fourEmpty 2 (fun j => ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩) (fun _ => rfl)
def disjointRight : Root fourEmpty (tupleScheme 2) :=
  tupleRoot fourEmpty 2 (fun j => ⟨j.val + 2, Nat.add_lt_add_right j.isLt 2⟩) (fun _ => rfl)

theorem cross_root_equality_essential :
    EqualityCode twoForms sharedLeft sharedRight
      (identityPresentation 2 1) (identityPresentation 2 0) ∧
    ¬ EqualityCode twoForms disjointLeft disjointRight
      (identityPresentation 2 1) (identityPresentation 2 0) := by
  constructor
  · exact ⟨1, ⟨1, ⟨rfl, rfl⟩, rfl⟩, ⟨1, ⟨rfl, rfl⟩, rfl⟩⟩
  · rintro ⟨x, ⟨y, ⟨_, hy⟩, hxy⟩, ⟨z, ⟨_, hz⟩, hxz⟩⟩
    have h12 : (1 : Fin 4) = 2 := (hxy.trans hy.symm).symm.trans (hxz.trans hz.symm)
    exact (by decide : (1 : Fin 4) ≠ 2) h12

def orderedBool : Structure tiny Bool :=
  emptyFunction (fun _ => True) (fun x y => x = false ∧ y = true)

theorem comparison_code_essential :
    Function.Injective Bool.not ∧
    (∀ x, orderedBool.unary () (!x) ↔ orderedBool.unary () x) ∧
    ¬ (∀ x y, orderedBool.binary () (!x) (!y) ↔ orderedBool.binary () x y) := by
  refine ⟨(fun {x y} h => by cases x <;> cases y <;> cases h <;> rfl), (fun _ => Iff.rfl), ?_⟩
  intro h
  have hh := (h false true).mpr ⟨rfl, rfl⟩
  exact Bool.noConfusion hh.1

abbrev rootOnlyScheme : RootScheme tiny where
  Tag := Unit
  finiteTag := inferInstance
  arity _ := 1
  coordinateSort _ _ := ()
  delta _ := .unary () ⟨0, Term.id (L := tiny) ()⟩

def orphanHost : Structure tiny Bool := emptyFunction (fun x => x = false) (fun _ _ => False)

theorem orphan_not_generated :
    true ∉ (Object.full orphanHost rootOnlyScheme).support := by
  intro h
  have hc : orphanHost.IsClosed {false} := by
    intro F x hx y hy; exact False.elim hy
  have hcoord : (Object.full orphanHost rootOnlyScheme).coordinates ⊆ {false} := by
    rintro x ⟨r, j, rfl⟩
    obtain ⟨z, hz, hroot⟩ := r.valid
    have hj : j = 0 := Subsingleton.elim _ _
    exact hj ▸ ((Set.mem_singleton_iff.mp hz).symm ▸ hroot)
  have hf : true ∈ ({false} : Set Bool) := orphanHost.closure_minimal hc hcoord h
  exact Bool.noConfusion hf

def orphanColored : Structure tiny Bool :=
  emptyFunction (fun x => x = false) (fun x y => x = true ∧ y = true)

def falseRoot {C : Structure tiny Bool}
    (hU : C.unary () false) (hs : C.sort false = ()) : Root C rootOnlyScheme where
  tag := ()
  coordinate _ := false
  sorted _ := hs
  valid := ⟨false, rfl, hU⟩

def orphanUncoloredObject : Object orphanHost rootOnlyScheme Unit where
  root _ := falseRoot rfl rfl
  injective _ _ _ := Subsingleton.elim _ _

def orphanColoredObject : Object orphanColored rootOnlyScheme Unit where
  root _ := falseRoot rfl rfl
  injective _ _ _ := Subsingleton.elim _ _

theorem term_empty_graph_no_motion {L : Language} {V : Type} (C : Structure L V)
    (empty : ∀ F x, C.func F x = ∅) {s t : L.Sorts} (q : Term L s t)
    {x y : V} (hy : y ∈ q.eval C x) : y = x := by
  cases q with
  | id => exact hy
  | app F q =>
    obtain ⟨z, _, hy⟩ := hy
    rw [empty] at hy
    exact False.elim hy

theorem orphan_colored_presentation_false (a : Unit)
    (p : Presentation twoForms rootOnlyScheme) {x : Bool}
    (hx : x ∈ (orphanColoredObject.root a).presentation twoForms p) : x = false := by
  obtain ⟨z, ⟨_, hz⟩, hx⟩ := hx
  exact (term_empty_graph_no_motion orphanColored (fun _ _ => rfl) _ hx).trans hz.symm

theorem term_eval_of_equal_functions {L : Language} {V : Type} (C D : Structure L V)
    (hF : ∀ F x, C.func F x = D.func F x) {s t : L.Sorts} (q : Term L s t) (x : V) :
    q.eval C x = q.eval D x := by
  induction q with
  | id => rfl
  | app F q ih =>
    ext y
    constructor
    · rintro ⟨z, hz, hy⟩; exact ⟨z, ih ▸ hz, hF F z ▸ hy⟩
    · rintro ⟨z, hz, hy⟩; exact ⟨z, ih.symm ▸ hz, (hF F z).symm ▸ hy⟩

theorem orphan_presentation_iff (a : Unit) (p : Presentation twoForms rootOnlyScheme) (x : Bool) :
    x ∈ (orphanColoredObject.root a).presentation twoForms p ↔
      x ∈ (orphanUncoloredObject.root a).presentation twoForms p := by
  have hc : (orphanColoredObject.root a).coordinateGraph p.1 =
      (orphanUncoloredObject.root a).coordinateGraph p.1 := rfl
  constructor
  · rintro ⟨z, hz, hx⟩
    exact ⟨z, hc ▸ hz, term_eval_of_equal_functions orphanColored orphanHost (fun _ _ => rfl) _ z ▸ hx⟩
  · rintro ⟨z, hz, hx⟩
    exact ⟨z, hc.symm ▸ hz,
      (term_eval_of_equal_functions orphanColored orphanHost (fun _ _ => rfl) _ z).symm ▸ hx⟩

/-- Both complete selected-root codes agree while an orphan carries
different hidden binary expansion data on the SAME marked carrier. -/
def invisible_orphan_embedding :
    Object.Embedding twoForms orphanUncoloredObject orphanColoredObject where
  point x := x
  injective := Function.injective_id
  tag_eq _ := rfl
  equality_iff a b p q := by
    constructor
    · rintro ⟨x, hx, hy⟩
      exact ⟨x, (orphan_presentation_iff a p x).mp hx, (orphan_presentation_iff b q x).mp hy⟩
    · rintro ⟨x, hx, hy⟩
      exact ⟨x, (orphan_presentation_iff a p x).mpr hx, (orphan_presentation_iff b q x).mpr hy⟩
  unary_iff _ a p := by
    constructor
    · rintro ⟨x, hx, hU⟩; exact ⟨x, (orphan_presentation_iff a p x).mp hx, hU⟩
    · rintro ⟨x, hx, hU⟩; exact ⟨x, (orphan_presentation_iff a p x).mpr hx, hU⟩
  binary_iff _ a _ p _ := by
    constructor
    · rintro ⟨x, _, hx, _, hxy⟩
      have hfalse := orphan_colored_presentation_false a p hx
      exact False.elim (Bool.noConfusion (hfalse.symm.trans hxy.1))
    · rintro ⟨_, _, _, _, hR⟩
      exact False.elim hR

theorem invisible_orphan_data_differ :
    ¬ orphanHost.binary () true true ∧ orphanColored.binary () true true :=
  ⟨fun h => h, rfl, rfl⟩

def jumpingHost : Structure tiny Bool :=
  model (fun _ => {true}) (fun _ _ _ hy hz => hy.trans hz.symm)
    (fun x => x = false) (fun _ _ => False)

def jumpingRoot : Root jumpingHost rootOnlyScheme where
  tag := ()
  coordinate _ := false
  sorted _ := rfl
  valid := ⟨false, rfl, rfl⟩

theorem jumping_function_idempotent (x : Bool) :
    jumpingHost.func () x = {true} ∧ jumpingHost.func () true = {true} := ⟨rfl, rfl⟩

theorem jumping_code_function_not_root :
    ¬ EqualityCode twoForms jumpingRoot jumpingRoot
      (functionPresentation 1 0) (identityPresentation 1 0) := by
  rintro ⟨x, ⟨_, _, _, _, hx⟩, ⟨y, ⟨_, hy⟩, hxy⟩⟩
  have hfalse : x = false := hxy.trans hy.symm
  exact Bool.noConfusion (hfalse.symm.trans hx)

theorem singleton_defined_function_code_fixed (C : Structure tiny Unit)
    (r : Root C rootOnlyScheme) :
    EqualityCode twoForms r r (functionPresentation 1 0) (functionPresentation 1 0) →
      EqualityCode twoForms r r (functionPresentation 1 0) (identityPresentation 1 0) := by
  rintro ⟨x, hx, _⟩
  refine ⟨x, hx, x, ?_, rfl⟩
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

theorem term_nonempty_of_total {L : Language} {V : Type} (C : Structure L V)
    (total : ∀ F x, (C.func F x).Nonempty) {s t : L.Sorts} (q : Term L s t) (x : V) :
    (q.eval C x).Nonempty := by
  induction q with
  | id => exact ⟨x, rfl⟩
  | app F q ih =>
    obtain ⟨z, hz⟩ := ih
    obtain ⟨y, hy⟩ := total F z
    exact ⟨y, z, hz, hy⟩

theorem jumping_term_nonempty {s t : Unit} (q : Term tiny s t) (x : Bool) :
    (q.eval jumpingHost x).Nonempty :=
  term_nonempty_of_total jumpingHost (fun _ _ => ⟨true, rfl⟩) q x

theorem jumping_finite_normal_forms : twoForms.Valid jumpingHost := by
  intro s t q x _
  cases q with
  | id s => cases s; rfl
  | app F q =>
    cases F
    change (Term.app () q).eval jumpingHost x = functionTerm.eval jumpingHost x
    ext y
    constructor
    · rintro ⟨z, _, hy⟩; exact ⟨x, rfl, hy⟩
    · rintro ⟨z, _, hy⟩
      obtain ⟨w, hw⟩ := jumping_term_nonempty q x
      exact ⟨w, hw, hy⟩

theorem added_function_enlarges_old_support :
    true ∈ (Object.full jumpingHost rootOnlyScheme).support ∧
      true ∉ (Object.full orphanHost rootOnlyScheme).support := by
  refine ⟨?_, orphan_not_generated⟩
  let O := Object.full jumpingHost rootOnlyScheme
  have hfalse : false ∈ O.support := O.coordinate_mem_support jumpingRoot 0
  exact jumpingHost.isClosed_closure O.coordinates () false hfalse rfl

theorem old_singleton_not_expanded_closed : ¬ jumpingHost.IsClosed {false} := by
  intro h
  have ht : true ∈ ({false} : Set Bool) := h () false rfl rfl
  exact Bool.noConfusion ht

theorem no_same_singleton_jump (F : Unit → Unit) : ¬ ∃ x, F x ≠ x := by
  rintro ⟨x, hx⟩
  exact hx (Subsingleton.elim _ _)

abbrev oldLanguage : Language where
  Sorts := Unit
  Func := Empty
  Unary := Unit
  Binary := Unit
  input := Empty.elim
  output := Empty.elim
  unarySort _ := ()
  leftSort _ := ()
  rightSort _ := ()
  finiteSort := inferInstance
  finiteFunc := inferInstance
  finiteUnary := inferInstance
  finiteBinary := inferInstance

def forgetAddedFunction : Reduct oldLanguage tiny where
  sortMap x := x
  funcMap := Empty.elim
  unaryMap x := x
  binaryMap x := x
  input_eq F := F.elim
  output_eq F := F.elim
  unary_eq _ := rfl
  left_eq _ := rfl
  right_eq _ := rfl

abbrev oldRootScheme : RootScheme oldLanguage where
  Tag := Unit
  finiteTag := inferInstance
  arity _ := 1
  coordinateSort _ _ := ()
  delta _ := .unary () ⟨0, Term.id (L := oldLanguage) ()⟩

/-- This time the OLD structure is the actual named reduct that forgets the
ADDED function, rather than a different interpretation of an old symbol. -/
theorem added_symbol_breaks_support_reduct_commutation :
    true ∈ (Object.full jumpingHost rootOnlyScheme).support ∧
    true ∉ (Object.full (jumpingHost.reduct forgetAddedFunction) oldRootScheme).support := by
  refine ⟨added_function_enlarges_old_support.1, ?_⟩
  let C := jumpingHost.reduct forgetAddedFunction
  intro ht
  have hc : C.IsClosed {false} := by intro F; exact F.elim
  have hcoord : (Object.full C oldRootScheme).coordinates ⊆ {false} := by
    rintro _ ⟨r, j, rfl⟩
    obtain ⟨z, hz, hroot⟩ := r.valid
    have hj : j = 0 := Subsingleton.elim _ _
    exact hj ▸ ((Set.mem_singleton_iff.mp hz).symm ▸ hroot)
  exact Bool.noConfusion (C.closure_minimal hc hcoord ht)

/-- Logical incidence diagnostic only: picking the host after the expansion
works, whereas a single host before all expansions fails. -/
theorem ep_quantifier_order :
    (∀ expansion : Bool, ∃ host : Bool, host ≠ expansion) ∧
      ¬ (∃ host : Bool, ∀ expansion : Bool, host ≠ expansion) := by
  constructor
  · intro expansion
    exact ⟨!expansion, by cases expansion <;> decide⟩
  · rintro ⟨host, h⟩
    exact h host rfl

theorem favorable_expansion_not_universal :
    (∃ expansion : Bool, expansion = true) ∧ ¬ (∀ expansion : Bool, expansion = true) := by
  exact ⟨⟨true, rfl⟩, fun h => Bool.noConfusion (h false)⟩

end CCO.FullCode.Boundaries
