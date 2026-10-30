import CCO.ResetOrder.Unary.Category
import Mathlib.Data.Fintype.EquivFin

/-! C53: actual same binary root type with different generated unary types. -/
namespace CCO.ResetOrder.ClosureBoundaries
open CCO.UnarySupport
open CCO.ResetOrder.Unary

def language : Signature where
  Sorts := Unit
  Func := Unit
  Rel := Unit
  input _ := ()
  output _ := ()
  arity _ := 2
  argument _ _ := ()
  finiteSort := inferInstance
  finiteFunc := inferInstance
  finiteRel := inferInstance

def diagram (split : Bool) : Structure language (Fin 4) where
  sort _ := ()
  func _ x := if x = 0 then {2} else if x = 1 then {if split then 3 else 2} else ∅
  functional _ x y z hy hz := by split at hy <;> split at hz <;> simp_all
  func_sorted _ _ _ _ := ⟨rfl,rfl⟩
  rel _ _ := True
  rel_sorted _ _ _ _ := rfl

theorem same_binary_root_reduct :
    ∀xs : Fin 2 → Fin 4, (diagram false).rel () xs ↔ (diagram true).rel () xs := fun _ => Iff.rfl

theorem no_pointed_closure_embedding :
    ¬ ∃f : Hom (diagram false) (diagram true), f.point 0 = 0 ∧ f.point 1 = 1 := by
  rintro ⟨f,h0,h1⟩
  have ha := f.map_func () 0 2 (by simp [diagram])
  have hb := f.map_func () 1 2 (by simp [diagram])
  rw [h0] at ha
  rw [h1] at hb
  have ha' : f.point 2 = 2 := by simpa [diagram] using ha
  have hb' : f.point 2 = 3 := by simpa [diagram] using hb
  exact (by decide : (2 : Fin 4) ≠ 3) (ha'.symm.trans hb')

theorem midpoint_already_in_whole_pair_closure :
    ∃z : Fin 4, z ∈ (diagram false).closure {0,1} ∧ (0 : Fin 4) ≠ z ∧ z ≠ 1 := by
  refine ⟨2,?_,by decide,by decide⟩
  exact ⟨0,by simp,Relation.ReflTransGen.refl.tail ⟨(),by simp [diagram]⟩⟩

def generated (split : Bool) : Set (Fin 4) := (diagram split).closure {0,1}

def closedDiagram (split : Bool) : Structure language (generated split) :=
  (diagram split).induce (generated split) ((diagram split).isClosed_closure _)

def rootZero (split : Bool) : generated split := ⟨0,(diagram split).subset_closure _ (by simp)⟩
def rootOne (split : Bool) : generated split := ⟨1,(diagram split).subset_closure _ (by simp)⟩

def descendantTwo : generated false :=
  ⟨2,0,by simp,Relation.ReflTransGen.refl.tail ⟨(),by simp [diagram]⟩⟩

/-- The failure concerns the WHOLE induced generated structures themselves. -/
theorem no_actual_pointed_generated_embedding :
    ¬ ∃f : Hom (closedDiagram false) (closedDiagram true),
      (f.point (rootZero false)).val = 0 ∧ (f.point (rootOne false)).val = 1 := by
  rintro ⟨f,h0,h1⟩
  have ha := f.map_func () (rootZero false) descendantTwo (by
    change (2 : Fin 4) ∈ (diagram false).func () 0
    simp [diagram])
  have hb := f.map_func () (rootOne false) descendantTwo (by
    change (2 : Fin 4) ∈ (diagram false).func () 1
    simp [diagram])
  change (f.point descendantTwo).val ∈ (diagram true).func () (f.point (rootZero false)).val at ha
  change (f.point descendantTwo).val ∈ (diagram true).func () (f.point (rootOne false)).val at hb
  rw [h0] at ha
  rw [h1] at hb
  have ha' : (f.point descendantTwo).val = 2 := by simpa [diagram] using ha
  have hb' : (f.point descendantTwo).val = 3 := by simpa [diagram] using hb
  exact (by decide : (2 : Fin 4) ≠ 3) (ha'.symm.trans hb')

theorem root_reduct_does_not_determine_generated_type :
    (∀xs : Fin 2 → Fin 4, (diagram false).rel () xs ↔ (diagram true).rel () xs) ∧
    (¬ ∃f : Hom (diagram false) (diagram true), f.point 0 = 0 ∧ f.point 1 = 1) ∧
    (∃z : Fin 4, z ∈ (diagram false).closure {0,1} ∧ (0 : Fin 4) ≠ z ∧ z ≠ 1) :=
  ⟨same_binary_root_reduct,no_pointed_closure_embedding,midpoint_already_in_whole_pair_closure⟩

end CCO.ResetOrder.ClosureBoundaries
