import CCO.ResetOrder.FreshMidpoints
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Basic.Finite.Prod

/-! The finite obligations refer ONLY to the original source, and each newly
chosen midpoint is outside the ENTIRE accumulated host. -/
universe u v
namespace CCO.ResetOrder.Unary
open CCO.UnarySupport
variable {L : Signature.{u}} {P : Fibres.{u,v} L} {X : ExtraLanguage L}

abbrev Comparison (A : TaskObject P) :=
  {p : A.old.Carrier × A.old.Carrier // A.order.lt p.1 p.2}

structure StoredArray (A : TaskObject P) (n : ℕ) (obligation : Fin n → Comparison A)
    (D : FullObject P X) where
  copy : TaskHom A D.task
  midpoint : Fin n → D.task.old.Carrier
  left : ∀i, D.task.order.lt (copy.old.point (obligation i).val.1) (midpoint i)
  right : ∀i, D.task.order.lt (midpoint i) (copy.old.point (obligation i).val.2)
  reset_left : ∀i, P.reset D.task.old (copy.old.point (obligation i).val.1) (midpoint i)
  reset_right : ∀i, P.reset D.task.old (midpoint i) (copy.old.point (obligation i).val.2)
  fresh : ∀i, midpoint i ∉ Set.range copy.old.point
  distinct : Function.Injective midpoint

theorem store_original_comparisons {R : FullAge P X} (schema : MidpointSchema R)
    (A : TaskObject P) (n : ℕ) (obligation : Fin n → Comparison A)
    (F : FullObject P X) (hF : R F) (initial : TaskHom A F.task) :
    ∃D, R D ∧ Nonempty (StoredArray A n obligation D) := by
  induction n with
  | zero =>
    refine ⟨F,hF,⟨⟨initial,Fin.elim0,?_,?_,?_,?_,?_,?_⟩⟩⟩
    all_goals intro i; exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨D,hD,⟨s⟩⟩ := ih (fun i => obligation i.castSucc)
    have hcomp := (s.copy.order_iff _ _).2 (obligation (Fin.last n)).property
    obtain ⟨E,hE,j,z,hfresh,hl,hr,hml,hmr⟩ := schema D hD _ _ hcomp
    let mid : Fin (n+1) → E.task.old.Carrier := Fin.lastCases z (fun i => j.point (s.midpoint i))
    refine ⟨E,hE,⟨⟨taskCompose j.task s.copy,mid,?_,?_,?_,?_,?_,?_⟩⟩⟩
    · intro i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simpa only [mid,Fin.lastCases_last,Fin.lastCases_castSucc,taskCompose,compose,FullHom.point,Function.comp_def] using hl
      · simpa only [mid,Fin.lastCases_last,Fin.lastCases_castSucc,taskCompose,compose,FullHom.point,Function.comp_def] using (j.task.order_iff _ _).2 (s.left k)
    · intro i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simpa only [mid,Fin.lastCases_last,Fin.lastCases_castSucc,taskCompose,compose,FullHom.point,Function.comp_def] using hr
      · simpa only [mid,Fin.lastCases_last,Fin.lastCases_castSucc,taskCompose,compose,FullHom.point,Function.comp_def] using (j.task.order_iff _ _).2 (s.right k)
    · intro i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simpa only [mid,Fin.lastCases_last,Fin.lastCases_castSucc,taskCompose,compose,FullHom.point,Function.comp_def] using hml
      · simpa only [mid,Fin.lastCases_last,Fin.lastCases_castSucc,taskCompose,compose,FullHom.point,Function.comp_def] using (P.reset_natural j.task.old _ _).2 (s.reset_left k)
    · intro i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simpa only [mid,Fin.lastCases_last,Fin.lastCases_castSucc,taskCompose,compose,FullHom.point,Function.comp_def] using hmr
      · simpa only [mid,Fin.lastCases_last,Fin.lastCases_castSucc,taskCompose,compose,FullHom.point,Function.comp_def] using (P.reset_natural j.task.old _ _).2 (s.reset_right k)
    · intro i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · rintro ⟨a,ha⟩
        simp only [mid,Fin.lastCases_last,Fin.lastCases_castSucc] at ha
        exact hfresh ⟨s.copy.old.point a,ha⟩
      · rintro ⟨a,ha⟩
        simp only [mid,Fin.lastCases_last,Fin.lastCases_castSucc] at ha
        exact s.fresh k ⟨a,j.task.old.injective ha⟩
    · intro i k h
      revert h
      refine Fin.lastCases ?_ (fun a => ?_) i
      · refine Fin.lastCases ?_ (fun b => ?_) k
        · intro _; rfl
        · intro h
          simp only [mid,Fin.lastCases_last,Fin.lastCases_castSucc] at h
          exact False.elim (hfresh ⟨s.midpoint b,h.symm⟩)
      · refine Fin.lastCases ?_ (fun b => ?_) k
        · intro h
          simp only [mid,Fin.lastCases_last,Fin.lastCases_castSucc] at h
          exact False.elim (hfresh ⟨s.midpoint a,h⟩)
        · intro h
          simp only [mid,Fin.lastCases_last,Fin.lastCases_castSucc] at h
          exact congrArg Fin.castSucc (s.distinct (j.task.old.injective h))

structure StoredPattern (A : TaskObject P) (D : FullObject P X) where
  copy : TaskHom A D.task
  midpoint : ∀x y, A.order.lt x y → ∃z,
    D.task.order.lt (copy.old.point x) z ∧ D.task.order.lt z (copy.old.point y) ∧
    P.reset D.task.old (copy.old.point x) z ∧ P.reset D.task.old z (copy.old.point y)

theorem store_all_original_comparisons {R : FullAge P X} (schema : MidpointSchema R)
    (A : TaskObject P) (F : FullObject P X) (hF : R F) (initial : TaskHom A F.task) :
    ∃D, R D ∧ Nonempty (StoredPattern A D) := by
  classical
  letI : Fintype (Comparison A) := Fintype.ofFinite _
  let enumeration : Fin (Fintype.card (Comparison A)) ≃ Comparison A := (Fintype.equivFin _).symm
  obtain ⟨D,hD,⟨s⟩⟩ := store_original_comparisons schema A _ enumeration F hF initial
  refine ⟨D,hD,⟨{ copy := s.copy, midpoint := ?_ }⟩⟩
  intro x y hxy
  let i := enumeration.symm ⟨(x,y),hxy⟩
  have hi : enumeration i = ⟨(x,y),hxy⟩ := enumeration.apply_symm_apply _
  refine ⟨s.midpoint i,?_,?_,?_,?_⟩
  · simpa only [hi] using s.left i
  · simpa only [hi] using s.right i
  · simpa only [hi] using s.reset_left i
  · simpa only [hi] using s.reset_right i

def StoredPattern.map {A : TaskObject P} {D E : FullObject P X}
    (s : StoredPattern A D) (f : FullHom D E) : StoredPattern A E where
  copy := taskCompose f.task s.copy
  midpoint x y h := by
    obtain ⟨z,hl,hr,hml,hmr⟩ := s.midpoint x y h
    exact ⟨f.point z,(f.task.order_iff _ _).2 hl,(f.task.order_iff _ _).2 hr,
      (P.reset_natural f.task.old _ _).2 hml,(P.reset_natural f.task.old _ _).2 hmr⟩

end CCO.ResetOrder.Unary
