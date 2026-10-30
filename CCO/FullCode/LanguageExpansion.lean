import CCO.FullCode.Roots
import CCO.FullCode.StructureTransport

/-! Ordinary expansions keep the sort set, up to its specified renaming.
Old qf root formulas then have a constructed, literal expanded reading. -/
universe u v
namespace CCO.FullCode
variable {L₀ L₁ : Language.{u}} {V : Type v}

structure LanguageExpansion (L₀ L₁ : Language.{u}) extends Reduct L₀ L₁ where
  sortEquiv : L₁.Sorts ≃ L₀.Sorts
  sort_eq : ∀ s, sortEquiv s = sortMap s

namespace LanguageExpansion
variable (ρ : LanguageExpansion L₀ L₁)

def up (s : L₀.Sorts) : L₁.Sorts := ρ.sortEquiv.symm s

theorem input_lift (F : L₀.Func) : L₁.input (ρ.funcMap F) = ρ.up (L₀.input F) := by
  apply ρ.sortEquiv.injective
  rw [ρ.sort_eq, ρ.input_eq]
  exact (ρ.sortEquiv.apply_symm_apply _).symm

theorem output_lift (F : L₀.Func) : L₁.output (ρ.funcMap F) = ρ.up (L₀.output F) := by
  apply ρ.sortEquiv.injective
  rw [ρ.sort_eq, ρ.output_eq]
  exact (ρ.sortEquiv.apply_symm_apply _).symm

theorem unary_lift (U : L₀.Unary) : L₁.unarySort (ρ.unaryMap U) = ρ.up (L₀.unarySort U) := by
  apply ρ.sortEquiv.injective
  rw [ρ.sort_eq, ρ.unary_eq]
  exact (ρ.sortEquiv.apply_symm_apply _).symm

theorem left_lift (R : L₀.Binary) : L₁.leftSort (ρ.binaryMap R) = ρ.up (L₀.leftSort R) := by
  apply ρ.sortEquiv.injective
  rw [ρ.sort_eq, ρ.left_eq]
  exact (ρ.sortEquiv.apply_symm_apply _).symm

theorem right_lift (R : L₀.Binary) : L₁.rightSort (ρ.binaryMap R) = ρ.up (L₀.rightSort R) := by
  apply ρ.sortEquiv.injective
  rw [ρ.sort_eq, ρ.right_eq]
  exact (ρ.sortEquiv.apply_symm_apply _).symm

end LanguageExpansion

def Term.retype {L : Language.{u}} {s t s' t' : L.Sorts}
    (hs : s = s') (ht : t = t') (q : Term L s t) : Term L s' t' := hs ▸ ht ▸ q

theorem Term.eval_retype {L : Language.{u}} {s t s' t' : L.Sorts}
    (hs : s = s') (ht : t = t') (q : Term L s t) (C : Structure L V) (x : V) :
    (q.retype hs ht).eval C x = q.eval C x := by cases hs; cases ht; rfl

def Term.lift (ρ : LanguageExpansion L₀ L₁) :
    {s t : L₀.Sorts} → Term L₀ s t → Term L₁ (ρ.up s) (ρ.up t)
  | _, _, .id s => .id (ρ.up s)
  | _, _, .app F q =>
    (Term.app (ρ.funcMap F) ((q.lift ρ).retype rfl (ρ.input_lift F).symm)).retype rfl (ρ.output_lift F)

theorem Term.eval_lift (ρ : LanguageExpansion L₀ L₁) (C : Structure L₁ V)
    {s t : L₀.Sorts} (q : Term L₀ s t) (x : V) :
    (q.lift ρ).eval C x = q.eval (C.reduct ρ.toReduct) x := by
  induction q with
  | id => rfl
  | app F q ih =>
    simp only [lift, eval_retype, eval, ih]
    rfl

def CoordinateTerm.retype {L : Language.{u}} {n : ℕ} {ctx : Fin n → L.Sorts}
    {s t : L.Sorts} (h : s = t) (a : CoordinateTerm L ctx s) : CoordinateTerm L ctx t :=
  ⟨a.1, a.2.retype rfl h⟩

def CoordinateTerm.lift (ρ : LanguageExpansion L₀ L₁) {n : ℕ} {ctx : Fin n → L₀.Sorts}
    {s : L₀.Sorts} (a : CoordinateTerm L₀ ctx s) :
    CoordinateTerm L₁ (fun j => ρ.up (ctx j)) (ρ.up s) := ⟨a.1, a.2.lift ρ⟩

theorem CoordinateTerm.eval_lift (ρ : LanguageExpansion L₀ L₁) (C : Structure L₁ V)
    {n : ℕ} {ctx : Fin n → L₀.Sorts} {s : L₀.Sorts} (a : CoordinateTerm L₀ ctx s)
    (xs : Fin n → V) : (a.lift ρ).eval C xs = a.eval (C.reduct ρ.toReduct) xs :=
  a.2.eval_lift ρ C _

theorem CoordinateTerm.eval_retype {L : Language.{u}} (C : Structure L V)
    {n : ℕ} {ctx : Fin n → L.Sorts} {s t : L.Sorts} (h : s = t)
    (a : CoordinateTerm L ctx s) (xs : Fin n → V) :
    (a.retype h).eval C xs = a.eval C xs := a.2.eval_retype rfl h C _

def Formula.lift (ρ : LanguageExpansion L₀ L₁) {n : ℕ} {ctx : Fin n → L₀.Sorts} :
    Formula L₀ ctx → Formula L₁ (fun j => ρ.up (ctx j))
  | .truth => .truth
  | .equal a b => .equal (a.lift ρ) (b.lift ρ)
  | .unary U a => .unary (ρ.unaryMap U) ((a.lift ρ).retype (ρ.unary_lift U).symm)
  | .binary R a b => .binary (ρ.binaryMap R) ((a.lift ρ).retype (ρ.left_lift R).symm)
      ((b.lift ρ).retype (ρ.right_lift R).symm)
  | .neg p => .neg (p.lift ρ)
  | .conj p q => .conj (p.lift ρ) (q.lift ρ)

theorem Formula.eval_lift (ρ : LanguageExpansion L₀ L₁) (C : Structure L₁ V)
    {n : ℕ} {ctx : Fin n → L₀.Sorts} (p : Formula L₀ ctx) (xs : Fin n → V) :
    (p.lift ρ).eval C xs ↔ p.eval (C.reduct ρ.toReduct) xs := by
  induction p with
  | truth => exact Iff.rfl
  | equal a b => simp only [lift, eval, CoordinateTerm.eval_lift]
  | unary U a => simp only [lift, eval, CoordinateTerm.eval_retype, CoordinateTerm.eval_lift]; rfl
  | binary R a b => simp only [lift, eval, CoordinateTerm.eval_retype, CoordinateTerm.eval_lift]; rfl
  | neg p ih => exact not_congr ih
  | conj p q hp hq => exact and_congr hp hq

def RootScheme.lift (S : RootScheme L₀) (ρ : LanguageExpansion L₀ L₁) : RootScheme L₁ where
  Tag := S.Tag
  finiteTag := S.finiteTag
  arity := S.arity
  coordinateSort tag j := ρ.up (S.coordinateSort tag j)
  delta tag := (S.delta tag).lift ρ

def Root.toOld (ρ : LanguageExpansion L₀ L₁) {C : Structure L₁ V} {S : RootScheme L₀}
    (r : Root C (S.lift ρ)) : Root (C.reduct ρ.toReduct) S where
  tag := r.tag
  coordinate := r.coordinate
  sorted j := by
    change ρ.sortMap (C.sort (r.coordinate j)) = S.coordinateSort r.tag j
    rw [← ρ.sort_eq, r.sorted j]
    exact ρ.sortEquiv.apply_symm_apply _
  valid := ((S.delta r.tag).eval_lift ρ C r.coordinate).mp r.valid

def Root.toExpanded (ρ : LanguageExpansion L₀ L₁) {C : Structure L₁ V} {S : RootScheme L₀}
    (r : Root (C.reduct ρ.toReduct) S) : Root C (S.lift ρ) where
  tag := r.tag
  coordinate := r.coordinate
  sorted j := by
    apply ρ.sortEquiv.injective
    rw [ρ.sort_eq]
    exact (r.sorted j).trans (ρ.sortEquiv.apply_symm_apply _).symm
  valid := ((S.delta r.tag).eval_lift ρ C r.coordinate).mpr r.valid

def Root.expansionEquiv (ρ : LanguageExpansion L₀ L₁) (C : Structure L₁ V) (S : RootScheme L₀) :
    Root C (S.lift ρ) ≃ Root (C.reduct ρ.toReduct) S where
  toFun := Root.toOld ρ
  invFun := Root.toExpanded ρ
  left_inv r := by cases r; rfl
  right_inv r := by cases r; rfl

end CCO.FullCode
