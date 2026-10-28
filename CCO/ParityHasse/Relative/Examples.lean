import CCO.ParityHasse.Relative.Source

/-! Boundary consumers and a genuine real/nonfunctional two-sheet control.
The finite control asserts relation algebra only, not a CCO source instance. -/
universe u v w t
namespace CCO.ParityHasse.Relative

section Boundaries
variable {A : Type v}
theorem kernel_power (K : Setoid A) : ∀ n, power K K n = K
  | 0 => rfl
  | n+1 => by rw [power_succ,kernel_power K n,(bisaturated_self K).1]

theorem kernel_closure (K : Setoid A) : closure K K = K := by
  funext x y; apply propext
  constructor
  · rintro ⟨n,hn⟩; rwa [kernel_power K n] at hn
  · intro h; exact ⟨0,h⟩

theorem nontrivial_kernel_zero (K : Setoid A) (R : Rel A) (x y : A)
    (hxy : K x y) : power K R 0 x y := hxy

/-- Even an empty word in the quotient pulls back to the WHOLE kernel. -/
theorem empty_quotient_word (G : Type t) [Group G] {Q : Type*} [MulAction G Q]
    (π : A → Q) :
    pull π (OrbitalWord.relation G Q (.nil : OrbitalWord Q)) = GroupActions.kernel π := rfl

/-- Empty restrictions mean full Top, not zero; no compactness is involved. -/
theorem empty_quotient_restrictions (G : Type t) [Group G] {Q : Type*} [MulAction G Q]
    (x y : Q) : orbitalEvaluate G Q [] x y := by simp [orbitalEvaluate]
end Boundaries

namespace TwoSheets
abbrev Point := Bool × Fin 3

def kernel : Setoid Point :=
  ⟨fun x y => x.1 = y.1,⟨fun _ => rfl,fun h => h.symm,fun h k => h.trans k⟩⟩

def relation : Rel Point := fun x y => x.1 ≠ y.1

theorem saturated : Bisaturated kernel relation := by
  constructor <;> funext x y <;> apply propext
  · constructor
    · rintro ⟨z,hxz,hzy⟩ hxy
      exact hzy (hxz.symm.trans hxy)
    · intro h; exact ⟨x,rfl,h⟩
  · constructor
    · rintro ⟨z,hxz,hzy⟩ hxy
      exact hxz (hxy.trans hzy.symm)
    · intro h; exact ⟨y,h,rfl⟩

theorem square : mul relation relation = kernel := by
  funext x y; apply propext
  constructor
  · rintro ⟨z,hxz,hzy⟩
    change x.1 = y.1
    cases hx : x.1 <;> cases hy : y.1 <;> cases hz : z.1 <;>
      simp_all [relation]
  · intro hxy
    refine ⟨(Bool.not x.1,0),?_,?_⟩
    · change x.1 ≠ !x.1
      cases x.1 <;> decide
    · change (!x.1) ≠ y.1
      change x.1 = y.1 at hxy
      rw [← hxy]
      cases x.1 <;> decide

/-- There are genuinely distinct real successors in one opposite K-class. -/
theorem not_real_functional : ∃ x y z : Point,
    relation x y ∧ relation x z ∧ y ≠ z := by
  refine ⟨(false,0),(true,0),(true,1),by change false ≠ true; decide,by change false ≠ true; decide,?_⟩
  decide

/-- A NONTRIVIAL kernel-zero pair is retained literally in relative powers. -/
theorem zero_retains_whole_kernel :
    power kernel relation 0 (false,0) (false,1) ∧ ((false,0) : Point) ≠ (false,1) := by
  exact ⟨rfl,by decide⟩

def classEquivBool : Quotient kernel ≃ Bool where
  toFun := Quotient.lift (fun x : Point => x.1) (fun _ _ h => h)
  invFun b := Quotient.mk kernel (b,0)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ x => exact Quotient.sound rfl
  right_inv _ := rfl

theorem exactly_two_classes : Nat.card (Quotient kernel) = 2 := by
  rw [Nat.card_congr classEquivBool]
  simp only [Nat.card_eq_fintype_card,Fintype.card_bool]

/-- The ACTUAL quotient relation is the graph of Bool.not. -/
theorem quotient_graph (b c : Bool) : imageRelation Prod.fst relation b c ↔ (!b) = c := by
  constructor
  · rintro ⟨x,y,hx,hy,hxy⟩
    change x.1 ≠ y.1 at hxy
    rw [hx,hy] at hxy
    cases b <;> cases c <;> simp_all
  · intro h
    refine ⟨(b,0),(c,0),rfl,rfl,?_⟩
    change b ≠ c
    rw [← h]
    cases b <;> decide

end TwoSheets
end CCO.ParityHasse.Relative
