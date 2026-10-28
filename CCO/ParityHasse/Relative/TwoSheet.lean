import CCO.ParityHasse.Relative.Algebra
import CCO.ParityHasse.Original.RelativeIndices
import CCO.ParityHasse.Original.Transposition

/-! Actual two-sheet geometry on real equivalence classes, independent of
exact closure separation and of the Hasse theorem. -/
universe u v w t
namespace CCO.ParityHasse.Relative
open Original

section Setoids
variable {A : Type v}
def odd (E F : Setoid A) : Rel A := fun x y => F x y ∧ ¬E x y

theorem two_other_eq {T : Type*} (h : Nat.card T = 2) (a b c : T)
    (hb : b ≠ a) (hc : c ≠ a) : b = c := by
  obtain ⟨d,hd,hu⟩ := (Nat.card_eq_two_iff' a).mp h
  exact (hu b hb).trans (hu c hc).symm

theorem odd_symmetric (E F : Setoid A) : ∀ x y, odd E F x y → odd E F y x :=
  fun _ _ h => ⟨F.symm h.1, fun he => h.2 (E.symm he)⟩

/-- Every real point has a point in the other E-class of its F-class. -/
theorem odd_serial (E F : Setoid A)
    (htwo : ∀ x, relativeIndex E F x = 2) : ∀ x, ∃ y, odd E F x y := by
  intro x
  let q : RelativeClass E F x := Quotient.mk _ ⟨x,F.refl x⟩
  obtain ⟨r,hr,_⟩ := (Nat.card_eq_two_iff' q).mp (htwo x)
  revert hr
  refine Quotient.inductionOn r ?_
  intro y hy
  exact ⟨y.val,y.property,fun h => hy (Quotient.sound (E.symm h))⟩

/-- Three real points in one F-class cannot lie in three different E-classes. -/
theorem odd_mul_subset (E F : Setoid A)
    (htwo : ∀ x, relativeIndex E F x = 2) : mul (odd E F) (odd E F) ≤ E := by
  rintro x z ⟨y,hxy,hyz⟩
  let qx : RelativeClass E F y := Quotient.mk _ ⟨x,F.symm hxy.1⟩
  let qy : RelativeClass E F y := Quotient.mk _ ⟨y,F.refl y⟩
  let qz : RelativeClass E F y := Quotient.mk _ ⟨z,hyz.1⟩
  have hx : qx ≠ qy := fun h => hxy.2 (@Quotient.exact {z // F y z} _ _ _ h)
  have hz : qz ≠ qy := fun h => hyz.2 (E.symm (@Quotient.exact {z // F y z} _ _ _ h))
  exact @Quotient.exact {z // F y z} _ _ _ (two_other_eq (htwo y) qy qx qz hx hz)

/-- Genuine two-sheet complement product, without real-point functionality. -/
theorem odd_square (E F : Setoid A) (hEF : E ≤ F)
    (htwo : ∀ x, relativeIndex E F x = 2) : mul (odd E F) (odd E F) = E := by
  funext x z; apply propext
  constructor
  · exact odd_mul_subset E F htwo x z
  · intro hxz
    obtain ⟨y,hxy⟩ := odd_serial E F htwo x
    refine ⟨y,hxy,F.trans (F.symm hxy.1) (hEF hxz),?_⟩
    intro hyz
    exact hxy.2 (E.trans hxz (E.symm hyz))

 theorem odd_bisaturated (E F : Setoid A) (hEF : E ≤ F) : Bisaturated E (odd E F) := by
  constructor <;> funext x y <;> apply propext
  · constructor
    · rintro ⟨z,hxz,hzy⟩
      exact ⟨F.trans (hEF hxz) hzy.1,fun h => hzy.2 (E.trans (E.symm hxz) h)⟩
    · intro h; exact ⟨x,E.refl x,h⟩
  · constructor
    · rintro ⟨z,hxz,hzy⟩
      exact ⟨F.trans hxz.1 (hEF hzy),fun h => hxz.2 (E.trans h (E.symm hzy))⟩
    · intro h; exact ⟨y,h,E.refl y⟩

end Setoids

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]
variable (H : HomogeneousSource S G)

include H in
/-- C21, with uniformity supplied by actual original-source transitivity. -/
theorem original_odd_square (Y U : ColourEq S i) (hYU : Y ≤ U) (a : X i)
    (htwo : relativeIndex Y.val U.val a = 2) : mul (odd Y.val U.val) (odd Y.val U.val) = Y :=
  odd_square Y.val U.val hYU (fun x => (relativeIndex_uniform S H Y U a x).symm.trans htwo)

include H in
/-- The numerical index equality comes from the actual relative-class
bijection, separately from the modular interval order isomorphism. -/
theorem maximal_transposition_index (Y U K : ColourEq S i)
    (hKU : K ⊓ U = Y) (a : X i)
    (htwo : relativeIndex Y.val U.val a = 2) :
    relativeIndex K.val (ColourEq.join S H K U).val a = 2 := by
  have hj (x y : X i) : (K.val ⊔ U.val) x y ↔ ∃ z, U x z ∧ K z y := by
    rw [sup_comm]
    exact sup_relation_iff S H U K x y
  have hh := relativeIndex_transposition K.val U.val hj a
  have he : K.val ⊓ U.val = Y.val := congrArg Subtype.val hKU
  rw [he,htwo] at hh
  exact hh.symm

end CCO.ParityHasse.Relative
