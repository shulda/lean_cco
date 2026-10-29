import CCO.SafeReadings.PrimitivePowers
import CCO.SafeReadings.PositiveOutside
import Mathlib.Logic.Function.Iterate

/-! Quantitative iteration after the central pure action has cleared.
The zeroth outside power is an absent identity ACTION, never a strong menu. -/
universe u v w t
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
namespace PositiveOutside
variable {S} {i j : ι}

def power (point : S.RealPointGluing) (P : PositiveOutside S i i) :
    Nat → PositiveOutside S i i
  | 0 => .absent _
  | n+1 => (power point P n).comp point P

@[simp] theorem power_zero (point : S.RealPointGluing) (P : PositiveOutside S i i) :
    P.power point 0 = .absent i := rfl

@[simp] theorem power_succ (point : S.RealPointGluing) (P : PositiveOutside S i i) (n) :
    P.power point (n+1) = (P.power point n).comp point P := rfl

@[simp] theorem power_absent (point : S.RealPointGluing) (n) :
    (PositiveOutside.absent i : PositiveOutside S i i).power point n = .absent i := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [power_succ, ih, comp]

 theorem power_present (point : S.RealPointGluing) (P : S.Menu i i) (hP) (n) :
    (PositiveOutside.present P hP).power point (n+1) =
      .present (loopPower S P n) (loopPower_nonempty S point P hP n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (power point (.present P hP) (n+1)).comp point (.present P hP) = _
    rw [ih]
    rfl

@[simp] theorem power_positive (point : S.RealPointGluing)
    (P : PositiveOutside S i i) {n} (hn : 0 < n) :
    (P.power point n).positive = P.positive := by
  cases P with
  | absent => simp only [power_absent, positive]
  | present P hP =>
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [power_present]; rfl

 theorem comp_loop_comm (point : S.RealPointGluing)
    (P Q : PositiveOutside S i i) : P.comp point Q = Q.comp point P := by
  cases P <;> cases Q <;> simp only [comp]
  congr 1
  exact S.loop_product_commute _ _

/-- Two outside loops act on a raw pair menu. -/
def sandwich (L : PositiveOutside S i i) (R : PositiveOutside S j j)
    (D : S.Menu i j) : S.Menu i j := L.left (right D R)

 theorem sandwich_iterate (point : S.RealPointGluing) (edge : S.RealEdgeGluing)
    (L : PositiveOutside S i i) (R : PositiveOutside S j j) (D : S.Menu i j) (n) :
    (sandwich L R)^[n] D = sandwich (L.power point n) (R.power point n) D := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [sandwich, power_succ]
    rw [← left_right edge, right_comp point edge, ← left_comp point edge,
      comp_loop_comm point L (L.power point n)]

variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]

/-- A positive loop sandwich fills EVERY nonempty raw menu after 2m0
iterations, independently of exactness of that input or its outside factors. -/
theorem sandwich_iterate_full (H : HomogeneousSource S G)
    (primitive : SortwisePrimitive S) (point : S.RealPointGluing) (edge : S.RealEdgeGluing)
    (L : PositiveOutside S i i) (R : PositiveOutside S j j)
    (hpos : (L.positive || R.positive) = true)
    (m0 : Nat) (hm0 : 0 < m0)
    (hi : Nat.card (S.Atom i i) ≤ m0) (hj : Nat.card (S.Atom j j) ≤ m0)
    (D : S.Menu i j) (hD : D.Nonempty) :
    (sandwich L R)^[2*m0] D = Set.univ := by
  rw [sandwich_iterate point edge]
  cases L with
  | absent =>
    cases R with
    | absent => cases hpos
    | present R hR =>
      have hn : 2*m0 = (2*m0-1)+1 := by omega
      rw [hn, power_present, power_absent]
      change S.product D (loopPower S R (2*m0-1)) = Set.univ
      rw [primitive_loopPower_full_of_le S H primitive point edge R hR _ (by omega)]
      exact S.product_top_of_point_gluing point D hD
  | present L hL =>
    have hn : 2*m0 = (2*m0-1)+1 := by omega
    rw [hn, power_present]
    change S.product (loopPower S L (2*m0-1)) (right D _) = Set.univ
    rw [primitive_loopPower_full_of_le S H primitive point edge L hL _ (by omega)]
    exact S.top_product_of_point_gluing point _ (right_nonempty point hD _)

end PositiveOutside
end CCO.SafeReadings
