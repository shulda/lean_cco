import CCO.RawExact.MixedJoins
import CCO.RawExact.Convolution

/-!
# B002 C15: fine-colour meet reconstruction, algebraic stage

In a symmetric original sort, every invariant equivalence is idempotent
and commutes with invariant RAW relations. Once the *nonempty exact*
meet-distribution provider of C10 is supplied, finite quotient colours
determine the fine K-colour. The provider is deliberately explicit:
this module does not silently assume Helly or exact convolution.
-/

universe u v w

namespace CCO.RawExact

variable {A : Type u} {G : Type v} [Group G] [MulAction G A]
variable {I : Type w}

/-- An indexed meet of ACTUAL original same-sort relations. -/
def familyMeet (E : I → A → A → Prop) : A → A → Prop :=
  fun x y => ∀ t, E t x y

theorem familyMeet_equiv (E : I → A → A → Prop)
    (hE : ∀ t, RawSymmetric.EquivRel (E t)) :
    RawSymmetric.EquivRel (familyMeet E) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x t
    exact (hE t).refl x
  · intro x y hxy t
    exact (hE t).symm x y (hxy t)
  · intro x y z hxy hyz t
    exact (hE t).trans x y z (hxy t) (hyz t)

theorem familyMeet_invariant (E : I → A → A → Prop)
    (hInv : ∀ t (g : G) x y, E t x y → E t (g • x) (g • y)) :
    ∀ (g : G) x y, familyMeet E x y →
      familyMeet E (g • x) (g • y) := by
  intro g x y hxy t
  exact hInv t g x y (hxy t)

/-- Same-sort saturation by ONE actual invariant equivalence adds
no second factor: E;R;E=E;R. True for logical identity R too. -/
theorem invariant_equiv_saturation_reduces
    (E R : A → A → Prop)
    (hE : RawSymmetric.EquivRel E)
    (invE : ∀ (g : G) x y, E x y → E (g • x) (g • y))
    (invR : ∀ (g : G) x y, R x y → R (g • x) (g • y))
    (hflip : RawSymmetric.PairFlip (G := G) (A := A)) :
    RawSymmetric.compose (RawSymmetric.compose E R) E =
      RawSymmetric.compose E R := by
  have hComm := RawSymmetric.invariant_commute R E invR invE hflip
  calc
    RawSymmetric.compose (RawSymmetric.compose E R) E =
        RawSymmetric.compose E (RawSymmetric.compose R E) :=
      raw_comp_assoc E R E
    _ = RawSymmetric.compose E (RawSymmetric.compose E R) := by
      rw [hComm]
    _ = RawSymmetric.compose (RawSymmetric.compose E E) R :=
      (raw_comp_assoc E E R).symm
    _ = RawSymmetric.compose E R := by
      rw [equiv_comp_self E hE]

/-- Algebraic part of C15. The one missing provider is precisely C10's
nonempty exact meet distribution, stated as hDistribution. No claim is
made for arbitrary invariant (non-exact) meets or an empty index family
without the stated provider. -/
theorem finite_fine_colour_from_distribution
    (E : I → A → A → Prop) (R : A → A → Prop)
    (hE : ∀ t, RawSymmetric.EquivRel (E t))
    (invE : ∀ t (g : G) x y, E t x y → E t (g • x) (g • y))
    (invR : ∀ (g : G) x y, R x y → R (g • x) (g • y))
    (hflip : RawSymmetric.PairFlip (G := G) (A := A))
    (hDistribution :
      RawSymmetric.compose (familyMeet E) R =
        (fun x y => ∀ t, RawSymmetric.compose (E t) R x y)) :
    (fun x y => ∀ t,
      RawSymmetric.compose (RawSymmetric.compose (E t) R) (E t) x y) =
    RawSymmetric.compose
      (RawSymmetric.compose (familyMeet E) R) (familyMeet E) := by
  have hSatE : ∀ t, RawSymmetric.compose
      (RawSymmetric.compose (E t) R) (E t) =
      RawSymmetric.compose (E t) R := by
    intro t
    exact invariant_equiv_saturation_reduces (E t) R
      (hE t) (invE t) invR hflip
  have hSatK : RawSymmetric.compose
      (RawSymmetric.compose (familyMeet E) R) (familyMeet E) =
      RawSymmetric.compose (familyMeet E) R :=
    invariant_equiv_saturation_reduces (familyMeet E) R
      (familyMeet_equiv E hE)
      (familyMeet_invariant E invE) invR hflip
  funext x y
  apply propext
  constructor
  · intro h
    have hK : RawSymmetric.compose (familyMeet E) R x y := by
      rw [hDistribution]
      intro t
      rw [← hSatE t]
      exact h t
    rw [hSatK]
    exact hK
  · intro h
    rw [hSatK] at h
    have hAll : ∀ t, RawSymmetric.compose (E t) R x y := by
      rw [hDistribution] at h
      exact h
    intro t
    rw [hSatE t]
    exact hAll t

end CCO.RawExact
