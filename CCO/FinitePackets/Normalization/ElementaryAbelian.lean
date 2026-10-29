import CCO.FinitePackets.Normalization.Translations
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! The finite exponent-two group is literally isomorphic to F2^d, including
the trivial group d=0.  This chooses a group basis, never packet origins. -/
universe v w t
namespace CCO.FinitePackets.Normalization
open CCO.RealHull.Geometry CCO.ParityHasse.Original

theorem finite_exponent_two_coordinates (K : Type v) [CommGroup K] [Finite K]
    (hsquare : ∀ k : K, k * k = 1) :
    ∃ d : Nat, Nonempty (K ≃* Multiplicative (Fin d → ZMod 2)) ∧ Nat.card K = 2^d := by
  letI : Module (ZMod 2) (Additive K) := AddCommGroup.zmodModule (n := 2) (by
    intro x
    rw [two_nsmul]
    change x.toMul * x.toMul = 1
    exact hsquare x.toMul)
  letI : Module.Finite (ZMod 2) (Additive K) := inferInstance
  let d := Module.finrank (ZMod 2) (Additive K)
  let b := Module.finBasis (ZMod 2) (Additive K)
  let e : K ≃* Multiplicative (Fin d → ZMod 2) :=
    AddEquiv.toMultiplicativeRight b.equivFun.toAddEquiv
  refine ⟨d,⟨e⟩,?_⟩
  calc
    Nat.card K = Nat.card (Multiplicative (Fin d → ZMod 2)) := Nat.card_congr e.toEquiv
    _ = 2^d := by simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,
      Fintype.card_fun,Fintype.card_fin,ZMod.card]

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable (F : ColourEq S ()) {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G) (hthin : ThinBottom S F)
include H hthin

theorem translation_elementary_abelian :
    ∃ d : Nat, Nonempty (Translation S F G ≃* Multiplicative (Fin d → ZMod 2)) ∧
      Nat.card (Translation S F G) = 2^d := by
  letI := translationCommGroup S F H hthin
  letI := translation_finite S F H hthin
  exact finite_exponent_two_coordinates _ (translation_square S F H hthin)

theorem packet_size_power_two (x : M) :
    ∃ d : Nat, Nat.card {y : M // F x y} = 2^d ∧
      Nonempty (Translation S F G ≃* Multiplicative (Fin d → ZMod 2)) := by
  obtain ⟨d,he,hcard⟩ := translation_elementary_abelian S F H hthin
  exact ⟨d,(Nat.card_congr (packetTranslationEquiv S F H hthin x)).symm.trans hcard,he⟩

end CCO.FinitePackets.Normalization
