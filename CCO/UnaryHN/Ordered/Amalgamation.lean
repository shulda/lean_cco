import CCO.UnaryHN.Ordered.Completion
import CCO.UnaryHN.Ordered.Shuffle

/-! Arbitrary global orders preserve heredity and strong amalgamation.
The order on an actual old strong amalgam is CONSTRUCTED by the finite
whole-base shuffle. No ordered-amalgamation provider is assumed. -/

universe u v
namespace CCO.UnaryHN.Native
open StructuralRamsey
open StructuralRamsey.Structure

theorem orderedClass_hereditary {L : Language.{u}} {K : Class.{u,v} L}
    (hK : Hereditary K) : Hereditary (OrderedClass K) := by
  intro V W C D hD e
  rcases hD with ⟨oldD, oD, hKD, rfl⟩
  let : LinearOrder W := oD
  let oV : LinearOrder V := LinearOrder.lift' e e.injective
  refine ⟨C.linearOrderReduct, oV, hK hKD e.linearOrderReduct, ?_⟩
  apply EPPABridge.native_ext
  · intro R xs
    cases R with
    | inl R => exact Iff.rfl
    | inr _ =>
      change C.rel (.inr ()) xs ↔ e (xs (0 : Fin 2)) < e (xs (1 : Fin 2))
      exact (e.map_rel_iff (.inr ()) xs).symm
  · intro F xs
    rfl

theorem orderedClass_finiteHereditarySAP {L : Language.{u}} {K : Class.{u,v} L}
    (hK : FiniteHereditarySAP K) : FiniteHereditarySAP (OrderedClass K) where
  finite := by
    rintro V C ⟨old, o, hold, rfl⟩
    exact hK.finite old hold
  singleton := by
    rintro V C ⟨old, o, hold, rfl⟩
    exact hK.singleton old hold
  hereditary := orderedClass_hereditary hK.hereditary
  strong := by
    intro H V W Root Left Right hLeft hRight sL sR
    have hRoot : OrderedClass K Root := orderedClass_hereditary hK.hereditary hLeft sL
    rcases hRoot with ⟨oldH, oH, hKH, rfl⟩
    rcases hLeft with ⟨oldL, oL, hKL, rfl⟩
    rcases hRight with ⟨oldR, oR, hKR, rfl⟩
    let : LinearOrder H := oH
    let : LinearOrder V := oL
    let : LinearOrder W := oR
    let : Finite H := hK.finite oldH hKH
    let : Finite V := hK.finite oldL hKL
    let : Finite W := hK.finite oldR hKR
    let : Fintype H := Fintype.ofFinite H
    let : Fintype V := Fintype.ofFinite V
    let : Fintype W := Fintype.ofFinite W
    obtain ⟨Z, hZ, T, hT, jL, jR, hAgree, hOverlap⟩ :=
      hK.strong hKL hKR sL.linearOrderReduct sR.linearOrderReduct
    let : Finite Z := hZ
    obtain ⟨oZ, hmonoL, hmonoR⟩ := Ordered.shuffle_orders sL sR sL.strictMono sR.strictMono
      jL jR jL.injective jR.injective hOverlap
    let : LinearOrder Z := oZ
    exact ⟨Z, hZ, T.withLinearOrder, ⟨T, oZ, hT, rfl⟩,
      withOrderEmbedding jL hmonoL, withOrderEmbedding jR hmonoR, hAgree, hOverlap⟩

end CCO.UnaryHN.Native
