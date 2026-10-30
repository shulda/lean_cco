import CCO.UnaryHN.EPPABridge.Homomorphism

/-! Genuine HN unary injectivization from the accepted EPPA completion
theorem. The transported class consists of actual decoded members with ONE
fixed nullary profile, not a class-completion or representation callback. -/

universe u v
namespace CCO.UnaryHN.Native.EPPABridge
open StructuralRamsey
open StructuralRamsey.Structure

def encodeDecodedEmbedding {L : Language.{u}} {V W : Type v}
    (P : NullaryProfile L) {A : AllThoseEPPA.Structure (positiveLanguage L) V}
    {B : Structure L W} (e : Embedding (decode P A) B) :
    AllThoseEPPA.Structure.Embedding (trivialAction L) A (encode B) where
  lang := PUnit.unit
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro n ⟨R, hR, hp⟩ xs
    subst n
    change B.rel R (e.toFun ∘ xs) ↔ A.rel ⟨R, rfl, hp⟩ xs
    simpa only [decode, dite_eq_left hp] using e.map_rel_iff R xs
  map_func := by
    intro n ⟨F, hF⟩ xs
    subst n
    exact e.map_func F xs

def profileClass {L : Language.{u}} [ (positiveLanguage L).HasUnaryFunctions ]
    {K : Class.{u,v} L} (hK : FiniteHereditarySAP K) (P : NullaryProfile L) :
    AllThoseEPPA.TreeLike.HereditaryFiniteStrongAmalgamationClass (trivialAction L) where
  mem A := K (decode P A)
  finite_of_mem A hA := hK.finite (decode P A) hA
  hereditary e hB := hK.hereditary hB (decodeEmbedding P e)
  strong_amalgamate := by
    intro I X Y D B₁ B₂ f g _hD hB₁ hB₂
    obtain ⟨Z, hZ, T, hT, jL, jR, hAgree, hOverlap⟩ :=
      hK.strong hB₁ hB₂ (decodeEmbedding P f) (decodeEmbedding P g)
    have hPT : HasProfile T P := embedding_profile jL (decode_hasProfile P B₁)
    refine ⟨Z, hZ, encode T, ?_, encodeDecodedEmbedding P jL,
      encodeDecodedEmbedding P jR, ?_, ?_⟩
    · change K (decode P (encode T))
      rw [decode_encode hPT]
      exact hT
    · apply AllThoseEPPA.Structure.Embedding.ext_of_lang_toFun (trivialAction L)
      · exact Subsingleton.elim _ _
      · exact funext hAgree
    · intro x y hxy
      obtain ⟨z, hx, hy⟩ := hOverlap x y hxy
      exact ⟨z, hx.symm, hy.symm⟩

theorem unary_completionIffStrong {L : Language.{u}} (hUnary : Unary L)
    {K : Class.{u,v} L} (hK : FiniteHereditarySAP K)
    {V : Type v} [Finite V] (C : Structure L V) :
    HasCompletion K C ↔ HasStrongCompletion K C := by
  constructor
  · rintro ⟨W, hW, D, hD, f, hf⟩
    letI : (positiveLanguage L).HasUnaryFunctions := unaryInstance hUnary
    let P := actualProfile C
    let KP := profileClass hK P
    have hPC : HasProfile C P := has_actualProfile C
    have hPD : HasProfile D P := HE_profile hUnary hf
    have hKD : KP.mem (encode D) := by
      change K (decode P (encode D))
      rw [decode_encode hPD]
      exact hD
    have hComp : KP.toAmalgamationClass.HasCompletion (encode C) :=
      ⟨W, hW, encode D, hKD, encodeHom hf.1, encodeHE hf⟩
    obtain ⟨X, hX, B, hB, g, hg, hInjective⟩ :=
      (AllThoseEPPA.MainTheorems.completionIffStrong (trivialAction L) KP (encode C)).mp hComp
    have hMaps : ∃ g' : AllThoseEPPA.Structure.Homomorphism (trivialAction L)
        (encode C) (encode (decode P B)),
        AllThoseEPPA.Structure.Homomorphism.IsHomomorphismEmbedding (trivialAction L) g' ∧
        Function.Injective g'.toFun := by
      rw [encode_decode P B]
      exact ⟨g, hg, hInjective⟩
    obtain ⟨g', hg', hInj⟩ := hMaps
    exact ⟨X, hX, decode P B, hB, g'.toFun,
      decodeHE hPC (decode_hasProfile P B) g' hg', hInj⟩
  · exact HasStrongCompletion.to_completion

end CCO.UnaryHN.Native.EPPABridge

namespace CCO.UnaryHN.Native
open StructuralRamsey

/-- HN Proposition2.6 in the exact source class and partial-unary setting.
The obstruction bound, ambient Ramsey theorem and ordered transfer play no
part in this independent provider. Strong means globally injective HE. -/
theorem unary_injective_completion {L : Language.{u}} (hUnary : Unary L)
    {K : Class.{u,v} L} (hK : FiniteHereditarySAP K) (_hIrr : AllIrreducible K)
    {V : Type v} [Finite V] (C : Structure L V) (_hC : C.SingletonValued) :
    HasCompletion K C → HasStrongCompletion K C :=
  (EPPABridge.unary_completionIffStrong hUnary hK C).mp

end CCO.UnaryHN.Native
