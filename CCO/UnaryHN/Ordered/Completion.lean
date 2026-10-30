import CCO.UnaryHN.Ordered.Forget
import CCO.UnaryHN.EPPABridge.Completion
import Mathlib.Order.WithBot

/-! Transport the displayed order along the genuine E02 injection, then
extend it on the WHOLE finite completion carrier. WithBot labels also handle
an empty ordered test target and extra completion points without choices of
representatives in the source. Reflection is required only on actual K
irreducible pieces, whose given global source orders are retained. -/

universe u v
namespace CCO.UnaryHN.Native
open StructuralRamsey
open StructuralRamsey.Structure

def transportedOrder {L : Language.{u}} {V W : Type v}
    (C : Structure L.withLinearOrder V) (D : Structure L W) (g : V → W) :
    Structure L.withLinearOrder W where
  rel R := by
    cases R with
    | inl R => exact D.rel R
    | inr _ => exact fun (xs : Fin 2 → W) =>
        ∃ x y, g x = xs 0 ∧ g y = xs 1 ∧ C.rel (.inr ()) ![x, y]
  func := D.func

theorem extend_transported_order {L : Language.{u}} {V W P : Type v}
    [Finite W] [LinearOrder P] (C : Structure L.withLinearOrder V)
    (D : Structure L W) (p : V → P)
    (hp : ∀ x y, C.rel (.inr ()) ![x, y] → p x < p y)
    (g : V → W) (hg : Function.Injective g) :
    ∃ o : LinearOrder W, ∀ x y, C.rel (.inr ()) ![x, y] →
      @LT.lt W o.toLT (g x) (g y) := by
  classical
  let label : W → WithBot P := fun z =>
    if h : ∃ x, g x = z then (p (Classical.choose h) : WithBot P) else ⊥
  have hlabel (x : V) : label (g x) = (p x : WithBot P) := by
    have hx : ∃ y, g y = g x := ⟨x, rfl⟩
    simp only [label, dite_eq_left hx]
    exact congrArg (fun y => (p y : WithBot P)) (hg (Classical.choose_spec hx))
  have hl : ∀ a b, (transportedOrder C D g).rel (.inr ()) ![a, b] → label a < label b := by
    intro a b hab
    change ∃ x y, g x = a ∧ g y = b ∧ C.rel (.inr ()) ![x, y] at hab
    obtain ⟨x, y, hx, hy, hxy⟩ := hab
    rw [← hx, ← hy, hlabel, hlabel]
    simpa using hp x y hxy
  obtain ⟨o, ho⟩ := Structure.exists_linearOrder_extension (transportedOrder C D g) label hl
  refine ⟨o, ?_⟩
  intro x y hxy
  exact ho (g x) (g y) ⟨x, y, rfl, rfl, hxy⟩

def withOrderEmbedding {L : Language.{u}} {V W : Type v}
    [LinearOrder V] [LinearOrder W] {A : Structure L V} {B : Structure L W}
    (e : Embedding A B) (hm : StrictMono e) :
    Embedding A.withLinearOrder B.withLinearOrder where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R xs
    cases R with
    | inl R => exact e.map_rel_iff R xs
    | inr _ => exact hm.lt_iff_lt
  map_func := e.map_func

theorem ordered_completion {L : Language.{u}} (hUnary : Unary L)
    {K : Class.{u,v} L} (hK : FiniteHereditarySAP K) (hIrr : AllIrreducible K)
    {V P : Type v} [Finite V] [Finite P]
    (C : Structure L.withLinearOrder V) (hSingle : C.SingletonValued)
    (D₀ : Structure L.withLinearOrder P) (hD₀ : AllOrderedModels L D₀)
    (p : V → P) (hp : HE C D₀ p)
    (hPieces : IrreduciblesIn (OrderedClass K) C)
    (hOld : HasCompletion K C.linearOrderReduct) :
    HasStrongCompletion (OrderedClass K) C := by
  obtain ⟨W, hW, D, hD, g, hg, hInjective⟩ :=
    unary_injective_completion hUnary hK hIrr C.linearOrderReduct hSingle hOld
  let : Finite W := hW
  rcases hD₀ with ⟨old₀, o₀, _hS₀, rfl⟩
  let : LinearOrder P := o₀
  have hpOrder : ∀ x y, C.rel (.inr ()) ![x, y] → p x < p y := by
    intro x y hxy
    exact hp.1.1 (.inr ()) ![x, y] hxy
  obtain ⟨o, hExt⟩ := extend_transported_order C D p hpOrder g hInjective
  let : LinearOrder W := o
  refine ⟨W, hW, D.withLinearOrder, ⟨D, o, hD, rfl⟩, g, ?_, hInjective⟩
  constructor
  · constructor
    · intro R xs hx
      cases R with
      | inl R => exact hg.1.1 R xs hx
      | inr _ =>
        have he : ![xs (0 : Fin 2), xs (1 : Fin 2)] = xs := by funext i; fin_cases i <;> rfl
        have hx' : C.rel (.inr ()) ![xs (0 : Fin 2), xs (1 : Fin 2)] := he.symm ▸ hx
        exact hExt (xs (0 : Fin 2)) (xs (1 : Fin 2)) hx'
    · exact hg.1.2
  · intro X E hE e
    obtain ⟨oldE, oE, hKE, rfl⟩ := hPieces E hE e
    let : LinearOrder X := oE
    obtain ⟨f, hf⟩ := hg.2 oldE (hIrr oldE hKE) e.linearOrderReduct
    have hm : StrictMono f := by
      intro x y hxy
      have hc := (e.map_rel_iff (.inr ()) ![x, y]).mpr hxy
      have he : e ∘ ![x, y] = ![e x, e y] := by funext i; fin_cases i <;> rfl
      have hc' : C.rel (.inr ()) ![e x, e y] :=
        Eq.mp (congrArg (C.rel (.inr ())) he) hc
      rw [hf x, hf y]
      exact hExt (e x) (e y) hc'
    exact ⟨withOrderEmbedding f hm, hf⟩

end CCO.UnaryHN.Native
