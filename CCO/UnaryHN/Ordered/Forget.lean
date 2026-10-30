import CCO.UnaryHN.OrderedAmbient

/-! Forget only the displayed order. Closed subsets and their cardinalities
are literally unchanged. An old irreducible is expanded by the ACTUAL order
relation pulled back along its given embedding, without claiming that every
expanded irreducible has irreducible reduct. -/

universe u v
namespace CCO.UnaryHN.Native
open StructuralRamsey
open StructuralRamsey.Structure

def pullDisplayedOrder {L : Language.{u}} {V W : Type v}
    (E : Structure L V) (C : Structure L.withLinearOrder W)
    (e : Embedding E C.linearOrderReduct) : Structure L.withLinearOrder V where
  rel R := by
    cases R with
    | inl R => exact E.rel R
    | inr _ => exact fun xs => C.rel (.inr ()) (e ∘ xs)
  func := E.func

def pullDisplayedOrderEmbedding {L : Language.{u}} {V W : Type v}
    {E : Structure L V} {C : Structure L.withLinearOrder W}
    (e : Embedding E C.linearOrderReduct) : Embedding (pullDisplayedOrder E C e) C where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R xs
    cases R with
    | inl R => exact e.map_rel_iff R xs
    | inr _ => exact Iff.rfl
  map_func := e.map_func

theorem pullDisplayedOrder_irreducible {L : Language.{u}} {V W : Type v}
    {E : Structure L V} {C : Structure L.withLinearOrder W}
    (e : Embedding E C.linearOrderReduct) (hE : E.Irreducible) :
    (pullDisplayedOrder E C e).Irreducible := by
  intro H X Y Z Root Left Right Target sL sR jL jR hfree f
  exact hE hfree.linearOrderReduct f.linearOrderReduct

theorem ordered_irreducibles_reduct {L : Language.{u}} {K : Class.{u,v} L}
    {V : Type v} {C : Structure L.withLinearOrder V}
    (hPieces : IrreduciblesIn (OrderedClass K) C) :
    IrreduciblesIn K C.linearOrderReduct := by
  intro X E hE e
  obtain ⟨old, o, hold, heq⟩ := hPieces (pullDisplayedOrder E C e)
    (pullDisplayedOrder_irreducible e hE) (pullDisplayedOrderEmbedding e)
  have hred := congrArg Structure.linearOrderReduct heq
  change E = old at hred
  exact hred.symm ▸ hold

theorem HE_order_reduct {L : Language.{u}} {V W : Type v}
    {C : Structure L.withLinearOrder V} {D : Structure L.withLinearOrder W}
    {f : V → W} (hf : HE C D f) : HE C.linearOrderReduct D.linearOrderReduct f := by
  constructor
  · exact ⟨fun R xs hx => hf.1.1 (.inl R) xs hx, hf.1.2⟩
  · intro X E hE e
    obtain ⟨g, hg⟩ := hf.2 (pullDisplayedOrder E C e)
      (pullDisplayedOrder_irreducible e hE) (pullDisplayedOrderEmbedding e)
    exact ⟨g.linearOrderReduct, hg⟩

theorem ordered_completion_reduct {L : Language.{u}} {K : Class.{u,v} L}
    {V : Type v} {C : Structure L.withLinearOrder V} :
    HasCompletion (OrderedClass K) C → HasCompletion K C.linearOrderReduct := by
  rintro ⟨W, hW, D, ⟨old, o, hold, rfl⟩, f, hf⟩
  exact ⟨W, hW, old, hold, f, HE_order_reduct hf⟩

theorem ordered_small_reduct {L : Language.{u}} {K : Class.{u,v} L}
    {V : Type v} {C : Structure L.withLinearOrder V} {n : ℕ}
    (h : ClosedSmallCompletable (OrderedClass K) C n) :
    ClosedSmallCompletable K C.linearOrderReduct n := by
  intro S hcard hS
  exact ordered_completion_reduct (h S hcard hS)

end CCO.UnaryHN.Native
