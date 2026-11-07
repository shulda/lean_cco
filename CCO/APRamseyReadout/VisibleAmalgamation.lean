import CCO.TerminalHiddenHN.RealExpansion

/-! The direct embedding-colouring argument for ordinary AP. The
Ramsey and JEP premises concern the SAME actual expanded class. The
conclusion gives a commuting span, with no strong-intersection claim. -/

universe u v w l k
namespace CCO.APRamseyReadout
open CCO.TerminalHiddenHN
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable (E : RealExpansionData.{u,v,w,l,k} S)

def ExpandedJEP : Prop :=
  ∀ (A B : FiniteInduced (X := X)) (a : E.Expansion A) (b : E.Expansion B),
    ∃ (C : FiniteInduced (X := X)) (c : E.Expansion C),
      Nonempty (E.Embedding a c) ∧ Nonempty (E.Embedding b c)

def ExpandedAP : Prop :=
  ∀ (A B₁ B₂ : FiniteInduced (X := X))
    (a : E.Expansion A) (b₁ : E.Expansion B₁) (b₂ : E.Expansion B₂)
    (f₁ : E.Embedding a b₁) (f₂ : E.Embedding a b₂),
    ∃ (C : FiniteInduced (X := X)) (c : E.Expansion C)
      (g₁ : E.Embedding b₁ c) (g₂ : E.Embedding b₂ c),
        g₁.comp f₁ = g₂.comp f₂

theorem expandedEmbedding_comp_assoc {A B C D : FiniteInduced (X := X)}
    {a : E.Expansion A} {b : E.Expansion B} {c : E.Expansion C} {d : E.Expansion D}
    (h : E.Embedding c d) (g : E.Embedding b c) (f : E.Embedding a b) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply RealExpansionData.Embedding.ext
  intro x
  rfl

/-- C31. Colour an A-embedding by whether it extends the prescribed
B₁ map. A joint host contains such a map, so its monochromatic Ramsey
image makes the prescribed B₂ map extendible as well. -/
theorem expandedAP_of_ramsey_jep (ramsey : E.Ramsey) (jep : ExpandedJEP E) :
    ExpandedAP E := by
  classical
  intro A B₁ B₂ a b₁ b₂ f₁ f₂
  obtain ⟨J,j,⟨j₁⟩,⟨j₂⟩⟩ := jep B₁ B₂ b₁ b₂
  obtain ⟨C,c,hC⟩ := ramsey A J a j 2 (by decide)
  let colour (h : E.Embedding a c) : Fin 2 :=
    if ∃ g : E.Embedding b₁ c, g.comp f₁ = h then 0 else 1
  obtain ⟨q,hq⟩ := hC colour
  have hFirst : ∃ g : E.Embedding b₁ c, g.comp f₁ = q.comp (j₁.comp f₁) :=
    ⟨q.comp j₁,expandedEmbedding_comp_assoc E q j₁ f₁⟩
  have hZero : colour (q.comp (j₁.comp f₁)) = 0 := by
    simp [colour,hFirst]
  have hMono := hq (j₁.comp f₁) (j₂.comp f₂)
  have hSecondZero : colour (q.comp (j₂.comp f₂)) = 0 := hMono.symm.trans hZero
  have hSecond : ∃ g : E.Embedding b₁ c, g.comp f₁ = q.comp (j₂.comp f₂) := by
    by_cases h : ∃ g : E.Embedding b₁ c, g.comp f₁ = q.comp (j₂.comp f₂)
    · exact h
    · have hOne : colour (q.comp (j₂.comp f₂)) = 1 := by simp [colour,h]
      have hFalse : (0 : Fin 2) = 1 := hSecondZero.symm.trans hOne
      exact False.elim ((by decide : (0 : Fin 2) ≠ 1) hFalse)
  obtain ⟨g,hg⟩ := hSecond
  exact ⟨C,c,g,q.comp j₂,hg.trans (expandedEmbedding_comp_assoc E q j₂ f₂).symm⟩

end CCO.APRamseyReadout
