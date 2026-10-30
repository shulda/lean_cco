import CCO.FullCode.Ramsey
import CCO.FullCode.CodeLanguage

/-! The visible Ramsey conclusion on the LITERAL finite relational full
code language, using all its actual induced structure embeddings. -/
universe u v w z a b
namespace CCO.FullCode
variable {L : Language.{u}} {N : NormalForms L} {S : RootScheme L}
variable {V : Type v} {W : Type w} {Z : Type z}
variable {C : Structure L V} {D : Structure L W} {E : Structure L Z}
variable {A : Type a} {B : Type b}

theorem visible_arrow_as_code {O : Object C S A} {P : Object D S B} {k : ℕ}
    (arrow : VisibleArrow (N := N) O P E k) :
    HiddenArrow (O.codeStructure N) (P.codeStructure N)
      ((Object.full E S).codeStructure N) k := by
  intro color
  obtain ⟨g, shade, mono⟩ := arrow (fun f => color f.asCodeEmbedding)
  refine ⟨g.asCodeEmbedding, shade, ?_⟩
  intro f
  have hf := mono (Object.embeddingOfCode f)
  have compose : (g.comp (Object.embeddingOfCode f)).asCodeEmbedding =
      g.asCodeEmbedding.comp f := by
    apply Structure.Embedding.ext
    intro x
    rfl
  change color ((g.comp (Object.embeddingOfCode f)).asCodeEmbedding) = shade at hf
  rw [compose] at hf
  exact hf

/-- Actual finite visible full-code Ramsey readout. The chosen host is
fixed before ANY coloring of ALL visible induced structure embeddings. -/
theorem finite_full_code_ramsey_readout
    {H : FiniteHidden.{u,v} L → Prop} (hereditary : HereditaryHidden H)
    (normal : ∀ D, H D → N.Valid D.model) (ramsey : HasHiddenRamsey H)
    (C D : FiniteHidden.{u,v} L) (hC : H C) (hD : H D)
    (O : Object C.model S A) (P : Object D.model S B) (k : ℕ) (positive : 0 < k) :
    ∃ E : FiniteHidden.{u,v} L, H E ∧
      HiddenArrow (O.codeStructure N) (P.codeStructure N)
        ((Object.full E.model S).codeStructure N) k := by
  obtain ⟨E, hE, arrow⟩ := finite_tuple_ramsey_readout hereditary normal ramsey
    C D hC hD O P k positive
  exact ⟨E, hE, visible_arrow_as_code arrow⟩

end CCO.FullCode
