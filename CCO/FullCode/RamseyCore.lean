import CCO.FullCode.CodeTransport

/-! Exact embedding-arrow pullback. The later full-code source theorem
instantiates its correspondence by the actually constructed FCODE maps. -/
universe u v w z a b
namespace CCO.FullCode
variable {L : Language.{u}} {N : NormalForms L} {S : RootScheme L}
variable {V : Type v} {W : Type w} {Z : Type z}
variable {C : Structure L V} {D : Structure L W} {E : Structure L Z}
variable {A : Type a} {B : Type b}

/-- A color is common to composites with EVERY source embedding. -/
def HiddenArrow (C : Structure L V) (D : Structure L W) (E : Structure L Z) (k : ℕ) : Prop :=
  ∀ color : Structure.Embedding C E → Fin k,
    ∃ g : Structure.Embedding D E, ∃ shade : Fin k,
      ∀ f : Structure.Embedding C D, color (g.comp f) = shade

def VisibleArrow (O : Object C S A) (P : Object D S B) (E : Structure L Z) (k : ℕ) : Prop :=
  ∀ color : Object.Embedding N O (Object.full E S) → Fin k,
    ∃ g : Object.Embedding N P (Object.full E S), ∃ shade : Fin k,
      ∀ f : Object.Embedding N O P, color (g.comp f) = shade

/-- Internal color argument. The correspondence and its naturality must
be actually constructed, rather than supplied to the final source theorem. -/
theorem embedding_arrow_pullback (O : Object C S A) (P : Object D S B)
    (toVisibleA : Structure.Embedding O.supportStructure E →
      Object.Embedding N O (Object.full E S))
    (toVisibleB : Structure.Embedding P.supportStructure E →
      Object.Embedding N P (Object.full E S))
    (onSupport : Object.Embedding N O P →
      Structure.Embedding O.supportStructure P.supportStructure)
    (naturality : ∀ g f, (toVisibleB g).comp f = toVisibleA (g.comp (onSupport f)))
    {k : ℕ} (hidden : HiddenArrow O.supportStructure P.supportStructure E k) :
    VisibleArrow (N := N) O P E k := by
  intro color
  obtain ⟨g, shade, monochromatic⟩ := hidden (color ∘ toVisibleA)
  refine ⟨toVisibleB g, shade, ?_⟩
  intro f
  rw [naturality]
  exact monochromatic (onSupport f)

end CCO.FullCode
