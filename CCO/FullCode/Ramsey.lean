import CCO.FullCode.RamseyAge
import CCO.FullCode.Naturality
import CCO.FullCode.Cofinality

/-! The full tuple code transfers the supplied hidden EMBEDDING Ramsey
property. Every FCODE and naturality input below is actually constructed.
The hidden witness may contain orphans; no root cover, EP or SAP is used. -/
universe u v w z a b
namespace CCO.FullCode
variable {L : Language.{u}} {N : NormalForms L} {S : RootScheme L}
variable {V : Type v} {W : Type w} {Z : Type z}
variable {C : Structure L V} {D : Structure L W} {E : Structure L Z}
variable {A : Type a} {B : Type b}

/-- C17--C19: actual full-code maps color ALL hidden embeddings and
identify every composite through the proved presentation naturality. -/
theorem full_code_arrow (O : Object C S A) (P : Object D S B)
    (hC : N.Valid C) (hD : N.Valid D) {k : ℕ}
    (hidden : HiddenArrow O.supportStructure P.supportStructure E k) :
    VisibleArrow (N := N) O P E k :=
  embedding_arrow_pullback O P (Object.fromHidden N O) (Object.fromHidden N P)
    (fun f => f.onSupport hC hD) (fun g f => Object.fromHidden_comp f g hC hD) hidden

/-- C16--C20 and the source Ramsey export. Actual heredity supplies both
finite generated supports; hidden Ramsey fixes ONE finite host before the
visible coloring. Empty/zero-coordinate roots use the same proof. -/
theorem finite_tuple_ramsey_readout
    {H : FiniteHidden.{u,v} L → Prop} (hereditary : HereditaryHidden H)
    (normal : ∀ D, H D → N.Valid D.model) (ramsey : HasHiddenRamsey H)
    (C D : FiniteHidden.{u,v} L) (hC : H C) (hD : H D)
    (O : Object C.model S A) (P : Object D.model S B) (k : ℕ) (positive : 0 < k) :
    ∃ E : FiniteHidden.{u,v} L, H E ∧
      VisibleArrow (N := N) O P E.model k := by
  obtain ⟨E, hE, hidden⟩ := ramsey (C.support O) (D.support P)
    (support_in_hidden_age hereditary C hC O)
    (support_in_hidden_age hereditary D hD P) k positive
  exact ⟨E, hE, full_code_arrow O P (normal C hC) (normal D hD) hidden⟩

end CCO.FullCode
