import CCO.PairSafeSplit.Infinity.MarkedFibres

/-! C30 finite assembly support. Infinitely many actual old same-type
points give arbitrarily many distinct simultaneous witnesses, before any
embedding into the constructed homogeneous marked limit. -/

universe u v w z l
namespace CCO.PairSafeSplit.Infinity
open RealAction
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {V : Type z} [Finite V]

/-- Delete exactly the anchor slot from an actual injective tuple. -/
def tupleBase (p : V ↪ Sigma X) (a : V) : FiniteInduced (X := X) where
  vertices := p '' {b | b ≠ a}
  finite_vertices := (Set.toFinite _).image p

theorem tupleBase_mem (p : V ↪ Sigma X) (a b : V) (hb : b ≠ a) :
    p b ∈ (tupleBase p a).vertices := ⟨b,hb,rfl⟩

theorem anchor_not_mem_tupleBase (p : V ↪ Sigma X) (a : V) :
    p a ∉ (tupleBase p a).vertices := by
  rintro ⟨b,hb,h⟩
  exact hb (p.injective h)

def tupleMarkedFibre (p : V ↪ Sigma X) (a : V) {Label : Type l}
    (mark : Sigma X → Label) : Set (Sigma X) :=
  {y | SameTypeOver S (tupleBase p a) (p a) y ∧ mark y = mark (p a)}

/-- Extend the WHOLE original tuple injectively by n fresh actual points,
all retaining the anchor's complete old type and its mark. -/
theorem exists_old_witnesses (p : V ↪ Sigma X) (a : V) {Label : Type l}
    (mark : Sigma X → Label) (hinf : (tupleMarkedFibre S p a mark).Infinite)
    (n : ℕ) :
    ∃ q : V ⊕ Fin n ↪ Sigma X,
      (∀ b, q (.inl b) = p b) ∧
      ∀ j, SameTypeOver S (tupleBase p a) (p a) (q (.inr j)) ∧
        mark (q (.inr j)) = mark (p a) := by
  let U := tupleMarkedFibre S p a mark \ Set.range p
  have hu : U.Infinite := hinf.diff (Set.finite_range p)
  let e : ℕ ↪ U := hu.natEmbedding U
  let f : Fin n ↪ Sigma X := (Fin.valEmbedding.trans e).trans (Function.Embedding.subtype U)
  have hf (j : Fin n) : f j ∈ tupleMarkedFibre S p a mark ∧ f j ∉ Set.range p :=
    (e j.val).property
  let q : V ⊕ Fin n ↪ Sigma X := {
    toFun := Sum.elim p f
    inj' := by
      intro x y h
      cases x with
      | inl b =>
        cases y with
        | inl c => exact congrArg Sum.inl (p.injective h)
        | inr j => exact False.elim ((hf j).2 ⟨b,h⟩)
      | inr j =>
        cases y with
        | inl b => exact False.elim ((hf j).2 ⟨b,h.symm⟩)
        | inr k => exact congrArg Sum.inr (f.injective h) }
  exact ⟨q,fun _ => rfl,fun j => (hf j).1⟩

noncomputable def replacePoint (p : V → Sigma X) (a : V) (y : Sigma X) : V → Sigma X := by
  classical
  exact fun b => if b = a then y else p b

/-- A complete old one-point type preserves EVERY ordered pair colour
when the anchor is replaced, including the logical diagonal. -/
theorem replacePoint_colours (p : V ↪ Sigma X) (a : V) (y : Sigma X)
    (hy : SameTypeOver S (tupleBase p a) (p a) y) (b c : V) :
    taggedColour S (p b) (p c) =
      taggedColour S (replacePoint p a y b) (replacePoint p a y c) := by
  classical
  by_cases hb : b = a <;> by_cases hc : c = a
  · subst b; subst c
    simpa [replacePoint] using hy.1
  · subst b
    simpa [replacePoint,hc] using
      hy.2.1 (p c) (tupleBase_mem p a c hc)
  · subst c
    simpa [replacePoint,hb] using
      hy.2.2 (p b) (tupleBase_mem p a b hb)
  · simp [replacePoint,hb,hc]

theorem replacePoint_marks (p : V ↪ Sigma X) (a : V) (y : Sigma X)
    {Label : Type l} (mark : Sigma X → Label) (hy : mark y = mark (p a)) (b : V) :
    mark (p b) = mark (replacePoint p a y b) := by
  classical
  by_cases hb : b = a
  · subst b
    simpa [replacePoint] using hy.symm
  · simp [replacePoint,hb]

/-- The replacement tuple remains an actual injective complete old object
when the chosen witness avoids the entire original tuple. -/
theorem replacePoint_injective (p : V ↪ Sigma X) (a : V) (y : Sigma X)
    (hy : y ∉ Set.range p) : Function.Injective (replacePoint p a y) := by
  classical
  intro b c h
  by_cases hb : b = a <;> by_cases hc : c = a
  · exact hb.trans hc.symm
  · exact False.elim (hy ⟨c,by simpa [replacePoint,hb,hc] using h.symm⟩)
  · exact False.elim (hy ⟨b,by simpa [replacePoint,hb,hc] using h⟩)
  · exact p.injective (by simpa [replacePoint,hb,hc] using h)

end CCO.PairSafeSplit.Infinity
