import CCO.FullPhaseLift.Canonical.Source

/-! Finite definitional expansion retaining every old symbol and naming
all complete unary and distinct-pair profiles. Unrealized names interpret
as empty predicates. The distinctness guard provides actual separation. -/

universe v w
namespace CCO.FullPhaseLift.Canonical
attribute [local instance] Classical.propDecidable

private theorem cast_roundtrip {n m : ℕ} (h : n = m) (h' : m = n) (i : Fin n) :
    Fin.cast h' (Fin.cast h i) = i := Fin.ext rfl

def expansion (L : Signature) : Signature where
  size := L.size + (Fintype.card (Profile L 1) + Fintype.card (Profile L 2))
  arity := Fin.addCases L.arity (Fin.addCases (fun _ => 1) (fun _ => 2))

def oldSymbol (L : Signature) (r : Fin L.size) : Fin (expansion L).size :=
  Fin.castAdd _ r

noncomputable def unarySymbol (L : Signature) (p : Profile L 1) : Fin (expansion L).size :=
  Fin.natAdd L.size (Fin.castAdd _ ((Fintype.equivFin _) p))

noncomputable def pairSymbol (L : Signature) (p : Profile L 2) : Fin (expansion L).size :=
  Fin.natAdd L.size (Fin.natAdd _ ((Fintype.equivFin _) p))

@[simp] theorem oldSymbol_arity (L : Signature) (r : Fin L.size) :
    (expansion L).arity (oldSymbol L r) = L.arity r := by
  simp [expansion,oldSymbol]

@[simp] theorem unarySymbol_arity (L : Signature) (p : Profile L 1) :
    (expansion L).arity (unarySymbol L p) = 1 := by
  simp [expansion,unarySymbol]

@[simp] theorem pairSymbol_arity (L : Signature) (p : Profile L 2) :
    (expansion L).arity (pairSymbol L p) = 2 := by
  simp [expansion,pairSymbol]

noncomputable def expand {L : Signature} {V : Type v} (T : BoolTable L V) :
    BoolTable (expansion L) V := by
  intro r
  refine Fin.addCases (motive := fun r => (Fin ((expansion L).arity r) → V) → Bool) ?_ ?_ r
  · intro a
    let h : L.arity a = (expansion L).arity (Fin.castAdd _ a) := by simp [expansion]
    exact fun xs => T a (xs ∘ Fin.cast h)
  · intro b
    refine Fin.addCases (motive := fun b =>
      (Fin ((expansion L).arity (Fin.natAdd L.size b)) → V) → Bool) ?_ ?_ b
    · intro a
      let p := (Fintype.equivFin (Profile L 1)).symm a
      let h : 1 = (expansion L).arity (Fin.natAdd L.size (Fin.castAdd _ a)) := by simp [expansion]
      exact fun xs => decide (unaryProfile T (xs (Fin.cast h 0)) = p)
    · intro a
      let p := (Fintype.equivFin (Profile L 2)).symm a
      let h : 2 = (expansion L).arity (Fin.natAdd L.size (Fin.natAdd _ a)) := by simp [expansion]
      exact fun xs => decide (xs (Fin.cast h 0) ≠ xs (Fin.cast h 1) ∧
        pairProfile T (xs (Fin.cast h 0)) (xs (Fin.cast h 1)) = p)

@[simp] theorem expand_old {L : Signature} {V : Type v} (T : BoolTable L V)
    (r : Fin L.size) (xs : Fin (L.arity r) → V) :
    expand T (oldSymbol L r) (xs ∘ Fin.cast (oldSymbol_arity L r)) = T r xs := by
  simp [expand,oldSymbol,expansion,Function.comp_def,Fin.cast]

@[simp] theorem expand_unary {L : Signature} {V : Type v} (T : BoolTable L V)
    (p : Profile L 1) (xs : Fin 1 → V) :
    expand T (unarySymbol L p) (xs ∘ Fin.cast (unarySymbol_arity L p)) =
      decide (unaryProfile T (xs 0) = p) := by
  simp [expand,unarySymbol,expansion,Function.comp_def,Fin.cast]

@[simp] theorem expand_pair {L : Signature} {V : Type v} (T : BoolTable L V)
    (p : Profile L 2) (xs : Fin 2 → V) :
    expand T (pairSymbol L p) (xs ∘ Fin.cast (pairSymbol_arity L p)) =
      decide (xs 0 ≠ xs 1 ∧ pairProfile T (xs 0) (xs 1) = p) := by
  simp [expand,pairSymbol,expansion,Function.comp_def,Fin.cast]

noncomputable def expandEmbedding {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W} (e : Embedding A B) :
    Embedding (expand A) (expand B) := by
  apply embeddingOf e.point e.injective
  intro r xs
  cases r using Fin.addCases with
  | left a =>
    simpa only [expand,Fin.addCases_left,Function.comp_assoc] using
      embedding_read e a (xs ∘ Fin.cast (by simp [expansion]))
  | right b =>
    cases b using Fin.addCases with
    | left a =>
      simp only [expand,Fin.addCases_right,Fin.addCases_left]
      congr 1
      simp only [Function.comp_apply,unaryProfile_embedding]
    | right b =>
      simp only [expand,Fin.addCases_right]
      congr 1
      simp only [Function.comp_apply,pairProfile_embedding]
      exact propext (and_congr (not_congr e.injective.eq_iff) Iff.rfl)

noncomputable def forgetEmbedding {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W} (e : Embedding (expand A) (expand B)) :
    Embedding A B := by
  apply embeddingOf e.point e.injective
  intro r xs
  have h := embedding_read e (oldSymbol L r) (xs ∘ Fin.cast (oldSymbol_arity L r))
  simpa only [← Function.comp_assoc,expand_old] using h

noncomputable def expandIso {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W} (e : Iso A B) : Iso (expand A) (expand B) :=
  ⟨e.point,(expandEmbedding e.toEmbedding).rel_iff⟩

noncomputable def forgetIso {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W} (e : Iso (expand A) (expand B)) : Iso A B :=
  ⟨e.point,(forgetEmbedding e.toEmbedding).rel_iff⟩

@[simp] theorem forget_expandEmbedding {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W} (e : Embedding A B) :
    forgetEmbedding (expandEmbedding e) = e := by cases e; rfl

@[simp] theorem expand_forgetEmbedding {L : Signature} {V : Type v} {W : Type w}
    {A : BoolTable L V} {B : BoolTable L W} (e : Embedding (expand A) (expand B)) :
    expandEmbedding (forgetEmbedding e) = e := by cases e; rfl

/-- Every actual distinct pair has an irreflexive named positive relation. -/
theorem expand_separates {L : Signature} {V : Type v} (T : BoolTable L V)
    (x y : V) (hne : x ≠ y) :
    ∃ r : Fin (expansion L).size, ∃ slots : Fin ((expansion L).arity r) → Fin 2,
      expand T r (![x,y] ∘ slots) = true ∧ ∀ z, expand T r (fun _ => z) = false := by
  let p := pairProfile T x y
  refine ⟨pairSymbol L p,Fin.cast (pairSymbol_arity L p),?_,?_⟩
  · simp only [expand_pair,Matrix.cons_val_zero,Matrix.cons_val_one,hne,
      true_and,decide_true]
    simp [hne,p]
  · intro z
    have h := expand_pair T p ![z,z]
    have ht : ![z,z] ∘ Fin.cast (pairSymbol_arity L p) = fun _ => z := by
      funext j
      change ![z,z] (Fin.cast _ j) = z
      generalize Fin.cast (pairSymbol_arity L p) j = k
      fin_cases k <;> rfl
    rw [ht] at h
    simpa using h

end CCO.FullPhaseLift.Canonical
