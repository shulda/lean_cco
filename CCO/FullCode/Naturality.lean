import CCO.FullCode.EmbeddingBijection

/-! Naturality of the ACTUALLY constructed full-code bijection. -/
universe u v w z a b c
namespace CCO.FullCode.Object
variable {L : Language.{u}} {N : NormalForms L} {S : RootScheme L}
variable {V : Type v} {W : Type w} {Z : Type z}
variable {C : Structure L V} {D : Structure L W} {E : Structure L Z}
variable {A : Type a} {B : Type b} {K : Type c}
variable {O : Object C S A} {P : Object D S B} {Q : Object E S K}
noncomputable section

private theorem coordinate_cast_roundtrip {s t : S.Tag} (h : s = t)
    (j : Fin (S.arity s)) :
    (h.symm ▸ (h ▸ j : Fin (S.arity t)) : Fin (S.arity s)) = j := by
  cases h
  rfl

theorem onSupport_id (hC : N.Valid C) :
    (Embedding.id N O).onSupport hC hC = Structure.Embedding.id O.supportStructure := by
  apply Structure.Embedding.ext
  intro x
  apply Subtype.ext
  obtain ⟨a, p, hx⟩ := (O.mem_support_iff_presentation N hC x.val).mp x.property
  exact (O.root a).presentation_functional N p
    ((Embedding.id N O).extendPoint_presentation hC x a p hx) hx

theorem onSupport_comp (f : Embedding N O P) (g : Embedding N P Q)
    (hC : N.Valid C) (hD : N.Valid D) (hE : N.Valid E) :
    (g.comp f).onSupport hC hE = (g.onSupport hD hE).comp (f.onSupport hC hD) := by
  apply Structure.Embedding.ext
  intro x
  apply Subtype.ext
  obtain ⟨a, p, hx⟩ := (O.mem_support_iff_presentation N hC x.val).mp x.property
  have middle := f.extendPoint_presentation hC x a p hx
  have target := g.extendPoint_presentation hD ((f.onSupport hC hD).point x) (f.point a) p middle
  exact (Q.root (g.point (f.point a))).presentation_functional N p
    ((g.comp f).extendPoint_presentation hC x a p hx) target

theorem fromHidden_comp (f : Embedding N O P) (g : Structure.Embedding P.supportStructure E)
    (hC : N.Valid C) (hD : N.Valid D) :
    (fromHidden N P g).comp f = fromHidden N O (g.comp (f.onSupport hC hD)) := by
  apply Embedding.ext
  intro a
  change (P.markedRoot (f.point a)).map g = (O.markedRoot a).map (g.comp (f.onSupport hC hD))
  apply Root.ext_coordinates (f.tag_eq a)
  intro j
  change Fin (S.arity (P.root (f.point a)).tag) at j
  apply congrArg g.point
  apply Subtype.ext
  change (P.root (f.point a)).coordinate j =
    f.extendPoint hC ⟨(O.root a).coordinate ((f.tag_eq a) ▸ j), _⟩
  rw [f.extendPoint_coordinate hC hD]
  congr 1
  change j = ((f.tag_eq a).symm ▸
    ((f.tag_eq a) ▸ j : Fin (S.arity (O.root a).tag)) : Fin (S.arity (P.root (f.point a)).tag))
  exact (coordinate_cast_roundtrip (f.tag_eq a) j).symm

end
end CCO.FullCode.Object
