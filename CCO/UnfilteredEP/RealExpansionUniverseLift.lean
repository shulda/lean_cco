import CCO.UnfilteredEP.RealExpansionEP

/-! Universe enlargement of the SAME actual relational expansion. Only
the predicate names and allowed expansion values are wrapped in ULift.
Every original induced carrier, point map and interpreted predicate is
unchanged. Ramsey and EP are transferred on ALL actual embeddings. -/

universe u v w l k r s
namespace CCO.TerminalHiddenHN.RealExpansionData
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable (E : RealExpansionData.{u,v,w,l,k} S)

def universeLiftRealExpansion : RealExpansionData.{u,v,w,max l r,max k s} S where
  Unary := ULift.{r} E.Unary
  Binary := ULift.{r} E.Binary
  finiteUnary := by letI := E.finiteUnary; infer_instance
  finiteBinary := by letI := E.finiteBinary; infer_instance
  unarySort R := E.unarySort R.down
  leftSort R := E.leftSort R.down
  rightSort R := E.rightSort R.down
  Expansion A := ULift.{s} (E.Expansion A)
  nonempty A := (E.nonempty A).map ULift.up
  unary a R x := E.unary a.down R.down x
  binary a R x y := E.binary a.down R.down x y
  unary_sorted a R x h := E.unary_sorted a.down R.down x h
  binary_sorted a R x y h := E.binary_sorted a.down R.down x y h
  faithful a b hu hb := by
    apply ULift.ext
    exact E.faithful a.down b.down (fun R x => hu (ULift.up R) x)
      (fun R x y => hb (ULift.up R) x y)
  restrict f b := ULift.up (E.restrict f b.down)
  restrict_unary f b R x := E.restrict_unary f b.down R.down x
  restrict_binary f b R x y := E.restrict_binary f b.down R.down x y

/-- The equivalence retains the literal SAME old induced embedding. -/
def universeLiftEmbeddingEquiv {A B : FiniteInduced (X := X)}
    (a : E.Expansion A) (b : E.Expansion B) :
    E.Embedding a b ≃
      (universeLiftRealExpansion.{u,v,w,l,k,r,s} E).Embedding (ULift.up a) (ULift.up b) where
  toFun f := {
    old := f.old
    unary_iff R x := f.unary_iff R.down x
    binary_iff R x y := f.binary_iff R.down x y }
  invFun f := {
    old := f.old
    unary_iff R x := f.unary_iff (ULift.up R) x
    binary_iff R x y := f.binary_iff (ULift.up R) x y }
  left_inv f := by apply Embedding.ext; intro x; rfl
  right_inv f := by apply Embedding.ext; intro x; rfl

@[simp] theorem universeLiftEmbeddingEquiv_old {A B : FiniteInduced (X := X)}
    (a : E.Expansion A) (b : E.Expansion B) (f : E.Embedding a b) :
    (universeLiftEmbeddingEquiv.{u,v,w,l,k,r,s} E a b f).old = f.old := rfl

@[simp] theorem universeLiftEmbeddingEquiv_symm_old {A B : FiniteInduced (X := X)}
    (a : E.Expansion A) (b : E.Expansion B)
    (f : (universeLiftRealExpansion.{u,v,w,l,k,r,s} E).Embedding (ULift.up a) (ULift.up b)) :
    ((universeLiftEmbeddingEquiv.{u,v,w,l,k,r,s} E a b).symm f).old = f.old := rfl

@[simp] theorem universeLiftEmbeddingEquiv_comp {A B C : FiniteInduced (X := X)}
    (a : E.Expansion A) (b : E.Expansion B) (c : E.Expansion C)
    (g : E.Embedding b c) (f : E.Embedding a b) :
    universeLiftEmbeddingEquiv.{u,v,w,l,k,r,s} E a c (g.comp f) =
      (universeLiftEmbeddingEquiv.{u,v,w,l,k,r,s} E b c g).comp
        (universeLiftEmbeddingEquiv.{u,v,w,l,k,r,s} E a b f) := by
  apply Embedding.ext
  intro x
  rfl

theorem universeLift_reasonable (h : E.Reasonable) :
    (universeLiftRealExpansion.{u,v,w,l,k,r,s} E).Reasonable := by
  intro A B f a
  obtain ⟨b,hb⟩ := h A B f a.down
  refine ⟨ULift.up b,?_⟩
  apply ULift.ext
  exact hb

theorem universeLift_Ramsey (h : E.Ramsey) :
    (universeLiftRealExpansion.{u,v,w,l,k,r,s} E).Ramsey := by
  intro A B a b n hn
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  obtain ⟨C,c,arrow⟩ := h A B a b n hn
  refine ⟨C,ULift.up c,?_⟩
  intro colour
  let colour' (f : E.Embedding a c) : Fin n :=
    colour (universeLiftEmbeddingEquiv.{u,v,w,l,k,r,s} E a c f)
  obtain ⟨g,hg⟩ := arrow colour'
  refine ⟨universeLiftEmbeddingEquiv E b c g,?_⟩
  intro f₁ f₂
  let f₁' := (universeLiftEmbeddingEquiv.{u,v,w,l,k,r,s} E a b).symm f₁
  let f₂' := (universeLiftEmbeddingEquiv.{u,v,w,l,k,r,s} E a b).symm f₂
  have law₁ : universeLiftEmbeddingEquiv.{u,v,w,l,k,r,s} E a c (g.comp f₁') =
      (universeLiftEmbeddingEquiv E b c g).comp f₁ := by
    apply Embedding.ext
    intro x
    rfl
  have law₂ : universeLiftEmbeddingEquiv.{u,v,w,l,k,r,s} E a c (g.comp f₂') =
      (universeLiftEmbeddingEquiv E b c g).comp f₂ := by
    apply Embedding.ext
    intro x
    rfl
  exact (congrArg colour law₁.symm).trans ((hg f₁' f₂').trans (congrArg colour law₂))

theorem universeLift_EP (h : E.EP) :
    (universeLiftRealExpansion.{u,v,w,l,k,r,s} E).EP := by
  intro A a
  rcases a with ⟨a⟩
  obtain ⟨B,hB⟩ := h A a
  refine ⟨B,?_⟩
  intro b
  rcases b with ⟨b⟩
  obtain ⟨f⟩ := hB b
  exact ⟨universeLiftEmbeddingEquiv E a b f⟩

end CCO.TerminalHiddenHN.RealExpansionData
