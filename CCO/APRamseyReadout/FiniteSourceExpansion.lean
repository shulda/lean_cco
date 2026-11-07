import CCO.TerminalHiddenHN.RealExpansion

/-! The separate FINITE original-source branch. Name actual points by
unary predicates. Allowed assignments are all induced realizations in
that finite source; original homogeneity extends a prescribed labeling
along the SAME old embedding. No infinite-source, clone, SAP or CCO
hypothesis enters this argument. -/

universe u v w t
namespace CCO.APRamseyReadout
open CCO.TerminalHiddenHN
noncomputable section
variable {ι : Type u} {X : ι → Type v}

def finiteWhole (X : ι → Type v) [Finite (Sigma X)] : FiniteInduced (X := X) where
  vertices := Set.univ
  finite_vertices := Set.finite_univ

def finitePointInclusion (S : AtomicSource.{u,v,w} ι X) [Finite (Sigma X)]
    (A : FiniteInduced (X := X)) : InducedEmbedding S A (finiteWhole X) where
  toEmbedding := ⟨fun x => ⟨x.val,Set.mem_univ _⟩,fun _ _ h => Subtype.ext (congrArg Subtype.val h)⟩
  preserves_sort _ := rfl
  preserves_colours _ _ := rfl

def finiteLabelRestriction (S : AtomicSource.{u,v,w} ι X) [Finite (Sigma X)]
    {A B : FiniteInduced (X := X)} (f : InducedEmbedding S A B)
    (b : InducedEmbedding S B (finiteWhole X)) : InducedEmbedding S A (finiteWhole X) where
  toEmbedding := f.toEmbedding.trans b.toEmbedding
  preserves_sort x := (b.preserves_sort _).trans (f.preserves_sort x)
  preserves_colours x y := (f.preserves_colours x y).trans (b.preserves_colours _ _)

/-- All legal point labelings are induced realizations in the actual
finite original source. Label names themselves have their original sort. -/
def finiteLabelExpansion (S : AtomicSource.{u,v,w} ι X) [Finite (Sigma X)] :
    RealExpansionData.{u,v,w,max u v,max u v} S where
  Unary := Sigma X
  Binary := PEmpty.{max u v + 1}
  finiteUnary := inferInstance
  finiteBinary := inferInstance
  unarySort p := p.1
  leftSort := PEmpty.elim
  rightSort := PEmpty.elim
  Expansion A := InducedEmbedding S A (finiteWhole X)
  nonempty A := ⟨finitePointInclusion S A⟩
  unary a R x := (a.toEmbedding x).val = R
  binary a R := PEmpty.elim R
  unary_sorted a R x h :=
    (a.preserves_sort x).symm.trans (congrArg Sigma.fst h)
  binary_sorted a R := PEmpty.elim R
  faithful a b hu hb := by
    have hp : a.toEmbedding = b.toEmbedding := by
      apply Function.Embedding.ext
      intro x
      apply Subtype.ext
      exact ((hu (a.toEmbedding x).val x).mp rfl).symm
    cases a
    cases b
    cases hp
    rfl
  restrict f b := finiteLabelRestriction S f b
  restrict_unary f b R x := Iff.rfl
  restrict_binary f b R := PEmpty.elim R

/-- An expanded embedding is forced by the injective target labeling,
so every full embedding set has at most one element. -/
theorem finiteLabelEmbedding_unique (S : AtomicSource.{u,v,w} ι X) [Finite (Sigma X)]
    {A B : FiniteInduced (X := X)}
    {a : InducedEmbedding S A (finiteWhole X)} {b : InducedEmbedding S B (finiteWhole X)}
    (f g : (finiteLabelExpansion S).Embedding a b) : f = g := by
  apply RealExpansionData.Embedding.ext
  intro x
  apply b.toEmbedding.injective
  apply Subtype.ext
  have hf : (b.toEmbedding (f.old.toEmbedding x)).val = (a.toEmbedding x).val :=
    (f.unary_iff (a.toEmbedding x).val x).mpr rfl
  have hg : (b.toEmbedding (g.old.toEmbedding x)).val = (a.toEmbedding x).val :=
    (g.unary_iff (a.toEmbedding x).val x).mpr rfl
  exact hf.trans hg.symm

def finiteLabelToWhole (S : AtomicSource.{u,v,w} ι X) [Finite (Sigma X)]
    {A : FiniteInduced (X := X)} (a : InducedEmbedding S A (finiteWhole X)) :
    (finiteLabelExpansion S).Embedding a (finitePointInclusion S (finiteWhole X)) where
  old := a
  unary_iff R x := Iff.rfl
  binary_iff R := PEmpty.elim R

theorem finiteLabelExpansion_ramsey (S : AtomicSource.{u,v,w} ι X) [Finite (Sigma X)] :
    (finiteLabelExpansion S).Ramsey := by
  intro A B a b n hn
  refine ⟨finiteWhole X,finitePointInclusion S (finiteWhole X),?_⟩
  intro colour
  refine ⟨finiteLabelToWhole S b,?_⟩
  intro f g
  have he := finiteLabelEmbedding_unique S f g
  cases he
  rfl

/-- Finite homogeneity is used exactly to extend the given labels along
the prescribed OLD map. The label map is allowed to move original points. -/
theorem finiteLabelExpansion_reasonable (S : AtomicSource.{u,v,w} ι X) [Finite (Sigma X)]
    {G : Type t} [Group G] [MulAction G (Sigma X)] (H : HomogeneousSource S G) :
    (finiteLabelExpansion S).Reasonable := by
  intro A B f a
  letI : Finite A.vertices := A.finite_vertices.to_subtype
  obtain ⟨g,hg⟩ := H.extends_finite_diagram
    (fun x : A.vertices => (f.toEmbedding x).val)
    (fun x : A.vertices => (a.toEmbedding x).val)
    (fun x y => (f.preserves_colours x y).symm.trans (a.preserves_colours x y))
  let b : InducedEmbedding S B (finiteWhole X) := {
    toEmbedding := {
      toFun y := ⟨g • y.val,Set.mem_univ _⟩
      inj' := by
        intro y z h
        exact Subtype.ext (MulAction.injective g (congrArg Subtype.val h)) }
    preserves_sort y := H.preserves_sort g y.val
    preserves_colours y z := (H.preserves_colours g y.val z.val).symm }
  refine ⟨b,?_⟩
  apply (finiteLabelExpansion S).faithful
  · intro R x
    change g • (f.toEmbedding x).val = R ↔ (a.toEmbedding x).val = R
    rw [hg x]
  · intro R
    exact PEmpty.elim R

/-- B061 C59: a finite homogeneous original source admits its own finite
reasonable, precompact, reduct-surjective Ramsey labeling. This is the
separate finite branch, with no premise from the infinite clone theorem. -/
theorem finite_source_ramsey_expansion (S : AtomicSource.{u,v,w} ι X) [Finite (Sigma X)]
    {G : Type t} [Group G] [MulAction G (Sigma X)] (H : HomogeneousSource S G) :
    HasFiniteRelationalRamseyExpansion.{u,v,w,max u v,max u v} S :=
  ⟨finiteLabelExpansion S,finiteLabelExpansion_reasonable S H,finiteLabelExpansion_ramsey S⟩

end
end CCO.APRamseyReadout
