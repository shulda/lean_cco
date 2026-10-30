import CCO.APCharacter.SourceAge.Reduct
import CCO.APCharacter.SourceAge.UnarySourceHomogeneity
import CCO.APCharacter.Towers.UnaryReduct

/-! The actual canonical split supplies the concrete finite-age unary
forgetful functor and its SAME-map lifting, surjectivity and finite fibres. -/
universe u v w t
namespace CCO.APCharacter.SourceAge
open OwnerTransversal.CountableColour
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {M : MaskData S}
variable {completion : Age.CompletionProperty S M}
noncomputable section
variable (I : UnarySource.Identification S H completion)

def actualProjection : Towers.UnaryReduct S (UnarySource.source I) where
  parent c := c.1
  point _ x := x.val
  atom _ _ a := a.val
  atom_injective _ _ := Subtype.coe_injective
  colour c d x y := (Rank.colour_map S (UnarySource.β I) (UnarySource.tag I) x y).symm
  bijective := (UnarySource.oldEquiv I).bijective

theorem projection_owner (p : UnarySource.NewPoint I) :
    (actualProjection I).projectedTable.owner p =
      (reductTable S H completion).owner (UnarySource.newEquiv I p) :=
  (I.owner_sort ((UnarySource.oldEquiv I) p)).symm

theorem projection_colour (p q : UnarySource.NewPoint I) :
    (actualProjection I).projectedTable.colour p q =
      (reductTable S H completion).colour (UnarySource.newEquiv I p) (UnarySource.newEquiv I q) :=
  (I.colour_eq ((UnarySource.oldEquiv I) p) ((UnarySource.oldEquiv I) q)).symm

/-- The actual old-to-limit extension theorem is transported through the
actual whole-carrier equivalence, retaining the exact prescribed base map. -/
theorem actual_extension (seeds : M.FiniteSeedExtension) :
    FiniteExtension (Towers.UnaryReduct.originalTable (S := S)) (actualProjection I).projectedTable := by
  intro n m j p q ⟨ho,hc⟩
  let E := UnarySource.newEquiv I
  let qL := q.trans E.toEmbedding
  have hoL : ∀ x, (reductTable S H completion).owner (qL x) = (originalTable S).owner (p (j x)) := by
    intro x
    exact (projection_owner I (q x)).symm.trans (ho x)
  have hcL : ∀ x y, (reductTable S H completion).colour (qL x) (qL y) =
      (originalTable S).colour (p (j x)) (p (j y)) := by
    intro x y
    exact (projection_colour I (q x) (q y)).symm.trans (hc x y)
  obtain ⟨r,hrO,hrC,hr⟩ := forth_extension S H completion seeds n m j p qL ⟨hoL,hcL⟩
  let rN := r.trans E.symm.toEmbedding
  have hE (x : Fin m) : E (rN x) = r x := E.apply_symm_apply _
  refine ⟨rN,?_,?_,?_⟩
  · intro x
    exact (projection_owner I (rN x)).trans ((congrArg (reductTable S H completion).owner (hE x)).trans (hrO x))
  · intro x y
    exact (projection_colour I (rN x) (rN y)).trans
      ((congrArg₂ (reductTable S H completion).colour (hE x) (hE y)).trans (hrC x y))
  · intro x
    apply E.injective
    exact (hE (j x)).trans (hr x)

/-- This is a concrete finite-age expansion, with all three properties
proved from the actual source construction rather than extra callbacks. -/
def actual_unary_transition (seeds : M.FiniteSeedExtension) :
    Towers.UnaryTransition
      ⟨Age.Chart S (Age.zeroMask S),Age.chartCategory S (Age.zeroMask S)⟩
      ⟨Age.Chart (UnarySource.source I) (Age.zeroMask (UnarySource.source I)),
        Age.chartCategory (UnarySource.source I) (Age.zeroMask (UnarySource.source I))⟩ :=
  (actualProjection I).transition_of_extension (actual_extension I seeds)

end
end CCO.APCharacter.SourceAge
