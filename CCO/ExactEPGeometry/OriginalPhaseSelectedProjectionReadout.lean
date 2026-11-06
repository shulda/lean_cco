import CCO.ExactEPGeometry.OriginalPhaseSelectedPointEquiv
import CCO.ExactEPGeometry.OriginalSelectedGlobalClassReadout
import CCO.ExactEPGeometry.OriginalSelectedSortRetyping
import CCO.PairHomogeneity

/-!
# B062 C96/C103: actual selected quotient projection readout

The true successor selected-point equivalence commutes with the literal
current-to-selected quotient maps and actual unary point projection. Its
proof identifies real global original E-classes on both sides. The old
current-to-selected map is equivariant for the actual original group, so
equal complete old point-pair colours retain equal complete selected pair
colours. These are actual source calculations, with no quotient section.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter APCharacter.SourceAge APCharacter.Towers RigidGroupoid.Geometry
noncomputable section

variable (A B : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (transport : ExactTraceTransport A.source B.source P)
variable (base : A.Sorts) (hBase : ∀ i : A.Sorts, base = i)
variable (E : ExactEq A.source base)

/-- The literal current-to-selected quotient point map intertwines
the SAME actual old group action on every named parent. -/
theorem originalCurrentToSelectedPoint_smul (g : B.G) (p : Sigma B.Point) :
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    letI : ∀ i : Q.Sorts, MulAction B.G (Q.Point i) := Q.action
    originalCurrentToSelectedPoint A B P transport base hBase E (g • p) =
      g • originalCurrentToSelectedPoint A B P transport base hBase E p := by
  rcases p with ⟨i,x⟩
  let Qall := originalExactAllCurrentQuotientCurrentSource A B P transport base hBase E
  letI : ∀ k : Qall.Sorts, MulAction B.G (Qall.Point k) := Qall.action
  let Occ := OriginalOccupancy A B P base hBase E
  letI : Finite Occ := originalOccupancyFinite A B P base hBase E
  letI : Fintype Occ := Fintype.ofFinite Occ
  let σ := originalOccupancyRepresentativeEmbedding A B P base hBase E
  let D : SelectedRetyping (X := Qall.Point) σ (G := B.G) :=
    originalSelectedSortRetyping A B P transport base hBase E
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  letI : ∀ k : Q.Sorts, MulAction B.G (Q.Point k) := Q.action
  change (⟨(Quotient.mk'' i : Occ),D.pointEquiv i (Quotient.mk'' (g • x))⟩ : Sigma Q.Point) =
    ⟨(Quotient.mk'' i : Occ),g • D.pointEquiv i (Quotient.mk'' x)⟩
  exact congrArg (fun z => (⟨(Quotient.mk'' i : Occ),z⟩ : Sigma Q.Point))
    (D.equivariant i g (Quotient.mk'' x))

/-- Equality of every COMPLETE old fine pair colour preserves the
complete selected quotient pair colour, including logical equality and
all endpoint occupancy names. The actual old pair homogeneity is used. -/
theorem originalCurrentToSelectedPoint_taggedColour_of_eq
    (q s q' s' : Sigma B.Point)
    (h : taggedColour B.source q' s' = taggedColour B.source q s) :
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let π := originalCurrentToSelectedPoint A B P transport base hBase E
    taggedColour Q.source (π q') (π s') = taggedColour Q.source (π q) (π s) := by
  rcases q with ⟨i,x⟩
  rcases s with ⟨j,y⟩
  rcases q' with ⟨i',x'⟩
  rcases s' with ⟨j',y'⟩
  have hi : i' = i := (Sigma.mk.inj h).1
  subst i'
  have hj : j' = j := (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).1
  subst j'
  have hc : B.source.colour x' y' = B.source.colour x y :=
    eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
  obtain ⟨g,hgx,hgy⟩ :=
    (B.source.pair_homogeneous_of_homogeneous B.homogeneous) x' x y' y hc
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  letI : ∀ k : Q.Sorts, MulAction B.G (Q.Point k) := Q.action
  let π := originalCurrentToSelectedPoint A B P transport base hBase E
  have hMoveX : g • π ⟨i,x'⟩ = π ⟨i,x⟩ :=
    (originalCurrentToSelectedPoint_smul A B P transport base hBase E g ⟨i,x'⟩).symm.trans
      (congrArg π (congrArg (Sigma.mk i) hgx))
  have hMoveY : g • π ⟨j,y'⟩ = π ⟨j,y⟩ :=
    (originalCurrentToSelectedPoint_smul A B P transport base hBase E g ⟨j,y'⟩).symm.trans
      (congrArg π (congrArg (Sigma.mk j) hgy))
  have hPres := Q.homogeneous.preserves_colours g (π ⟨i,x'⟩) (π ⟨j,y'⟩)
  exact ((congrArg₂ (taggedColour Q.source) hMoveX hMoveY).symm.trans hPres).symm

variable {r : B.Sorts} (Kroot : Kernel B.source r)
variable (phase : SourcePhase B.source B.homogeneous
  (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)

/-- The actual selected point equivalence commutes with the actual
whole unary reduct on EVERY real successor point. All three maps are
constructed from the same original E-class and genuine source prefix. -/
theorem originalPhaseSelectedPointEquiv_currentToSelected :
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let πN := originalCurrentToSelectedPoint A N (P.compose R) hN base hBase E
    let πB := originalCurrentToSelectedPoint A B P transport base hBase E
    let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
    ∀ p : Sigma N.Point, f (πN p) = πB (R.project p) := by
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  let πN := originalCurrentToSelectedPoint A N (P.compose R) hN base hBase E
  let πB := originalCurrentToSelectedPoint A B P transport base hBase E
  let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
  let repN := originalSelectedTaggedRepresentative A N (P.compose R) hN base hBase E
  let repB := originalSelectedTaggedRepresentative A B P transport base hBase E
  let TN := currentOriginalExactSetoid A N (P.compose R) base hBase E
  let TB := currentOriginalExactSetoid A B P base hBase E
  dsimp only
  intro p
  have hF : TB.r (repB (f (πN p))) (R.project (repN (πN p))) :=
    originalPhaseSelectedPointEquiv_globalE A B P transport Kroot phase base hBase E (πN p)
  have hNClass := originalCurrentToSelectedPoint_globalE A N (P.compose R) hN base hBase E p
  have hNRel : TN.r (repN (πN p)) p := Quotient.exact hNClass
  have hProject : TB.r (R.project (repN (πN p))) (R.project p) := hNRel
  have hBClass := originalCurrentToSelectedPoint_globalE A B P transport base hBase E (R.project p)
  apply (originalSelectedGlobalEClassEquiv A B P transport base hBase E).injective
  change (Quotient.mk'' (repB (f (πN p))) : Quotient TB) = Quotient.mk'' (repB (πB (R.project p)))
  exact (Quotient.sound hF).trans ((Quotient.sound hProject).trans hBClass.symm)

end
end CCO.ExactEPGeometry
