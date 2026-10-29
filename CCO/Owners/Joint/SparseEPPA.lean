import CCO.Owners.Joint.FullAutomorphisms

/-! C19–21: independent EPPA for an arbitrary sparse original input.
The owner partial map is extended FIRST; every coordinate is then asked
for exactly that ENTIRE owner component. No point-homogeneity input. -/
namespace CCO.Owners.Joint
open CCO.Owners.Product
variable {G I A Ω : Type*} {Q O : I → Type*}
variable [Group G] [MulAction G A] [MulAction G Ω]
variable [∀ i, MulAction G (Q i)] [∀ i, MulAction G (O i)]

namespace AmbientGeometry
variable (P : AmbientGeometry (G := G) (I := I) (A := A) (Ω := Ω) (Q := Q) (O := O))
variable (B : Set Ω) (D : ∀ i, Set (Q i))
variable (hD : ∀ i (d : D i), P.own i d.val ∈ P.OwnerImage B i)
variable (surjD : ∀ i, Function.Surjective (P.finiteOwn B D hD i))
variable (fullB : FullOwners (P.finiteDiagram B))

/-- The projected partial maps have their actual image domains and
preserve EVERY named target pair orbital, including all diagonals. -/
theorem sparse_partial_square (p : OrbitalPartial (G := G) (P.point B D hD))
    (i : I) (w : p.domain) :
    P.finiteOwn B D hD i
      (((P.coordinateQuotient B D hD surjD i).projectedPartial p).map
        ⟨(P.coordinateQuotient B D hD surjD i).projection w.val,
          ⟨w.val,w.property,rfl⟩⟩) =
      (P.finiteDiagram B).beta i
        (((P.ownerQuotient B D hD surjD fullB).projectedPartial p).map
          ⟨(P.ownerQuotient B D hD surjD fullB).projection w.val,
            ⟨w.val,w.property,rfl⟩⟩) := by
  rw [(P.coordinateQuotient B D hD surjD i).partial_projection p w,
    (P.ownerQuotient B D hD surjD fullB).partial_projection p w]
  exact P.owner_coordinate B D hD surjD fullB (p.map w) i

/-- The whole optional source EPPA clause, independent of the factor
point-motion and joint kernel conclusions. Empty domains are included. -/
theorem eppa_sparse (a : Set (P.Witness B D hD))
    (ownerEPPA : EPPAFor (G := G) (ι := (Subtype.val : B → Ω))
      ((P.ownerQuotient B D hD surjD fullB).projection '' a))
    (factorEPPA : ∀ i, PrescribedEPPAFor (P.factorOwnerQuotient B D hD surjD i)
      ((fun w : P.Witness B D hD => w.val i) '' a)) :
    EPPAFor (G := G) (ι := P.point B D hD) a := by
  intro p hdom hmap
  let QO := P.ownerQuotient B D hD surjD fullB
  let QC := fun i => P.coordinateQuotient B D hD surjD i
  let OF := fun i => P.factorOwnerQuotient B D hD surjD i
  obtain ⟨g,hg⟩ := ownerEPPA (QO.projectedPartial p)
    (QO.partial_domain_subset p hdom) (QO.partial_mapsTo p hmap)
  have compat : ∀ i, ∀ x : ((QC i).projectedPartial p).domain,
      (OF i).projection (((QC i).projectedPartial p).map x) =
        (P.jointAction B i g).val ((OF i).projection x.val) := by
    intro i x
    obtain ⟨w,hw,hwx⟩ := x.property
    let w' : p.domain := ⟨w,hw⟩
    have hx : x = ⟨(QC i).projection w,⟨w,hw,rfl⟩⟩ := Subtype.ext hwx.symm
    subst x
    rw [(QC i).partial_projection p w']
    change P.finiteOwn B D hD i ((p.map w').val i) =
      (P.jointAction B i g).val (P.finiteOwn B D hD i (w.val i))
    calc
      _ = (P.finiteDiagram B).beta i (QO.projection (p.map w')) :=
        P.owner_coordinate B D hD surjD fullB (p.map w') i
      _ = (P.finiteDiagram B).beta i
          ((QO.projectedPartial p).map ⟨QO.projection w,⟨w,hw,rfl⟩⟩) :=
        congrArg ((P.finiteDiagram B).beta i) (QO.partial_projection p w').symm
      _ = (P.finiteDiagram B).beta i (g.val (QO.projection w)) :=
        congrArg ((P.finiteDiagram B).beta i) (hg _).symm
      _ = (P.jointAction B i g).val ((P.finiteDiagram B).beta i (QO.projection w)) :=
        ((P.jointOwnerQuotient B i).action_projection g _).symm
      _ = _ := congrArg (P.jointAction B i g).val
        (P.owner_coordinate B D hD surjD fullB w i).symm
  have coordinateExtensions : ∀ i, ∃ k : OrbitalAut G (Q i) (Subtype.val : D i → Q i),
      ((QC i).projectedPartial p).Extends k ∧ (OF i).action k = P.jointAction B i g := by
    intro i
    exact factorEPPA i ((QC i).projectedPartial p)
      ((QC i).partial_domain_subset p hdom) ((QC i).partial_mapsTo p hmap)
      (P.jointAction B i g) (compat i)
  choose k hk hown using coordinateExtensions
  let matching : Matching (P.factorAction B D hD surjD) (P.jointAction B) :=
    ⟨(g,k),hown⟩
  refine ⟨P.lift B D hD surjD fullB matching,?_⟩
  intro w
  apply Subtype.ext
  funext i
  rw [P.lift_coordinate]
  exact (hk i ⟨(QC i).projection w.val,⟨w.val,w.property,rfl⟩⟩).trans
    ((QC i).partial_projection p w)

end AmbientGeometry
end CCO.Owners.Joint

