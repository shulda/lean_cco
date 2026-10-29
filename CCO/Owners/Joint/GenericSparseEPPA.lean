import CCO.Owners.Joint.GenericFullAutomorphisms

/-! Generic sparse EPPA in arbitrary named unary/binary languages.
There is no ambient orbital action and no point-homogeneity hypothesis. -/
namespace CCO.Owners.Joint.Relational.LanguageDiagram
variable {I B : Type*} {Bi Di : I → Type*}
variable {d : OwnerDiagram I B Bi} {full : FullOwners d} {π : ∀ i, Di i → Bi i}
variable (L : LanguageDiagram d full π)

/-- Every genuine original partial map has genuine projected partial
maps on their actual image domains. Their owner squares commute. -/
theorem sparse_partial_square (p : Partial L.witnessStructure) (i : I) (w : p.domain) :
    (L.factorOwner i).projection
      (((L.toFactor i).projectedPartial p).map
        ⟨(L.toFactor i).projection w.val,⟨w.val,w.property,rfl⟩⟩) =
      d.beta i ((L.toOwner.projectedPartial p).map
        ⟨L.toOwner.projection w.val,⟨w.val,w.property,rfl⟩⟩) := by
  rw [(L.toFactor i).partial_projection p w, L.toOwner.partial_projection p w,
    L.factorOwner_projection]
  exact L.owner_coordinate (p.map w) i

/-- Extend the owner FIRST, then every factor with that ENTIRE prescribed
owner component. No common ambient orbital group, selected subgroup,
section, coherent extensions, or point-lifting premise is assumed. -/
theorem eppa_sparse (a : Set (Carrier d Di π))
    (ownerEPPA : EPPAFor L.ownerStructure (L.toOwner.projection '' a))
    (factorEPPA : ∀ i, PrescribedEPPAFor (L.factorOwner i)
      ((L.toFactor i).projection '' a)) :
    EPPAFor L.witnessStructure a := by
  intro p hdom hmap
  obtain ⟨g,hg⟩ := ownerEPPA (L.toOwner.projectedPartial p)
    (L.toOwner.partial_domain_subset p hdom) (L.toOwner.partial_mapsTo p hmap)
  have compat : ∀ i, ∀ x : ((L.toFactor i).projectedPartial p).domain,
      (L.factorOwner i).projection (((L.toFactor i).projectedPartial p).map x) =
        (L.jointAction i g).val ((L.factorOwner i).projection x.val) := by
    intro i x
    obtain ⟨w,hw,hwx⟩ := x.property
    let w' : p.domain := ⟨w,hw⟩
    have hx : x = ⟨(L.toFactor i).projection w,⟨w,hw,rfl⟩⟩ := Subtype.ext hwx.symm
    subst x
    rw [(L.toFactor i).partial_projection p w']
    calc
      _ = d.beta i (L.toOwner.projection (p.map w')) := by
        rw [L.factorOwner_projection]
        exact L.owner_coordinate (p.map w') i
      _ = d.beta i
          ((L.toOwner.projectedPartial p).map ⟨L.toOwner.projection w,⟨w,hw,rfl⟩⟩) :=
        congrArg (d.beta i) (L.toOwner.partial_projection p w').symm
      _ = d.beta i (g.val (L.toOwner.projection w)) := congrArg (d.beta i) (hg _).symm
      _ = (L.jointAction i g).val (d.beta i (L.toOwner.projection w)) :=
        (L.joint_action i g _).symm
      _ = _ := by
        congr 1
        rw [L.factorOwner_projection]
        exact (L.owner_coordinate w i).symm
  have coordinateExtensions : ∀ i, ∃ k : (L.factorStructure i).Aut,
      ((L.toFactor i).projectedPartial p).Extends k ∧
        (L.factorOwner i).action k = L.jointAction i g := by
    intro i
    exact factorEPPA i ((L.toFactor i).projectedPartial p)
      ((L.toFactor i).partial_domain_subset p hdom)
      ((L.toFactor i).partial_mapsTo p hmap) (L.jointAction i g) (compat i)
  choose k hk hown using coordinateExtensions
  let matching : Matching L.factorAction L.jointAction := ⟨(g,k),hown⟩
  refine ⟨L.lift matching,?_⟩
  intro w
  apply Subtype.ext
  funext i
  rw [L.lift_coordinate]
  calc
    _ = ((L.toFactor i).projectedPartial p).map
        ⟨(L.toFactor i).projection w.val,⟨w.val,w.property,rfl⟩⟩ := by
      rw [← L.toFactor_projection i w.val]
      exact hk i ⟨(L.toFactor i).projection w.val,⟨w.val,w.property,rfl⟩⟩
    _ = (L.toFactor i).projection (p.map w) := (L.toFactor i).partial_projection p w
    _ = (p.map w).val i := L.toFactor_projection i (p.map w)

end CCO.Owners.Joint.Relational.LanguageDiagram

