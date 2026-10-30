import CCO.PointGeneratedSAP.Examples.Constant
import CCO.PointGeneratedSAP.Alignment

/-! The empty-base obstruction instantiated in the actual original-full-Aut
interpretation interface, rather than in an arbitrary substituted action. -/
namespace CCO.PointGeneratedSAP.Examples.Constant
open UnaryFreshFrames

abbrev original : Original language Point model where
  realSort b := b = false
  originalRel := ∅

def realEquiv : original.Real ≃ ℕ where
  toFun x := x.val.getD 0
  invFun n := ⟨real n,rfl⟩
  left_inv := by
    rintro ⟨(n | n),h⟩
    · exact False.elim (Bool.noConfusion h)
    · rfl
  right_inv _ := rfl

theorem real_value (x : original.Real) : real (realEquiv x) = x.val := by
  rcases x with ⟨(n | n),h⟩
  · exact False.elim (Bool.noConfusion h)
  · rfl

def ofPerm (p : Equiv.Perm ℕ) : original.Aut := by
  refine ⟨(realEquiv.trans p).trans realEquiv.symm,?_,?_⟩
  · intro x
    exact (show model.sort (((realEquiv.trans p).trans realEquiv.symm) x).val = false from rfl).trans x.property.symm
  · intro R
    exact Empty.elim R

def toPerm (g : original.Aut) : Equiv.Perm ℕ :=
  (realEquiv.symm.trans g.val).trans realEquiv

def lift : original.Aut →* model.Aut where
  toFun g := permAut (toPerm g)
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    rintro (n | n) <;> rfl
  map_mul' g h := by
    apply Subtype.ext
    apply Equiv.ext
    rintro (n | n)
    · rfl
    · change real (realEquiv (g • (h • realEquiv.symm n))) =
        real (realEquiv (g • (realEquiv.symm (realEquiv (h • realEquiv.symm n)))))
      have he : realEquiv.symm (realEquiv (h • realEquiv.symm n)) = h • realEquiv.symm n :=
        realEquiv.left_inv (h • realEquiv.symm n)
      rw [he]

theorem lift_ofPerm (p : Equiv.Perm ℕ) : lift (ofPerm p) = permAut p := by
  apply Subtype.ext
  apply Equiv.ext
  rintro (n | n) <;> rfl

theorem real_image (D : Set original.Real) :
    Subtype.val '' D = real '' (realEquiv '' D) := by
  ext x
  constructor
  · rintro ⟨r,hr,rfl⟩
    exact ⟨realEquiv r,⟨r,hr,rfl⟩,real_value r⟩
  · rintro ⟨n,⟨r,hr,rfl⟩,rfl⟩
    exact ⟨r,hr,(real_value r).symm⟩

def interpretation : Interpretation model original where
  lift := lift
  lift_real := by
    intro g x
    rw [← real_value x]
    change real (realEquiv (g • (realEquiv.symm (realEquiv x)))) = (g • x).val
    have he : realEquiv.symm (realEquiv x) = x := realEquiv.left_inv x
    rw [he]
    exact real_value (g • x)
  locallyFinite := by
    intro D hD
    rw [real_image]
    exact closure_reals_finite (hD.image realEquiv)
  generating := by
    rintro (n | n)
    · refine ⟨⟨real 0,rfl⟩,?_⟩
      exact model.closure_closed _ () (real 0) (model.subset_closure _ rfl)
    · exact ⟨⟨real n,rfl⟩,model.subset_closure _ rfl⟩

theorem original_full_homogeneous : original.Homogeneous := by
  intro D hD f g
  let := hD.to_subtype
  obtain ⟨p,hp⟩ := Matching.original_homogeneous (realEquiv ∘ f.point) (realEquiv ∘ g.point)
    (realEquiv.injective.comp f.injective) (realEquiv.injective.comp g.injective)
  refine ⟨ofPerm p,?_⟩
  intro x
  apply realEquiv.injective
  exact hp x

/-- The nonempty-base test holds for the ACTUAL original full group used
by the generic statement, so the missing empty quantifier is substantive. -/
theorem nonempty_original_base_orbits (D : Set original.Real) (hD : D.Finite)
    (hne : D.Nonempty) (u : Point) (hu : u ∉ model.closure (Subtype.val '' D)) :
    (interpretation.orbitOver D u).Infinite := by
  classical
  have hu' : u ∉ model.closure (real '' (realEquiv '' D)) := by
    rwa [← real_image]
  have hnD : (realEquiv '' D).Nonempty := hne.image _
  cases u with
  | none => exact False.elim (hu' (hidden_in_nonempty_closure hnD))
  | some n =>
    intro hf
    let index : Point → ℕ := fun x => x.getD 0
    obtain ⟨k,_,hk⟩ := (Set.infinite_univ : (Set.univ : Set ℕ).Infinite).exists_notMem_finite
      ((hD.image realEquiv).union (hf.image index))
    have hn : n ∉ realEquiv '' D := fun hn => hu' (model.subset_closure _ ⟨n,hn,rfl⟩)
    let p := Equiv.swap n k
    have hfix : ∀ d ∈ D, ofPerm p • d = d := by
      intro d hd
      apply realEquiv.injective
      change Equiv.swap n k (realEquiv d) = realEquiv d
      apply Equiv.swap_apply_of_ne_of_ne
      · intro he
        exact hn (he ▸ (show realEquiv d ∈ realEquiv '' D from ⟨d,hd,rfl⟩))
      · intro he
        exact hk (Or.inl (he ▸ (show realEquiv d ∈ realEquiv '' D from ⟨d,hd,rfl⟩)))
    have hm : real k ∈ interpretation.orbitOver D (real n) := by
      apply (Interpretation.mem_orbitOver_iff interpretation D (real n) (real k)).mpr
      refine ⟨ofPerm p,hfix,?_⟩
      change lift (ofPerm p) • real n = real k
      rw [lift_ofPerm]
      simp [p]
    exact hk (Or.inr ⟨real k,hm,rfl⟩)

theorem original_empty_orbit : interpretation.orbitOver ∅ hidden = {hidden} := by
  ext x
  constructor
  · intro hx
    obtain ⟨a,_,ha⟩ := (Interpretation.mem_orbitOver_iff interpretation ∅ hidden x).mp hx
    exact ha.symm.trans (hidden_fixed _)
  · rintro rfl
    exact (Interpretation.mem_orbitOver_iff interpretation ∅ hidden hidden).mpr
      ⟨1,fun _ h => False.elim h,by rw [map_one]; exact one_smul _ _⟩

theorem not_PGO : ¬ interpretation.PGO := by
  intro h
  have hi := h ∅ Set.finite_empty hidden (by
    have he : Subtype.val '' (∅ : Set original.Real) = (∅ : Set Point) := Set.image_empty _
    rw [he,model.closure_empty]
    exact Set.notMem_empty _)
  rw [original_empty_orbit] at hi
  exact hi (Set.finite_singleton _)

def generatedPair : Piece original where
  toPiece := pair
  generated := by
    have he : {x | x ∈ pair.points ∧ original.realSort (model.sort x)} =
        real '' ({0} : Set ℕ) := by
      ext x
      cases x <;> simp [pair,model,sort,real,hidden]
    rw [he]
    exact pair_point_generated.symm

/-- The actual point-generated category already fails SAP on its empty
base, although every nonempty real-base orbit condition holds. -/
theorem not_point_generated_SAP : ¬ AgeSAP original := by
  intro sap
  let A : Piece original := Piece.empty
  let B := generatedPair
  let s : A.Embedding B.points := UnaryFreshFrames.Structure.Piece.Embedding.inclusion
    (fun _ h => False.elim h)
  obtain ⟨D,l,r,_,hs⟩ := sap A B B s s
  let x : B.points := ⟨hidden,Or.inr rfl⟩
  have hl : l.point x = hidden := hidden_embedding_fixed l
  have hr : r.point x = hidden := hidden_embedding_fixed r
  obtain ⟨a,_,_⟩ := hs x x (hl.trans hr.symm)
  exact a.property

end CCO.PointGeneratedSAP.Examples.Constant
