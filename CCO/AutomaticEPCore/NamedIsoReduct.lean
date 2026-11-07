import CCO.ExactEPGeometry.NamedCurrentSourceIso
import CCO.ExactEPGeometry.ExactTraceProduct
import CCO.ExactEPGeometry.CertifiedGateTower

/-! Whole named-source isomorphisms in the actual quotient tower have
literal old-to-new reducts. Their displayed fibres are bijective, so they
preserve the FULL displayed-middle product, with the exact same points.
This is a receiving bridge for the genuine coded safe tower, not a claim
that an arbitrary unary refinement has (TP). -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter.Towers CCO.ExactEPGeometry
noncomputable section

variable {A B : CurrentSource.{u,v,w,t}}

/-- Receive the complete inverse named-source isomorphism as the actual
sort/point/atom forgetful map. Atom injectivity follows from its complete
AtomicIso, rather than from an assumed reduct provider. -/
def namedIsoReduct (I : NamedCurrentSourceIso A B) :
    UnaryReduct A.source B.source := by
  let J := I.symm
  letI := B.source.finiteSort
  let atomic := namedAtomicIso J.sorts J.points J.owner
    B.source A.source J.palette
  exact {
    parent := J.sorts
    point := fun i => atomic.point i
    atom := fun i j => atomic.atom i j
    atom_injective := fun i j => (atomic.atom i j).injective
    colour := fun i j x y => (atomic.colours i j x y).symm
    bijective := by
      have same : (fun p : Sigma B.Point =>
          (⟨J.sorts p.1,atomic.point p.1 p.2⟩ : Sigma A.Point)) = J.points := by
        funext p
        exact namedPointEquiv_tagged J.sorts J.points J.owner p.1 p.2
      rw [same]
      exact J.points.bijective }

theorem namedIsoReduct_project (I : NamedCurrentSourceIso A B)
    (p : Sigma B.Point) :
    (namedIsoReduct I).project p = I.points.symm p :=
  namedPointEquiv_tagged I.symm.sorts I.symm.points I.symm.owner p.1 p.2

theorem namedIsoReduct_point_bijective (I : NamedCurrentSourceIso A B)
    (i : B.Sorts) : Function.Bijective ((namedIsoReduct I).point i) := by
  exact (namedPointEquiv I.symm.sorts I.symm.points I.symm.owner i).bijective

theorem namedIsoReduct_atom_bijective (I : NamedCurrentSourceIso A B)
    (i j : B.Sorts) : Function.Bijective ((namedIsoReduct I).atom i j) := by
  letI := B.source.finiteSort
  exact ((namedAtomicIso I.symm.sorts I.symm.points I.symm.owner
    B.source A.source I.symm.palette).atom i j).bijective

/-- The isomorphism has no missing old point in the displayed middle
fibre. Consequently the actual product equation needs no generic (TP)
axiom and does not change its specified middle sort. -/
theorem namedIsoReduct_product (I : NamedCurrentSourceIso A B) :
    ExactTraceProduct A.source B.source (namedIsoReduct I) := by
  constructor
  intro i j k D E _ _ x z
  constructor
  · rintro ⟨y,hxy,hyz⟩
    exact ⟨(namedIsoReduct I).point j y,hxy,hyz⟩
  · rintro ⟨y,hxy,hyz⟩
    obtain ⟨q,rfl⟩ := (namedIsoReduct_point_bijective I j).2 y
    exact ⟨q,hxy,hyz⟩

/-- For these actual isomorphisms, forgetting a word has the reverse
containment because its prescribed intermediate fibre is surjective.
This statement is false for general prefix UnaryReducts. -/
theorem namedIsoReduct_forgetWord_iff (I : NamedCurrentSourceIso A B)
    {i j : B.Sorts} (W : RawWord B.source i j)
    (x : B.Point i) (y : B.Point j) :
    RawWord.relation A.source
      (ProjectedWords.forgetWord A.source B.source (namedIsoReduct I) W)
      ((namedIsoReduct I).point i x) ((namedIsoReduct I).point j y) ↔
      RawWord.relation B.source W x y := by
  induction W with
  | nil i => exact ProjectedWords.point_eq_iff A.source B.source (namedIsoReduct I) x y
  | identity tail ih => exact ih x y
  | @atom i j k a tail ih =>
    constructor
    · rintro ⟨z,hxz,hzy⟩
      obtain ⟨q,rfl⟩ := (namedIsoReduct_point_bijective I j).2 z
      exact ⟨q,(ProjectedWords.atom_iff A.source B.source
        (namedIsoReduct I) a x q).mpr hxz,(ih q y).mp hzy⟩
    · exact ProjectedWords.forgetWord_forward A.source B.source (namedIsoReduct I) (.atom a tail) x y

theorem namedIsoReduct_forgetExact_iff (I : NamedCurrentSourceIso A B)
    {i j : B.Sorts} (D : RawExact.NonemptyExact B.source i j)
    (x : B.Point i) (y : B.Point j) :
    RawExact.evaluate A.source
      (ProjectedWords.forgetExact A.source B.source (namedIsoReduct I) D).words
      ((namedIsoReduct I).point i x) ((namedIsoReduct I).point j y) ↔
      RawExact.evaluate B.source D.words x y := by
  constructor
  · intro h W hW
    exact (namedIsoReduct_forgetWord_iff I W x y).mp
      (h _ (List.mem_map.mpr ⟨W,hW,rfl⟩))
  · intro h W hW
    obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hW
    exact (namedIsoReduct_forgetWord_iff I Q x y).mpr (h Q hQ)

private def endpointCast {S : CurrentSource.{u,v,w,t}}
    {i j i' j' : S.Sorts} (hi : i = i') (hj : j = j')
    (D : RawExact.NonemptyExact S.source i j) :
    RawExact.NonemptyExact S.source i' j' := by
  cases hi
  cases hj
  exact D

private theorem endpointCast_iff {S : CurrentSource.{u,v,w,t}}
    {i j i' j' : S.Sorts} (hi : i = i') (hj : j = j')
    (D : RawExact.NonemptyExact S.source i j)
    (x : S.Point i') (y : S.Point j') :
    RawExact.evaluate S.source (endpointCast hi hj D).words x y ↔
      RawExact.evaluate S.source D.words
        (cast (congrArg S.Point hi.symm) x)
        (cast (congrArg S.Point hj.symm) y) := by
  cases hi
  cases hj
  rfl

private theorem namedIsoReduct_inverse_point
    (I : NamedCurrentSourceIso A B) (i : B.Sorts) (x : B.Point i) :
    (namedIsoReduct I.symm).point ((namedIsoReduct I).parent i)
      ((namedIsoReduct I).point i x) =
        cast (congrArg B.Point (I.sorts.apply_symm_apply i).symm) x := by
  let P := namedIsoReduct I
  let Q := namedIsoReduct I.symm
  have h : Q.project (P.project ⟨i,x⟩) = (⟨i,x⟩ : Sigma B.Point) := by
    rw [namedIsoReduct_project,namedIsoReduct_project]
    exact I.points.apply_symm_apply ⟨i,x⟩
  have castTag {a b : B.Sorts} (he : a = b) (q : B.Point b) :
      (⟨a,cast (congrArg B.Point he.symm) q⟩ : Sigma B.Point) = ⟨b,q⟩ := by
    cases he
    rfl
  have tag := castTag (I.sorts.apply_symm_apply i) x
  have same := h.trans tag.symm
  exact eq_of_heq (Sigma.mk.inj same).2

/-- BOTH exact-word directions for a whole source isomorphism. Each
presentation is explicitly transported along its actual point/atom maps;
no new exactness or source provider is requested by the receiving tower. -/
theorem namedIsoReduct_transport (I : NamedCurrentSourceIso A B) :
    ExactTraceTransport A.source B.source (namedIsoReduct I) := by
  constructor
  · intro i j D _
    let P := namedIsoReduct I
    let Q := namedIsoReduct I.symm
    let F := ProjectedWords.forgetExact B.source A.source Q D
    let hi : Q.parent (P.parent i) = i := I.sorts.apply_symm_apply i
    let hj : Q.parent (P.parent j) = j := I.sorts.apply_symm_apply j
    refine ⟨endpointCast hi hj F,?_⟩
    intro x y
    rw [endpointCast_iff]
    have h := namedIsoReduct_forgetExact_iff I.symm D (P.point i x) (P.point j y)
    rw [namedIsoReduct_inverse_point,namedIsoReduct_inverse_point] at h
    exact h
  · intro i j D
    exact ⟨ProjectedWords.forgetExact A.source B.source (namedIsoReduct I) D,
      fun x y => (namedIsoReduct_forgetExact_iff I D x y).symm⟩

/-- A complete source renaming of a real exact prefix retains its actual
fixed original reduct, both RAW directions and the full typed product. -/
def namedIsoExactPrefix {original : CurrentSource.{u,v,w,t}}
    (s : CertifiedGateTower.ExactPrefix original)
    (I : NamedCurrentSourceIso s.current B) :
    CertifiedGateTower.ExactPrefix original where
  current := B
  reduct := s.reduct.compose (namedIsoReduct I)
  transport := ExactTraceTransport.compose s.reduct (namedIsoReduct I)
    s.transport (namedIsoReduct_transport I)
  product := ExactTraceProduct.compose s.reduct (namedIsoReduct I)
    s.transport s.product (namedIsoReduct_transport I) (namedIsoReduct_product I)

end
end CCO.AutomaticEPCore
