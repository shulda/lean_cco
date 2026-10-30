import CCO.PointGeneratedSAP.Alignment

/-! One original real stabilizer motion constructs the actual full induced
point-generated union. No hereditary hidden-base SAP is asserted. -/
universe u v
namespace CCO.PointGeneratedSAP
open UnaryFreshFrames
variable {L : Language.{u}} {V : Type v} {H : Structure L V}
variable {O : Original L V H} (C : Interpretation H O)
namespace Interpretation
include C

/-- C05–C11: PGO supplies a genuine strong amalgam for every induced PG span. -/
theorem ageSAP_of_PGO (hom : O.Homogeneous) (hInf : C.PGO) : AgeSAP O := by
  classical
  intro A B D s t
  obtain ⟨a₀,ha₀⟩ := align C hom A s.ambient t.ambient
  let g₀ := C.lift a₀
  have halign (a : A.points) : g₀ • s.point a = t.point a := ha₀ a
  let root := Piece.Embedding.image t
  let moved : Set V := (fun z => g₀ • z) '' B.points
  have hmoved : moved.Finite := B.finite.image _
  have hmoving : (moved \ root.points).Finite := hmoved.sdiff
  let moving := hmoving.toFinset
  let forbidden := D.finite.toFinset
  have hOrbit (x : V) (hx : x ∈ moving) :
      (MulAction.orbit (C.baseFixer root.realBase) x).Infinite := by
    apply hInf root.realBase root.finite_realBase x
    rw [root.generated_realBase]
    exact (hmoving.mem_toFinset.mp hx).2
  obtain ⟨k,hk⟩ := AclOwners.finite_action_avoidance
    (G := C.baseFixer root.realBase) moving forbidden hOrbit
  let g : H.Aut := k.val * g₀
  have hBase (a : A.points) : g • s.point a = t.point a := by
    change (k.val * g₀) • s.point a = t.point a
    rw [mul_smul,halign a]
    apply C.fixes_closure root.realBase k
    rw [root.generated_realBase]
    exact ⟨a,rfl⟩
  let F := (B.mapAut g).union D
  let l : B.Embedding F.points :=
    ((Structure.Piece.Embedding.identity B.toPiece).mapAut g).restrictTarget
      (fun b => Or.inl ⟨b,rfl⟩)
  let r : D.Embedding F.points := Structure.Piece.Embedding.inclusion (fun _ hd => Or.inr hd)
  refine ⟨F,l,r,hBase,?_⟩
  intro b d hbd
  have hValue : g • b.val = d.val := hbd
  have hIn : g₀ • b.val ∈ root.points := by
    by_contra hn
    have hMoving : g₀ • b.val ∈ moving := hmoving.mem_toFinset.mpr
      ⟨⟨b.val,b.property,rfl⟩,hn⟩
    exact hk (g₀ • b.val) hMoving d.val (D.finite.mem_toFinset.mpr d.property)
      (by change k.val • (g₀ • b.val) = d.val
          simpa only [g,mul_smul] using hValue)
  obtain ⟨a,ha⟩ := hIn
  have hs : s.point a = b.val := MulAction.injective g₀ ((halign a).trans ha)
  refine ⟨a,hs,?_⟩
  have he := hBase a
  rw [hs] at he
  exact he.symm.trans hValue

end Interpretation
end CCO.PointGeneratedSAP
