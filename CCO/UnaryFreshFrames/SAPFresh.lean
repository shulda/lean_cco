import CCO.UnaryFreshFrames.Age
import CCO.UnaryFreshFrames.ClosureActions

/-! Actual SAP supplies a whole fresh copy over one finite closed base.
Homogeneity aligns the entire first factor, then extends the second copy;
there is no point-generated or free-amalgam restriction. -/
universe u v
namespace CCO.UnaryFreshFrames.Structure
variable {L : Language.{u}} {V : Type v} (H : Structure L V)

/-- One full automorphism moves an entire finite closed factor away from
another factor outside their common closed base. -/
def FreshMotion : Prop :=
  ∀ (A B C : H.Piece), A.points ⊆ B.points → A.points ⊆ C.points →
    ∃ g : H.Aut, (∀ a ∈ A.points, g • a = a) ∧
      ∀ b ∈ B.points, ∀ c ∈ C.points, g • c = b → c ∈ A.points

theorem freshMotion_of_ageSAP (hom : H.Homogeneous) (sap : H.AgeSAP) :
    H.FreshMotion := by
  intro A B C hAB hAC
  let s : A.Embedding B.points := Piece.Embedding.inclusion hAB
  let t : A.Embedding C.points := Piece.Embedding.inclusion hAC
  obtain ⟨D, l, r, agree, strong⟩ := sap A B C s t
  obtain ⟨a, ha⟩ := hom B l.ambient (Piece.Embedding.identity B).ambient
  let q : C.Embedding Set.univ := (r.mapAut a).ambient
  obtain ⟨g, hg⟩ := hom C (Piece.Embedding.identity C).ambient q
  have hq (c : C.points) : g • c.val = a • r.point c := hg c
  have hl (b : B.points) : a • l.point b = b.val := ha b
  refine ⟨g, ?_, ?_⟩
  · intro x hx
    have he := agree ⟨x, hx⟩
    change l.point ⟨x, hAB hx⟩ = r.point ⟨x, hAC hx⟩ at he
    exact (hq ⟨x, hAC hx⟩).trans
      ((congrArg (fun z => a • z) he.symm).trans (hl ⟨x, hAB hx⟩))
  · intro b hb c hc hmove
    have he : l.point ⟨b, hb⟩ = r.point ⟨c, hc⟩ := by
      apply MulAction.injective a
      exact (hl ⟨b, hb⟩).trans (hmove.symm.trans (hq ⟨c, hc⟩))
    obtain ⟨x, _, hx⟩ := strong ⟨b, hb⟩ ⟨c, hc⟩ he
    change x.val = c at hx
    exact hx ▸ x.property

/-- C10: a fresh whole-factor copy excludes any finite candidate orbit.
Closing the finite forbidden orbit lets one use the actual hereditary SAP
span, including bases which have orphan hidden vertices. -/
theorem infiniteClosedOrbits_of_freshMotion (hfin : H.LocallyFinite)
    (fresh : H.FreshMotion) : H.InfiniteClosedOrbits H.Aut := by
  intro A hA hclosed x hx hOrbit
  let base : H.Piece := ⟨A, hA, hclosed⟩
  let forbidden : H.Piece := ⟨H.closure (A ∪ orbitOver H.Aut A x),
    hfin _ (hA.union hOrbit), H.closure_closed _⟩
  let source : H.Piece := ⟨H.closure (A ∪ {x}),
    hfin _ (hA.union (Set.finite_singleton x)), H.closure_closed _⟩
  have hAB : base.points ⊆ forbidden.points :=
    fun z hz => H.subset_closure _ (Or.inl hz)
  have hAC : base.points ⊆ source.points :=
    fun z hz => H.subset_closure _ (Or.inl hz)
  obtain ⟨g, hfix, havoid⟩ := fresh base forbidden source hAB hAC
  have hmem : g • x ∈ forbidden.points := H.subset_closure _ (Or.inr
    ((mem_orbitOver_iff H.Aut).mpr ⟨g, hfix, rfl⟩))
  exact hx (havoid (g • x) hmem x (H.subset_closure _ (Or.inr rfl)) rfl)

theorem infiniteClosedOrbits_of_ageSAP (hfin : H.LocallyFinite)
    (hom : H.Homogeneous) (sap : H.AgeSAP) : H.InfiniteClosedOrbits H.Aut :=
  H.infiniteClosedOrbits_of_freshMotion hfin (H.freshMotion_of_ageSAP hom sap)

end CCO.UnaryFreshFrames.Structure
