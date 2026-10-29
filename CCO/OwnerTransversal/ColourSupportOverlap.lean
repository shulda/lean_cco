import CCO.OwnerTransversal.ColourSupport

/-! One overlapping thin translate of a nonthin strong-closed diversity
support preserves the whole support. Freshness is obtained from an actual
original singleton stabilizer orbit and finite packets. No transversal
existence, local-sort invariance, or original SAP is assumed. -/

universe v w t
namespace CCO.OwnerTransversal
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable (F E : ColourEq S ()) {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G) (thin : ThinBottom S F)
variable [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)
variable (hF : F = finitePacket S H) (D : Set (FullColour S))

include H cco hF in
/-- C37, on the actual original real carrier. The conclusion retains the
entire owner stabilizer argument, including translations acting trivially
on some colours. -/
theorem colourSupport_overlap
    (nonthin : ∀ c ∈ D, ∀ x y : M, col S x y = c → ¬ F x y)
    (closed : ∀ x y z : M, col S x y ∈ D → col S y z ∈ D →
      ¬ F x z → col S x z ∈ D)
    (e : Translation S F G) (_he : e ∈ equivalenceTranslations S F E)
    (overlap : ∃ a ∈ D, switchColour S F e a ∈ D) :
    ∀ b ∈ D, switchColour S F e b ∈ D := by
  obtain ⟨a,ha,hea⟩ := overlap
  intro b hb
  obtain ⟨x,y,hxy⟩ := colour_realized S a
  obtain ⟨u,v,huv⟩ := colour_realized S b
  obtain ⟨g,hgy⟩ := S.original_sort_transitive_of_homogeneous H () u y
  let z₀ := g • v
  have hyz₀ : col S y z₀ = b := by
    rw [← hgy]
    exact (col_invariant S H g u v).trans huv
  have hnF : ¬ finitePacket S H y z₀ := by
    rw [← hF]
    exact nonthin b hb y z₀ hyz₀
  have horbit : (orbitOver G {y} z₀).Infinite := by
    intro hfin
    have hz : z₀ ∈ Acl G {y} := hfin
    rw [acl_singleton S H cco y] at hz
    exact hnF hz
  have hf : {z : M | F x z}.Finite := by
    subst F
    let : Finite {z : M | finitePacket S H x z} := finitePacket_finite S H x
    exact Set.toFinite _
  obtain ⟨z,hz,hxz⟩ := horbit.exists_notMem_finite hf
  obtain ⟨k,hfix,hk⟩ := hz
  have hyz : col S y z = b := by
    have hky := hfix y (Finset.mem_singleton_self y)
    rw [← hk,← hky]
    exact (col_invariant S H k y z₀).trans hyz₀
  have heaz : col S (e.val x) z ∈ D := by
    apply closed (e.val x) y z
    · rw [switchColour_left S F H,hxy]
      exact hea
    · exact hyz ▸ hb
    · intro h
      exact hxz (F.val.trans (translation_in_packet S F G e x) h)
  have hce : col S x (e.val z) ∈ D := by
    rw [switchColour_right S F H]
    rw [switchColour_left S F H] at heaz
    exact heaz
  have hyxe : col S y (e.val z) ∈ D := by
    apply closed y x (e.val z)
    · simpa only [col_symm S y x,hxy] using ha
    · exact hce
    · intro h
      have hyzF := F.val.trans h (F.val.symm (translation_in_packet S F G e z))
      exact nonthin b hb y z hyz hyzF
  rw [switchColour_right S F H,hyz] at hyxe
  exact hyxe

include H cco hF in
/-- The overlap condition in `ColourSupportConditions` is a THEOREM of
the nonthin actual triangle support, rather than an additional provider. -/
theorem colourSupportConditions_of_triangles
    (below : ∀ c ∈ D, FullColourBelow S E c)
    (nonthin : ∀ c ∈ D, ∀ x y : M, col S x y = c → ¬ F x y)
    (closed : ∀ x y z : M, col S x y ∈ D → col S y z ∈ D →
      ¬ F x z → col S x z ∈ D) : ColourSupportConditions S F E (G := G) D :=
  ⟨below, nonthin, closed, colourSupport_overlap S F E H cco hF D nonthin closed⟩

end
end CCO.OwnerTransversal
