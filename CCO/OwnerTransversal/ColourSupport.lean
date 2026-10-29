import CCO.FinitePackets.Normalization.ColourTransport
import CCO.FinitePackets.Normalization.SubgroupInterval
import CCO.RealClosure.Bounds.Singleton

/-! A strong-closed diversity support and its thin stabilizer define an
actual GLOBAL original colour-invariant equivalence. The support conditions
are intermediate algebraic hypotheses; consumers must prove them from the
actual transversal triangle palette. No local-sort invariance is substituted
for invariance on the original source. -/

universe v w t
namespace CCO.OwnerTransversal
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable (F E : ColourEq S ()) {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G) (thin : ThinBottom S F)
variable (D : Set (FullColour S))

/-- The stabilizer is a subgroup of the ACTUAL packet translations, with
the owner stabilizer included explicitly. It need not act freely on D. -/
def supportTranslations : Subgroup (Translation S F G) where
  carrier := {e | e ∈ equivalenceTranslations S F E ∧
    ∀ c ∈ D, switchColour S F e c ∈ D}
  one_mem' := ⟨(equivalenceTranslations S F E).one_mem, by
    intro c hc
    simpa only [switchColour_one] using hc⟩
  mul_mem' := by
    rintro e f ⟨he,heD⟩ ⟨hf,hfD⟩
    refine ⟨(equivalenceTranslations S F E).mul_mem he hf,?_⟩
    intro c hc
    rw [switchColour_mul S F H]
    exact heD _ (hfD _ hc)
  inv_mem' := by
    rintro e ⟨he,heD⟩
    refine ⟨(equivalenceTranslations S F E).inv_mem he,?_⟩
    intro c hc
    rw [translation_inv S F H thin]
    exact heD c hc

structure ColourSupportConditions : Prop where
  below : ∀ c ∈ D, FullColourBelow S E c
  nonthin : ∀ c ∈ D, ∀ x y : M, col S x y = c → ¬ F x y
  closed : ∀ x y z : M, col S x y ∈ D → col S y z ∈ D →
    ¬ F x z → col S x z ∈ D
  overlap : ∀ e : Translation S F G, e ∈ equivalenceTranslations S F E →
    (∃ c ∈ D, switchColour S F e c ∈ D) →
    ∀ c ∈ D, switchColour S F e c ∈ D

def supportRelation (x y : M) : Prop :=
  subgroupRelation S F (supportTranslations S F E H thin D) x y ∨ col S x y ∈ D

variable (hD : ColourSupportConditions S F E (G := G) D)
include hD

theorem supportRelation_le {x y : M} (h : supportRelation S F E H thin D x y) : E x y := by
  rcases h with ⟨e,he,rfl⟩ | hd
  · exact he.1 x
  · exact hD.below _ hd x y rfl

omit hD in
include H thin in
private theorem translate_twice (e : Translation S F G) (x : M) :
    e.val (e.val x) = x := by
  have he := congrArg (fun f : Translation S F G => f.val x)
    (translation_square S F H thin e)
  exact he

theorem supportRelation_trans {x y z : M}
    (hxy : supportRelation S F E H thin D x y)
    (hyz : supportRelation S F E H thin D y z) :
    supportRelation S F E H thin D x z := by
  rcases hxy with ⟨e,he,rfl⟩ | hxy
  · rcases hyz with ⟨f,hf,rfl⟩ | hyz
    · exact Or.inl ⟨f * e, (supportTranslations S F E H thin D).mul_mem hf he, rfl⟩
    · right
      have ht := he.2 _ hyz
      rw [← switchColour_left S F H, translate_twice S F H thin] at ht
      exact ht
  · rcases hyz with ⟨e,he,rfl⟩ | hyz
    · right
      rw [switchColour_right S F H]
      exact he.2 _ hxy
    · by_cases hxz : F x z
      · obtain ⟨e,he,_⟩ := translation_regular S F H thin x z hxz
        have hE : E x (e.val x) := by
          rw [he]
          exact E.val.trans (hD.below _ hxy _ _ rfl) (hD.below _ hyz _ _ rfl)
        have heE := equivalenceTranslations_at S F H E e x hE
        have hover : ∃ c ∈ D, switchColour S F e c ∈ D := by
          refine ⟨col S x y,hxy,?_⟩
          rw [← switchColour_left S F H,he,col_symm S z y]
          exact hyz
        exact Or.inl ⟨e,⟨heE,hD.overlap e heE hover⟩,he⟩
      · exact Or.inr (hD.closed x y z hxy hyz hxz)

/-- C39: the same old-colour union is an equivalence on ALL of M. -/
def supportEquivalence : ColourEq S () where
  val := {
    r := supportRelation S F E H thin D
    iseqv := ⟨fun x => Or.inl ((subgroupSetoid S F
      (supportTranslations S F E H thin D)).refl x), by
      intro x y h
      rcases h with hs | hd
      · exact Or.inl ((subgroupSetoid S F
          (supportTranslations S F E H thin D)).symm hs)
      · exact Or.inr (by simpa only [col_symm S y x] using hd),
      fun hxy hyz => supportRelation_trans S F E H thin D hD hxy hyz⟩ }
  property := by
    intro x y x' y' hc
    change col S x y = col S x' y' at hc
    constructor
    · intro h
      rcases h with hs | hd
      · exact Or.inl (subgroupRelation_transport S F H _ hc hs)
      · exact Or.inr (hc ▸ hd)
    · intro h
      rcases h with hs | hd
      · exact Or.inl (subgroupRelation_transport S F H _ hc.symm hs)
      · exact Or.inr (hc.symm ▸ hd)

theorem supportEquivalence_le : supportEquivalence S F E H thin D hD ≤ E :=
  fun _ _ h => supportRelation_le S F E H thin D hD h

/-- C40: an actual nonthin D-edge has an infinite original singleton
stabilizer orbit. This proves infinite GLOBAL classes directly from the
accepted absolute singleton acl theorem, without assuming an infinite
transversal embedding or original SAP. -/
theorem supportEquivalence_infinite [DecidableEq M]
    (cco : SemanticCCO.{0,v,0,w} S)
    (hF : F = finitePacket S H) (hne : D.Nonempty) (x : M) :
    Set.Infinite {y : M | supportEquivalence S F E H thin D hD x y} := by
  obtain ⟨c,hc⟩ := hne
  obtain ⟨a,b,hab⟩ := colour_realized S c
  obtain ⟨g,hgx⟩ := S.original_sort_transitive_of_homogeneous H () a x
  let y := g • b
  have hxy : col S x y = c := by
    rw [← hgx]
    exact (col_invariant S H g a b).trans hab
  have hnot : ¬ finitePacket S H x y := by
    rw [← hF]
    exact hD.nonthin c hc x y hxy
  have hinf : (orbitOver G {x} y).Infinite := by
    intro hfin
    have hy : y ∈ Acl G {x} := hfin
    rw [acl_singleton S H cco x] at hy
    exact hnot hy
  apply hinf.mono
  rintro z ⟨k,hfix,hk⟩
  right
  have hkx := hfix x (Finset.mem_singleton_self x)
  have hcol : col S x z = c := by
    rw [← hk,← hkx]
    exact (col_invariant S H k x y).trans hxy
  exact hcol ▸ hc

end
end CCO.OwnerTransversal
