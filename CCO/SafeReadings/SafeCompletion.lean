import CCO.SafeReadings.SafeRetraction
import CCO.SafeReadings.SafeCertificate
import CCO.StrongExact.PCExactness
import CCO.StrongExact.PCConverse
import CCO.SafeReadings.PCNatural

/-! A safe certificate supplies survivors, not an equivariant choice.
The final colouring uses the canonical greatest PC network and ONE joint
reading. Actual age membership has an explicit separately discharged API. -/
universe u v w z t r
namespace CCO.SafeReadings
open StrongExact StrongPC Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

def TriangleAge : Prop :=
  ∀ (V : Type z) (D : PartialDiagram S V), D.IsComplete →
    (∀ x y z (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
      (a : S.Atom (D.vertexSort x) (D.vertexSort y))
      (b : S.Atom (D.vertexSort y) (D.vertexSort z))
      (c : S.Atom (D.vertexSort x) (D.vertexSort z)),
      D.edge x y hxy = some a → D.edge y z hyz = some b → D.edge x z hxz = some c →
      S.Triangle a b c) → D.HasStrongCompletion

variable {G : Type*} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (cco : SemanticCCO.{u,v,0,w} S)
variable {safe : ∀ i j, S.Menu i j}
variable {V : Type z} (D : PartialDiagram S V) (hComp : D.HasStrongCompletion)

include hComp in
theorem fixed_domain_meets_safe (hs : SafeSystem S safe) (p : DistinctPair V)
    (hhole : D.edge p.src p.dst p.ne = none) :
    (fixedNetwork D p ∩ safe (D.vertexSort p.src) (D.vertexSort p.dst)).Nonempty := by
  obtain ⟨f,hf⟩ := hComp
  obtain ⟨g,hg,hsafe⟩ := safe_certificate S hs D f hf
  obtain ⟨a,ha,hacol⟩ := hsafe p.src p.dst p.ne hhole
  exact ⟨a,fixedNetwork_supports_completion D g hg p a hacol,ha⟩

variable (h : SelectorOn S (augmentedFamily S safe))

noncomputable def canonicalAtom (p : DistinctPair V) :
    S.Atom (D.vertexSort p.src) (D.vertexSort p.dst) :=
  h.choose (fixedNetwork D p)
    (Or.inl (fixedNetwork_exact_of_strongCompletion D H sap cco hComp p))

theorem canonicalAtom_member (p : DistinctPair V) :
    canonicalAtom S H sap cco D hComp h p ∈ fixedNetwork D p := h.member _ _

theorem canonicalAtom_reverse (p : DistinctPair V) :
    canonicalAtom S H sap cco D hComp h ⟨p.dst,p.src,p.ne.symm⟩ =
      S.conv (canonicalAtom S H sap cco D hComp h p) := by
  unfold canonicalAtom
  have hc := h.opposite (fixedNetwork D p)
    (Or.inl (fixedNetwork_exact_of_strongCompletion D H sap cco hComp p))
    (Or.inl (exact_opposite_of_gluing S (S.realEdgeGluing_of_SAP H sap)
      (fixedNetwork_exact_of_strongCompletion D H sap cco hComp p)))
  simpa only [fixedNetwork_converse D p] using hc

theorem canonicalAtom_record (p : DistinctPair V)
    (a : S.Atom (D.vertexSort p.src) (D.vertexSort p.dst))
    (ha : D.edge p.src p.dst p.ne = some a) :
    canonicalAtom S H sap cco D hComp h p = a := by
  have hm := fixedNetwork_refines_initial D p (canonicalAtom_member S H sap cco D hComp h p)
  change canonicalAtom S H sap cco D hComp h p ∈
    (match D.edge p.src p.dst p.ne with | none => Set.univ | some a => {a}) at hm
  simpa only [ha,Set.mem_singleton_iff] using hm

theorem canonicalAtom_triangle {x y z : V} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    S.Triangle (canonicalAtom S H sap cco D hComp h ⟨x,y,hxy⟩)
      (canonicalAtom S H sap cco D hComp h ⟨y,z,hyz⟩)
      (canonicalAtom S H sap cco D hComp h ⟨x,z,hxz⟩) := by
  have hp := h.pc (fixedNetwork D ⟨x,y,hxy⟩) (fixedNetwork D ⟨y,z,hyz⟩)
    (fixedNetwork D ⟨x,z,hxz⟩)
    (Or.inl (fixedNetwork_exact_of_strongCompletion D H sap cco hComp ⟨x,y,hxy⟩))
    (Or.inl (fixedNetwork_exact_of_strongCompletion D H sap cco hComp ⟨y,z,hyz⟩))
    (Or.inl (fixedNetwork_exact_of_strongCompletion D H sap cco hComp ⟨x,z,hxz⟩))
    (fixedNetwork_PC D hxy hyz hxz)
  obtain ⟨a,ha,b,hb,ht⟩ := hp.1 (Set.mem_singleton _)
  simpa only [canonicalAtom,Set.mem_singleton_iff.mp ha,Set.mem_singleton_iff.mp hb] using ht

noncomputable def canonicalDiagram : CompleteDiagram (S := S) V where
  diagram := {
    finite_type := D.finite_type
    vertexSort := D.vertexSort
    edge := fun x y hxy => some (canonicalAtom S H sap cco D hComp h ⟨x,y,hxy⟩)
    edge_reverse := by
      intro x y hxy a
      rw [Option.some.injEq,Option.some.injEq,
        canonicalAtom_reverse S H sap cco D hComp h ⟨x,y,hxy⟩]
      constructor
      · intro he; rw [he]
      · intro he
        have hh := congrArg S.conv he
        simpa only [S.conv_invol] using hh }
  complete := fun x y hxy => ⟨_,rfl⟩

theorem canonicalDiagram_records {x y : V} (hxy : x ≠ y)
    (a : S.Atom (D.vertexSort x) (D.vertexSort y)) (ha : D.edge x y hxy = some a) :
    (canonicalDiagram S H sap cco D hComp h).diagram.edge x y hxy = some a :=
  congrArg some (canonicalAtom_record S H sap cco D hComp h ⟨x,y,hxy⟩ a ha)

theorem canonicalDiagram_safe (hs : SafeSystem S safe)
    (hSafe : ∀ {i j} (E : S.Menu i j) (hE), (E ∩ safe i j).Nonempty → h.choose E hE ∈ safe i j)
    {x y : V} (hxy : x ≠ y) (hhole : D.edge x y hxy = none) :
    canonicalAtom S H sap cco D hComp h ⟨x,y,hxy⟩ ∈ safe (D.vertexSort x) (D.vertexSort y) :=
  hSafe _ _ (fixed_domain_meets_safe S D hComp hs ⟨x,y,hxy⟩ hhole)

theorem canonicalDiagram_in_age (age : TriangleAge.{u,v,w,z} S) :
    (canonicalDiagram S H sap cco D hComp h).diagram.HasStrongCompletion := by
  apply age V _ (canonicalDiagram S H sap cco D hComp h).complete
  intro x y z hxy hyz hxz a b c ha hb hc
  have he1 := Option.some.inj ha
  have he2 := Option.some.inj hb
  have he3 := Option.some.inj hc
  exact he1 ▸ he2 ▸ he3 ▸ canonicalAtom_triangle S H sap cco D hComp h hxy hyz hxz

/-- Literal name covariance of ALL structural maps is simultaneous:
the same selected colouring is used for every sigma and gamma. The
canonical-network transport premise is proved separately by greatestness. -/
theorem canonicalAtom_covariant {Λ : Type t} [Group Λ] {N : Type r}
    (A : PureTagAction S Λ N) (hInv : A.Invariant (augmentedFamily S safe))
    (hCov : h.Covariant A hInv) (σ : V ≃ V) (g : Λ)
    (hNetwork : ∀ p : DistinctPair V,
      A.act g ⟨D.vertexSort p.src,D.vertexSort p.dst,fixedNetwork D p⟩ =
        ⟨D.vertexSort (σ p.src),D.vertexSort (σ p.dst),
          fixedNetwork D ⟨σ p.src,σ p.dst,fun he => p.ne (σ.injective he)⟩⟩)
    (p : DistinctPair V) :
    A.label (canonicalAtom S H sap cco D hComp h
      ⟨σ p.src,σ p.dst,fun he => p.ne (σ.injective he)⟩) =
      A.label (canonicalAtom S H sap cco D hComp h p) := by
  have hh := hCov g ⟨D.vertexSort p.src,D.vertexSort p.dst,fixedNetwork D p⟩
    (Or.inl (fixedNetwork_exact_of_strongCompletion D H sap cco hComp p))
  have congrReading (E F : TaggedMenu S) (hE : E ∈ augmentedFamily S safe)
      (hF : F ∈ augmentedFamily S safe) (he : E = F) :
      A.label (h.choose E.2.2 hE) = A.label (h.choose F.2.2 hF) := by
    subst F
    rfl
  exact (congrReading _ _ _
    (Or.inl (fixedNetwork_exact_of_strongCompletion D H sap cco hComp _))
    (hNetwork p)).symm.trans hh

/-- The structural input concerns the ORIGINAL records/holes, rather
than assuming covariance of the final network. Naturality is proved for
the SAME actual greatest-PC construction and ALL its intermediate menus. -/
theorem canonicalAtom_covariant_initial {Λ : Type t} [Group Λ] {N : Type r}
    (A : PureTagAction S Λ N) (hInv : A.Invariant (augmentedFamily S safe))
    (hCov : h.Covariant A hInv) (σ : V ≃ V) (g : Λ)
    (hSort : ∀ x, D.vertexSort (σ x) = A.tag g (D.vertexSort x))
    (hInitial : ∀ p : DistinctPair V,
      A.act g ⟨D.vertexSort p.src,D.vertexSort p.dst,initial D p⟩ =
        ⟨D.vertexSort (σ p.src),D.vertexSort (σ p.dst),initial D (mapPair σ p)⟩)
    (p : DistinctPair V) :
    A.label (canonicalAtom S H sap cco D hComp h (mapPair σ p)) =
      A.label (canonicalAtom S H sap cco D hComp h p) :=
  canonicalAtom_covariant S H sap cco D hComp h A hInv hCov σ g
    (fixedNetwork_covariant S D σ A g hSort hInitial) p

end CCO.SafeReadings
