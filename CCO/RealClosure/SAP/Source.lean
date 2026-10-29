import CCO.RealClosure.Bounds.Algebraicity
import Mathlib.GroupTheory.GroupAction.Defs

/-! The elementary SAP branch permits nonsymmetric original binary colours.
The acting group is the actual ambient group, and finite diagrams retain
every ordered colour. No symmetry, CCO, finite-orbit or monolith provider is
included in the hypotheses. -/
universe v w t
namespace CCO.RealClosure.SAP

structure Source (M : Type v) where
  Colour : Type w
  finiteColour : Finite Colour
  colour : M → M → Colour
  diagonal : ∀ x y, colour x x = colour y y

structure FinitePart (M : Type v) where
  vertices : Set M
  finite_vertices : vertices.Finite

namespace Source
variable {M : Type v} (S : Source.{v,w} M)

structure Embedding (A B : FinitePart M) where
  toEmbedding : ↥A.vertices ↪ ↥B.vertices
  preserves : ∀ x y, S.colour x.val y.val =
    S.colour (toEmbedding x).val (toEmbedding y).val

structure AgeSAP : Prop where
  amalgamate : ∀ (A B C : FinitePart M)
    (eAB : S.Embedding A B) (eAC : S.Embedding A C),
    ∃ (D : FinitePart M) (eBD : S.Embedding B D) (eCD : S.Embedding C D),
      (∀ a, eBD.toEmbedding (eAB.toEmbedding a) =
        eCD.toEmbedding (eAC.toEmbedding a)) ∧
      (∀ b c, eBD.toEmbedding b = eCD.toEmbedding c →
        ∃ a, eAB.toEmbedding a = b ∧ eAC.toEmbedding a = c)

variable {G : Type t} [Group G] [MulAction G M]

structure Homogeneous : Prop where
  preserves : ∀ (g : G) (x y : M), S.colour (g • x) (g • y) = S.colour x y
  extends_finite : ∀ {V : Type v} [Finite V] (f h : V → M),
    (∀ x y, S.colour (f x) (f y) = S.colour (h x) (h y)) →
    ∃ g : G, ∀ x, g • f x = h x

theorem Homogeneous.transitive (H : S.Homogeneous (G := G)) (x y : M) :
    ∃ g : G, g • x = y := by
  obtain ⟨g,hg⟩ := H.extends_finite (fun _ : ULift.{v} Unit => x)
    (fun _ => y) (fun _ _ => S.diagonal x y)
  exact ⟨g,hg ⟨()⟩⟩

theorem Homogeneous.pair (H : S.Homogeneous (G := G))
    {x y x' y' : M}
    (hxy : S.colour x y = S.colour x' y')
    (hyx : S.colour y x = S.colour y' x') :
    ∃ g : G, g • x = x' ∧ g • y = y' := by
  let f : ULift.{v} Bool → M := fun b => if b.down then y else x
  let h : ULift.{v} Bool → M := fun b => if b.down then y' else x'
  obtain ⟨g,hg⟩ := H.extends_finite f h (by
    rintro ⟨a⟩ ⟨b⟩
    cases a <;> cases b <;> simp [f,h,hxy,hyx] <;> exact S.diagonal _ _)
  exact ⟨g,by simpa [f,h] using hg ⟨false⟩,by simpa [f,h] using hg ⟨true⟩⟩

def inclusion (A B : FinitePart M) (h : A.vertices ⊆ B.vertices) : S.Embedding A B where
  toEmbedding := ⟨fun x => ⟨x.val,h x.property⟩,by
    intro x y he
    apply Subtype.ext
    exact congrArg (fun z : ↥B.vertices => z.val) he⟩
  preserves _ _ := rfl

theorem Homogeneous.extends_embedding (H : S.Homogeneous (G := G))
    {A B : FinitePart M} (e : S.Embedding A B) :
    ∃ g : G, ∀ x : ↥A.vertices, g • x.val = (e.toEmbedding x).val := by
  letI := A.finite_vertices.to_subtype
  exact H.extends_finite Subtype.val (fun x => (e.toEmbedding x).val) e.preserves

/-- C19: strong amalgamation supplies a new point in one FIXED finite-base
orbit outside ANY displayed finite set. Both ordered spoke colours and the
entire base are retained, so no symmetry shortcut is present. -/
theorem orbit_fresh (H : S.Homogeneous (G := G)) (sap : S.AgeSAP)
    (A : Finset M) (x : M) (hx : x ∉ A) (F : Set M) (hF : F.Finite) :
    ∃ y, y ∈ Bounds.orbitOver G A x ∧ y ∉ F := by
  classical
  let B : FinitePart M := ⟨A,A.finite_toSet⟩
  let Ext : FinitePart M := ⟨Set.insert x (A : Set M),A.finite_toSet.insert x⟩
  let C : FinitePart M := ⟨Set.insert x ((A : Set M) ∪ F),
    (A.finite_toSet.union hF).insert x⟩
  have hBE : B.vertices ⊆ Ext.vertices := fun b hb => Or.inr hb
  have hBC : B.vertices ⊆ C.vertices := fun b hb => Or.inr (Or.inl hb)
  let eBE := S.inclusion B Ext hBE
  let eBC := S.inclusion B C hBC
  obtain ⟨D,eED,eCD,hbase,hstrong⟩ := sap.amalgamate B Ext C eBE eBC
  obtain ⟨g,hg⟩ := Homogeneous.extends_embedding S H eCD
  let xx : ↥Ext.vertices := ⟨x,Or.inl rfl⟩
  let out : M := (eED.toEmbedding xx).val
  let y : M := g⁻¹ • out
  have havoid : y ∉ F := by
    intro hy
    let c : ↥C.vertices := ⟨y,Or.inr (Or.inr hy)⟩
    have heq : eED.toEmbedding xx = eCD.toEmbedding c := by
      apply Subtype.ext
      exact (smul_inv_smul g out).symm.trans (hg c)
    obtain ⟨b,hb,_⟩ := hstrong xx c heq
    have hv : b.val = x := congrArg Subtype.val hb
    exact hx (hv ▸ b.property)
  have hfix (a : M) (ha : a ∈ A) :
      g⁻¹ • (eED.toEmbedding ⟨a,hBE ha⟩).val = a := by
    have hb := congrArg Subtype.val (hbase ⟨a,ha⟩)
    change (eED.toEmbedding ⟨a,hBE ha⟩).val =
      (eCD.toEmbedding ⟨a,hBC ha⟩).val at hb
    rw [hb,← hg ⟨a,hBC ha⟩]
    exact inv_smul_smul g a
  letI : Finite ↥Ext.vertices := Ext.finite_vertices.to_subtype
  let f : ↥Ext.vertices → M := Subtype.val
  let h : ↥Ext.vertices → M := fun z => g⁻¹ • (eED.toEmbedding z).val
  obtain ⟨k,hk⟩ := H.extends_finite f h (by
    intro a b
    exact (eED.preserves a b).trans (H.preserves g⁻¹ _ _).symm)
  refine ⟨y,⟨k,?_,hk xx⟩,havoid⟩
  intro a ha
  exact (hk ⟨a,hBE ha⟩).trans (hfix a ha)

theorem infinite_orbit (H : S.Homogeneous (G := G)) (sap : S.AgeSAP)
    (A : Finset M) (x : M) (hx : x ∉ A) :
    Set.Infinite (Bounds.orbitOver G A x) := by
  intro hf
  obtain ⟨y,hy,hn⟩ := S.orbit_fresh H sap A x hx _ hf
  exact hn hy

theorem acl_eq_base (H : S.Homogeneous (G := G)) (sap : S.AgeSAP)
    (A : Finset M) : Bounds.Acl G A = (A : Set M) := by
  ext x
  constructor
  · intro hx
    by_contra hn
    exact S.infinite_orbit H sap A x hn hx
  · exact Bounds.parameter_mem_acl A

end Source
end CCO.RealClosure.SAP
