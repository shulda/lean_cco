import CCO.HKNReservoir.RealizedAmalgamation

universe v w t
namespace CCO.HKNReservoir
noncomputable section
open AllThoseEPPA ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))
set_option quotPrecheck false
local notation "L" => Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())
local notation "act" => sourceAction S H R B Δ
local notation "N" => sourceStructure S H R B hB

/-- The actual finite class consists of full structures genuinely embedded
in the named source. Its amalgamation is discharged by actual closed SAP;
it is not a new provider premise of the tree theorem. -/
def realizedClass : FiniteStrongAmalgamationClass.{max v w,max v w,v} act where
  mem {X} E := Finite X ∧ Nonempty (Structure.Embedding act E N)
  amalgamate := by
    intro I X Y C D₁ D₂ f g h₁ h₂
    letI := h₁.1
    letI := h₂.1
    letI : Finite I := Finite.of_injective f.toFun f.injective
    obtain ⟨e₁⟩ := h₁.2
    obtain ⟨e₂⟩ := h₂.2
    obtain ⟨r,hl,hbase,hcross⟩ := align_realized_span S H R B hB Δ f g e₁ e₂
    let P := namedRange S H R B e₁.toFun ∪ namedRange S H R B r.toFun
    have hP : PacketClosed S H R B P := by
      intro a ha b hab
      rcases Finset.mem_union.mp ha with ha | ha
      · exact Finset.mem_union_left _ (namedRange_closed S H R B hB Δ e₁ a ha b hab)
      · exact Finset.mem_union_right _ (namedRange_closed S H R B hB Δ r a ha b hab)
    let T : Set (SourceCarrier S H R B) := {x | x.down ∈ P}
    have hT : (N).IsClosed T := packetClosed_isClosed S H R B hB P hP
    have hfin : T.Finite := by
      apply Set.Finite.of_finite_image (f := ULift.down)
      · exact P.finite_toSet.subset (by rintro z ⟨x,hx,rfl⟩; exact hx)
      · exact ULift.down_injective.injOn
    letI : Finite T := hfin
    let E := (N).induce T hT
    have hr₁ : Set.range e₁.toFun ⊆ T := by
      rintro _ ⟨x,rfl⟩
      exact Finset.mem_union_left _ ((mem_namedRange S H R B e₁.toFun _).mpr ⟨x,rfl⟩)
    have hr₂ : Set.range r.toFun ⊆ T := by
      rintro _ ⟨x,rfl⟩
      exact Finset.mem_union_right _ ((mem_namedRange S H R B r.toFun _).mpr ⟨x,rfl⟩)
    let j₁ := embeddingIntoInduce act e₁ T hT hr₁
    let j₂ := embeddingIntoInduce act r T hT hr₂
    refine ⟨T,inferInstance,E,⟨inferInstance,⟨(N).inclusion act T hT⟩⟩,j₁,j₂,?_,?_⟩
    · apply embedding_ext
      · exact hl
      · intro c
        exact Subtype.ext (hbase c)
    · intro x y
      change j₁ x = j₂ y ↔ _
      exact (Subtype.ext_iff).trans (hcross x y)

/-- C05–C07: every actual source tree has an injective
homomorphism-embedding into the actual original named source. -/
theorem actual_tree_realization {U : Type (max v w)} [Finite U]
    (A : Structure L U) (hA : A.IsIrreducible)
    (a : Structure.Embedding act A N) {V : Type (max v w)} {D : Structure L V}
    (tree : TreeLike.TreeAmalgamation act A D) :
    ∃ f : Structure.Homomorphism act D N, Function.Injective f.toFun ∧
      Structure.Homomorphism.IsHomomorphismEmbedding act f := by
  obtain ⟨Z,hZ,E,⟨_,⟨e⟩⟩,f,hf,he⟩ := tree_realization_in_strong_class act A hA
    (realizedClass S H R B hB Δ) ⟨inferInstance,⟨a⟩⟩ tree
  exact ⟨e.toHomomorphism.comp f,e.injective.comp hf,
    Structure.Homomorphism.comp_isHomomorphismEmbedding act _ _
      (Structure.Homomorphism.Embedding.toHomomorphism_isHomomorphismEmbedding act e) he⟩

end
end CCO.HKNReservoir
