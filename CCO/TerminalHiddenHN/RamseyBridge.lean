import CCO.TerminalHiddenHN.OrderedAge
import CCO.TerminalHiddenHN.HNBinding
import CCO.FullCode.RamseyAge
import CCO.UnaryHN.Source

/-! All induced ordered embeddings correspond on their literal maps.
HN's pairwise monochromatic conclusion gives the full-code explicit shade,
including when there is NO embedding of the first object into the second. -/

universe u v w r z
namespace CCO.TerminalHiddenHN
noncomputable section
variable (L : CCO.UnarySupport.Signature.{u}) (hbin : ∀ R, L.arity R = 2)

theorem orderedArrow_to_hiddenArrow
    {V : Type v} {W : Type w} {Z : Type z}
    (C : CCO.UnarySupport.Structure L V) (D : CCO.UnarySupport.Structure L W)
    (E : CCO.UnarySupport.Structure L Z)
    [LinearOrder V] [LinearOrder W] [LinearOrder Z]
    {k : ℕ} (hk : 0 < k) (arrow : CCO.UnaryHN.Raw.OrderedArrow C D E (Fin k)) :
    CCO.FullCode.HiddenArrow (orderedStructure L hbin C) (orderedStructure L hbin D)
      (orderedStructure L hbin E) k := by
  classical
  intro color
  obtain ⟨g,hg⟩ := arrow (fun f => color (orderedEmbedding L hbin f))
  refine ⟨orderedEmbedding L hbin g,?_⟩
  by_cases hCD : Nonempty (CCO.UnaryHN.Raw.OrderedEmbedding C D)
  · let f₀ := Classical.choice hCD
    refine ⟨color (orderedEmbedding L hbin (g.compose f₀)),?_⟩
    intro f
    let f' := orderedEmbeddingInverse L hbin f
    have he : orderedEmbedding L hbin (g.compose f') = (orderedEmbedding L hbin g).comp f := by
      apply CCO.FullCode.Structure.Embedding.ext
      intro x
      rfl
    exact (congrArg color he).symm.trans (hg f' f₀)
  · refine ⟨⟨0,hk⟩,?_⟩
    intro f
    exact False.elim (hCD ⟨orderedEmbeddingInverse L hbin f⟩)

/-- The actual HN witness is chosen before ALL colorings; its entire
carrier is retained, including orphan vertices outside root-generated parts. -/
theorem orderedRamsey_to_fullCode
    {K : CCO.UnaryHN.Raw.Class.{u,v} L}
    (ramsey : CCO.UnaryHN.Source.OrderedRamsey.{u,v,0} K) :
    CCO.FullCode.HasHiddenRamsey (orderedFullCodeAge L hbin K) := by
  intro X Y hX hY k hk
  rcases X with ⟨V,M,hV⟩
  rcases Y with ⟨W,N,hW⟩
  obtain ⟨C,oC,hC,hM⟩ := hX
  obtain ⟨D,oD,hD,hN⟩ := hY
  dsimp only at C oC hC hM D oD hD hN ⊢
  subst M
  subst N
  letI : Finite V := hV
  letI : Finite W := hW
  letI : LinearOrder V := oC
  letI : LinearOrder W := oD
  letI : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  obtain ⟨Z,hZ,oZ,E,hE,arrow⟩ := ramsey C D hC hD (Fin k)
  letI : LinearOrder Z := oZ
  exact ⟨⟨Z,orderedStructure L hbin E,hZ⟩,⟨E,oZ,hE,rfl⟩,
    orderedArrow_to_hiddenArrow L hbin C D E hk arrow⟩

section Actual
variable {ι : Type u} {X : ι → Type v} (S : CCO.AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : CCO.HomogeneousSource S G) (sap : CCO.AgeSAP S)
variable (hCover : ∀ i, CCO.TypedOrbitFrames.OriginalAllFullCoversInfinite S (i := i))
variable [∀ i, Countable (X i)]

/-- The SAME entire actual hidden age with ALL global orders is Ramsey
in its faithful FullCode language. Every HN/provider hypothesis is
constructed by the actual source binding; none survives as a callback. -/
theorem actual_hidden_fullcode_ramsey
    (cco : CCO.SemanticCCO.{u,v,max u v,w} S) :
    CCO.FullCode.HasHiddenRamsey (OrderedActualAge.{u,v,w,r,z} S H sap hCover) :=
  orderedRamsey_to_fullCode (Sig S H sap hCover) (sig_binary S H sap hCover)
    (actual_hidden_ordered_ramsey.{u,v,w,r,z,0} S H sap hCover cco)

end Actual

end
end CCO.TerminalHiddenHN
