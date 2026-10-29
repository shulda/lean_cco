import CCO.FiniteLift.SafeSpanBase
import CCO.FiniteLift.Closure

/-! Actual strong closed-span descent through a finite full exact kernel.
Both arbitrary base embeddings are lifted separately on their COMPLETE
preimages. Factor images contain whole kernel classes, which proves both
strongness after projection and safety of every entry in a cross matrix. -/

universe v w t
namespace CCO.FiniteLift
namespace ExactKernel

variable {A : Type v} {S : AtomicSource.{0,v,w} Unit (fun _ => A)}
variable {G : Type t} [Group G] [MulAction G A] (K : ExactKernel S G)

def ambientQuotientEmbedding (g : G) (L : Set K.Q) (W : Set A)
    (hW : ∀ x, K.proj x ∈ L → g • x ∈ W) :
    OrbitalEmbedding (FullAut G K.Q) L (K.proj '' W) where
  toEmbedding := {
    toFun := fun c => ⟨g • c.val, by
      obtain ⟨x, hx⟩ := K.onto c.val
      exact ⟨g • x, hW x (hx ▸ c.property), (K.proj_smul g x).trans (congrArg (g • ·) hx)⟩⟩
    inj' := by
      intro c d h
      exact Subtype.ext ((MulAction.injective g) (congrArg Subtype.val h)) }
  pair := fun c d => (full_orbital_iff _ _ _ _).mpr ⟨g, rfl, rfl⟩

@[simp] theorem ambientQuotientEmbedding_val (g : G) (L : Set K.Q) (W : Set A)
    (hW : ∀ x, K.proj x ∈ L → g • x ∈ W) (c : L) :
    ((K.ambientQuotientEmbedding g L W hW).toEmbedding c).val = g • c.val := rfl

/-- C08–C10: every finite absolutely closed quotient span descends from an
actual original closed span. The target closure uses the FULL quotient
automorphism group, without an onto map from the original group. -/
theorem strongClosedAmalgamation [Countable A]
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
    (finiteK : K.FiniteClasses) (safe : A → A → Prop)
    (amalgamate : StrongClosedAmalgamation G (aclSet G) safe) :
    StrongClosedAmalgamation (FullAut G K.Q) (aclSet (FullAut G K.Q))
      (quotientSafe K.proj safe) := by
  intro C L R hC hL hR closedC closedL closedR f g
  let oldF : OrbitalEmbedding G C L :=
    ⟨f.toEmbedding, fun x y => (full_orbital_iff _ _ _ _).mp (f.pair x y)⟩
  let oldG : OrbitalEmbedding G C R :=
    ⟨g.toEmbedding, fun x y => (full_orbital_iff _ _ _ _).mp (g.pair x y)⟩
  obtain ⟨f₀, hf₀⟩ := K.fullPreimage_embedding H cco hC oldF
  obtain ⟨g₀, hg₀⟩ := K.fullPreimage_embedding H cco hC oldG
  have hC' := K.fullPreimage_finite finiteK C hC
  have hL' := K.fullPreimage_finite finiteK L hL
  have hR' := K.fullPreimage_finite finiteK R hR
  obtain ⟨W, hW, l, r, commute, strong, safeCross⟩ :=
    amalgamate (K.proj ⁻¹' C) (K.proj ⁻¹' L) (K.proj ⁻¹' R) hC' hL' hR'
      (K.fullPreimage_closed H cco finiteK C hC closedC)
      (K.fullPreimage_closed H cco finiteK L hL closedL)
      (K.fullPreimage_closed H cco finiteK R hR closedR) f₀ g₀
  obtain ⟨gl, hgl⟩ := real_embedding_lift S H hL' l
  obtain ⟨gr, hgr⟩ := real_embedding_lift S H hR' r
  have memL (x : A) (hx : K.proj x ∈ L) : gl • x ∈ W :=
    (hgl ⟨x, hx⟩).symm ▸ (l.toEmbedding ⟨x, hx⟩).property
  have memR (x : A) (hx : K.proj x ∈ R) : gr • x ∈ W :=
    (hgr ⟨x, hx⟩).symm ▸ (r.toEmbedding ⟨x, hx⟩).property
  let lbar := K.ambientQuotientEmbedding gl L W memL
  let rbar := K.ambientQuotientEmbedding gr R W memR
  have projL (x : K.proj ⁻¹' L) : K.proj (l.toEmbedding x).val = gl • K.proj x.val :=
    (congrArg K.proj (hgl x).symm).trans (K.proj_smul gl x.val)
  have projR (x : K.proj ⁻¹' R) : K.proj (r.toEmbedding x).val = gr • K.proj x.val :=
    (congrArg K.proj (hgr x).symm).trans (K.proj_smul gr x.val)
  have commuteBar (c : C) : lbar.toEmbedding (f.toEmbedding c) =
      rbar.toEmbedding (g.toEmbedding c) := by
    obtain ⟨x, hx⟩ := K.onto c.val
    let a : K.proj ⁻¹' C := ⟨x, by change K.proj x ∈ C; rw [hx]; exact c.property⟩
    have hf : K.proj (f₀.toEmbedding a).val = (f.toEmbedding c).val := by
      simpa only [oldF, a, hx] using hf₀ a
    have hg : K.proj (g₀.toEmbedding a).val = (g.toEmbedding c).val := by
      simpa only [oldG, a, hx] using hg₀ a
    apply Subtype.ext
    change gl • (f.toEmbedding c).val = gr • (g.toEmbedding c).val
    rw [← hf, ← hg, ← projL, ← projR]
    exact congrArg (fun z : W => K.proj z.val) (commute a)
  have strongBar (a : L) (b : R) : lbar.toEmbedding a = rbar.toEmbedding b ↔
      ∃ c, f.toEmbedding c = a ∧ g.toEmbedding c = b := by
    constructor
    · intro hab
      have he : gl • a.val = gr • b.val := congrArg Subtype.val hab
      obtain ⟨x, hx⟩ := K.onto a.val
      let xx : K.proj ⁻¹' L := ⟨x, by change K.proj x ∈ L; rw [hx]; exact a.property⟩
      have hy : K.proj (gr⁻¹ • (gl • x)) = b.val := by
        rw [K.proj_smul, K.proj_smul, hx, he, inv_smul_smul]
      let yy : K.proj ⁻¹' R := ⟨gr⁻¹ • (gl • x), by
        change K.proj (gr⁻¹ • (gl • x)) ∈ R; rw [hy]; exact b.property⟩
      have hxy : l.toEmbedding xx = r.toEmbedding yy := by
        apply Subtype.ext
        rw [← hgl xx, ← hgr yy]
        exact (smul_inv_smul gr (gl • x)).symm
      obtain ⟨c, hcx, hcy⟩ := (strong xx yy).mp hxy
      refine ⟨⟨K.proj c.val, c.property⟩, Subtype.ext ?_, Subtype.ext ?_⟩
      · calc
          (f.toEmbedding ⟨K.proj c.val, c.property⟩).val =
              K.proj (f₀.toEmbedding c).val := (hf₀ c).symm
          _ = K.proj xx.val := congrArg (fun z : K.proj ⁻¹' L => K.proj z.val) hcx
          _ = a.val := hx
      · calc
          (g.toEmbedding ⟨K.proj c.val, c.property⟩).val =
              K.proj (g₀.toEmbedding c).val := (hg₀ c).symm
          _ = K.proj yy.val := congrArg (fun z : K.proj ⁻¹' R => K.proj z.val) hcy
          _ = b.val := hy
    · rintro ⟨c, rfl, rfl⟩
      exact commuteBar c
  refine ⟨K.proj '' W, hW.image K.proj, lbar, rbar, commuteBar, strongBar, ?_⟩
  intro a b ha hb
  refine ⟨?_, ?_⟩
  · intro he
    obtain ⟨c, hc, _⟩ := (strongBar a b).mp (Subtype.ext he)
    exact ha ⟨c, hc⟩
  · intro x y hx hy
    have hpx : K.proj (gl⁻¹ • x) = a.val := by
      rw [K.proj_smul, hx]
      exact inv_smul_smul gl a.val
    have hpy : K.proj (gr⁻¹ • y) = b.val := by
      rw [K.proj_smul, hy]
      exact inv_smul_smul gr b.val
    let xx : K.proj ⁻¹' L := ⟨gl⁻¹ • x, by
      change K.proj (gl⁻¹ • x) ∈ L; rw [hpx]; exact a.property⟩
    let yy : K.proj ⁻¹' R := ⟨gr⁻¹ • y, by
      change K.proj (gr⁻¹ • y) ∈ R; rw [hpy]; exact b.property⟩
    have ha' : xx ∉ Set.range f₀.toEmbedding := by
      rintro ⟨c, hc⟩
      apply ha
      refine ⟨⟨K.proj c.val, c.property⟩, Subtype.ext ?_⟩
      exact (hf₀ c).symm.trans
        ((congrArg (fun z : K.proj ⁻¹' L => K.proj z.val) hc).trans hpx)
    have hb' : yy ∉ Set.range g₀.toEmbedding := by
      rintro ⟨c, hc⟩
      apply hb
      refine ⟨⟨K.proj c.val, c.property⟩, Subtype.ext ?_⟩
      exact (hg₀ c).symm.trans
        ((congrArg (fun z : K.proj ⁻¹' R => K.proj z.val) hc).trans hpy)
    have hel : (l.toEmbedding xx).val = x :=
      (hgl xx).symm.trans (smul_inv_smul gl x)
    have her : (r.toEmbedding yy).val = y :=
      (hgr yy).symm.trans (smul_inv_smul gr y)
    simpa only [hel, her] using safeCross xx yy ha' hb'

/-- The actual fine-name palette is precisely the universal matrix palette. -/
theorem strongClosedSafePalette [Countable A]
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
    (finiteK : K.FiniteClasses) (safe : Set (S.Atom () ()))
    (amalgamate : StrongClosedAmalgamation G (aclSet G) (S.menuRel safe)) :
    StrongClosedAmalgamation (FullAut G K.Q) (aclSet (FullAut G K.Q))
      (quotientSafePalette S K safe) := by
  have he : quotientSafePalette S K safe = quotientSafe K.proj (S.menuRel safe) := by
    funext c d
    exact propext (quotientSafePalette_iff S K safe c d)
  rw [he]
  exact K.strongClosedAmalgamation H cco finiteK (S.menuRel safe) amalgamate

end ExactKernel
end CCO.FiniteLift
