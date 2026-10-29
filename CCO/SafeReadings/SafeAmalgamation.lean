import CCO.FiniteHelpers

/-! The GIVEN safety hypothesis concerns ALL complete induced spans.
The empty base is allowed. It is stronger than closed-span amalgamation. -/
universe u v w z
namespace CCO.SafeReadings
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

def SafePair (safe : ∀ i j, S.Menu i j) (p q : Sigma X) : Prop :=
  ∃ a ∈ safe p.1 q.1, S.colour p.2 q.2 = some a

structure StrongSafeAmalgamation (safe : ∀ i j, S.Menu i j) : Prop where
  amalgamate : ∀ (C A B : FiniteInduced (X := X))
      (eCA : InducedEmbedding S C A) (eCB : InducedEmbedding S C B),
    ∃ (D : FiniteInduced (X := X))
      (eAD : InducedEmbedding S A D) (eBD : InducedEmbedding S B D),
      (∀ c, eAD.toEmbedding (eCA.toEmbedding c) = eBD.toEmbedding (eCB.toEmbedding c)) ∧
      (∀ a b, eAD.toEmbedding a = eBD.toEmbedding b →
        ∃ c, eCA.toEmbedding c = a ∧ eCB.toEmbedding c = b) ∧
      (∀ a b, (∀ c, eCA.toEmbedding c ≠ a) → (∀ c, eCB.toEmbedding c ≠ b) →
        SafePair S safe (eAD.toEmbedding a).val (eBD.toEmbedding b).val)

theorem StrongSafeAmalgamation.sap {safe : ∀ i j, S.Menu i j}
    (h : StrongSafeAmalgamation S safe) : AgeSAP S := by
  constructor
  intro C A B e f
  obtain ⟨D,a,b,hbase,hsep,_⟩ := h.amalgamate C A B e f
  exact ⟨D,a,b,hbase,hsep⟩

/-- Recolour ONE pair on the SAME formal vertices and owners. Every other
ordered pair, including every real diagonal, retains its old colour. -/
theorem one_edge_safe_recolour {safe : ∀ i j, S.Menu i j}
    (h : StrongSafeAmalgamation S safe) {V : Type z} [Finite V]
    (f : V → Sigma X) (hf : Function.Injective f) (x y : V) (hxy : x ≠ y) :
    ∃ g : V → Sigma X, Function.Injective g ∧
      (∀ p, (g p).1 = (f p).1) ∧
      (∀ p q, ¬ (p = x ∧ q = y) → ¬ (p = y ∧ q = x) →
        taggedColour S (g p) (g q) = taggedColour S (f p) (f q)) ∧
      SafePair S safe (g x) (g y) := by
  classical
  let A : FiniteInduced (X := X) := ⟨f '' {p | p ≠ y}, (Set.toFinite _).image f⟩
  let B : FiniteInduced (X := X) := ⟨f '' {p | p ≠ x}, (Set.toFinite _).image f⟩
  let C : FiniteInduced (X := X) := ⟨f '' {p | p ≠ y ∧ p ≠ x}, (Set.toFinite _).image f⟩
  have hCA : C.vertices ⊆ A.vertices := fun _ ⟨p,hp,he⟩ => ⟨p,hp.1,he⟩
  have hCB : C.vertices ⊆ B.vertices := fun _ ⟨p,hp,he⟩ => ⟨p,hp.2,he⟩
  let ca := inducedInclusion S C A hCA
  let cb := inducedInclusion S C B hCB
  obtain ⟨D,a,b,hbase,hsep,hsafe⟩ := h.amalgamate C A B ca cb
  let l (p : V) (hp : p ≠ y) : ↥A.vertices := ⟨f p, p,hp,rfl⟩
  let r (p : V) (hp : p ≠ x) : ↥B.vertices := ⟨f p, p,hp,rfl⟩
  have agree (p : V) (hy : p ≠ y) (hx : p ≠ x) :
      a.toEmbedding (l p hy) = b.toEmbedding (r p hx) :=
    hbase ⟨f p, p,⟨hy,hx⟩,rfl⟩
  let g (p : V) : ↥D.vertices :=
    if hp : p ≠ y then a.toEmbedding (l p hp)
    else b.toEmbedding (r p (by simpa only [not_not.mp hp] using hxy.symm))
  have gl (p : V) (hp : p ≠ y) : g p = a.toEmbedding (l p hp) := by simp [g,hp]
  have gr (p : V) (hp : p ≠ x) : g p = b.toEmbedding (r p hp) := by
    by_cases hy : p ≠ y
    · exact (gl p hy).trans (agree p hy hp)
    · dsimp only [g]
      rw [dite_eq_right hy]
  have hinj : Function.Injective g := by
    intro p q he
    by_cases hp : p ≠ y
    · by_cases hq : q ≠ y
      · rw [gl p hp,gl q hq] at he
        exact hf (congrArg Subtype.val (a.toEmbedding.injective he))
      · have hqy : q = y := not_not.mp hq
        subst q
        rw [gl p hp,gr y hxy.symm] at he
        obtain ⟨c,_,hc⟩ := hsep _ _ he
        obtain ⟨t,ht,het⟩ := c.property
        have hty : t = y := hf (het.trans (congrArg Subtype.val hc))
        exact False.elim (ht.1 hty)
    · have hpy : p = y := not_not.mp hp
      subst p
      by_cases hq : q = y
      · exact hq.symm
      · rw [gl q hq,gr y hxy.symm] at he
        obtain ⟨c,_,hc⟩ := hsep _ _ he.symm
        obtain ⟨t,ht,het⟩ := c.property
        have hty : t = y := hf (het.trans (congrArg Subtype.val hc))
        exact False.elim (ht.1 hty)
  refine ⟨fun p => (g p).val, fun p q he => hinj (Subtype.ext he), ?_, ?_, ?_⟩
  · intro p
    dsimp only
    by_cases hp : p ≠ y
    · rw [gl p hp]; exact a.preserves_sort _
    · rw [gr p (by simpa [not_not.mp hp] using hxy.symm)]; exact b.preserves_sort _
  · intro p q h1 h2
    dsimp only
    by_cases hp : p ≠ y
    · by_cases hq : q ≠ y
      · rw [gl p hp,gl q hq]; exact (a.preserves_colours _ _).symm
      · have hqy := not_not.mp hq
        have hpx : p ≠ x := fun he => h1 ⟨he,hqy⟩
        have hqx : q ≠ x := by simpa [hqy] using hxy.symm
        rw [gr p hpx,gr q hqx]; exact (b.preserves_colours _ _).symm
    · have hpy := not_not.mp hp
      have hqx : q ≠ x := fun he => h2 ⟨hpy,he⟩
      have hpx : p ≠ x := by simpa [hpy] using hxy.symm
      rw [gr p hpx,gr q hqx]; exact (b.preserves_colours _ _).symm
  · dsimp only
    rw [gl x hxy,gr y hxy.symm]
    apply hsafe
    · intro c hc
      obtain ⟨t,ht,he⟩ := c.property
      exact ht.2 (hf (he.trans (congrArg Subtype.val hc)))
    · intro c hc
      obtain ⟨t,ht,he⟩ := c.property
      exact ht.1 (hf (he.trans (congrArg Subtype.val hc)))

/-- Retag a real point along a proved equality of named owners. -/
def pointAt (p : Sigma X) {i : ι} (h : p.1 = i) : X i := h ▸ p.2

theorem sigma_pointAt (p : Sigma X) {i : ι} (h : p.1 = i) :
    (⟨i, pointAt p h⟩ : Sigma X) = p := by cases p; cases h; rfl

theorem one_edge_safe_recolour_typed {safe : ∀ i j, S.Menu i j}
    (h : StrongSafeAmalgamation S safe) {V : Type z} [Finite V]
    (owner : V → ι) (f : ∀ p, X (owner p))
    (hf : Function.Injective (fun p => (⟨owner p,f p⟩ : Sigma X)))
    (x y : V) (hxy : x ≠ y) :
    ∃ g : ∀ p, X (owner p),
      Function.Injective (fun p => (⟨owner p,g p⟩ : Sigma X)) ∧
      (∀ p q, ¬ (p = x ∧ q = y) → ¬ (p = y ∧ q = x) →
        S.colour (g p) (g q) = S.colour (f p) (f q)) ∧
      (∃ a ∈ safe (owner x) (owner y), S.colour (g x) (g y) = some a) := by
  obtain ⟨g,hg,hs,hkeep,hsafe⟩ := one_edge_safe_recolour S h
    (fun p => ⟨owner p,f p⟩) hf x y hxy
  let g' (p : V) : X (owner p) := pointAt (g p) (hs p)
  have he (p : V) : (⟨owner p,g' p⟩ : Sigma X) = g p := sigma_pointAt _ _
  refine ⟨g',fun p q hpq => hg (by simpa only [he] using hpq),?_,?_⟩
  · intro p q h1 h2
    have hh := hkeep p q h1 h2
    rw [← he p,← he q] at hh
    simpa only [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and] using hh
  · rw [← he x,← he y] at hsafe
    exact hsafe

end CCO.SafeReadings
