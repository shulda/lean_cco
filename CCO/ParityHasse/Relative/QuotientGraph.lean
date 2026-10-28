import CCO.ParityHasse.Relative.QuotientWords

/-! Quotient functionality is proved on actual classes. No assertion that
the old real gate is a functional relation is made. -/
universe v q t
namespace CCO.ParityHasse.Relative

section Image
variable {A : Type v} {Q : Type q}
def imageRelation (π : A → Q) (R : A → A → Prop) : Q → Q → Prop :=
  fun q r => ∃ x y, π x = q ∧ π y = r ∧ R x y

theorem imageRelation_pullback (π : A → Q) (K : Setoid A)
    (hk : GroupActions.kernel π = K) (R : A → A → Prop) (sat : Bisaturated K R) :
    pull π (imageRelation π R) = R := by
  funext x y; apply propext
  constructor
  · rintro ⟨a,b,ha,hb,hab⟩
    have hxa : K x a := by rw [← hk]; exact ha.symm
    have hby : K b y := by rw [← hk]; exact hb
    exact sat.right (sat.left hxa hab) hby
  · intro h; exact ⟨x,y,rfl,rfl,h⟩

theorem imageRelation_symm (π : A → Q) (R : A → A → Prop)
    (hs : ∀ x y, R x y → R y x) :
    ∀ x y, imageRelation π R x y → imageRelation π R y x := by
  rintro _ _ ⟨a,b,ha,hb,hab⟩; exact ⟨b,a,hb,ha,hs a b hab⟩

theorem imageRelation_serial (π : A → Q) (surj : Function.Surjective π)
    (R : A → A → Prop) (hs : ∀ x, ∃ y, R x y) :
    ∀ q, ∃ r, imageRelation π R q r := by
  intro q
  obtain ⟨x,rfl⟩ := surj q
  obtain ⟨y,hxy⟩ := hs x
  exact ⟨π y,x,y,rfl,rfl,hxy⟩

theorem imageRelation_square (π : A → Q) (surj : Function.Surjective π)
    (K : Setoid A) (hk : GroupActions.kernel π = K)
    (R : A → A → Prop) (sat : Bisaturated K R) (sq : mul R R = K) :
    mul (imageRelation π R) (imageRelation π R) = Eq := by
  apply pull_injective π surj
  rw [pull_comp π surj,imageRelation_pullback π K hk R sat,sq,pull_identity,hk]

 theorem imageRelation_irreflexive (π : A → Q) (K : Setoid A)
    (hk : GroupActions.kernel π = K) (R : A → A → Prop)
    (hd : ∀ x y, R x y → ¬K x y) : ∀ q, ¬imageRelation π R q q := by
  rintro q ⟨x,y,hx,hy,hxy⟩
  apply hd x y hxy
  rw [← hk]
  exact hx.trans hy.symm
end Image

section Graph
variable {Q : Type q}
/-- A total symmetric relation whose square is equality is the graph of
an actual involution; this assertion lives on the quotient carrier. -/
structure InvolutionGraph (D : Q → Q → Prop) where
  map : Q → Q
  graph : ∀ x y, D x y ↔ map x = y
  involutive : Function.Involutive map
  fixedPointFree : ∀ x, map x ≠ x

noncomputable def involutionGraph (D : Q → Q → Prop)
    (serial : ∀ x, ∃ y, D x y) (symm : ∀ x y, D x y → D y x)
    (square : mul D D = Eq) (irreflexive : ∀ x, ¬D x x) : InvolutionGraph D := by
  classical
  let f : Q → Q := fun x => Classical.choose (serial x)
  have hf (x : Q) : D x (f x) := Classical.choose_spec (serial x)
  have unique (x y z : Q) (hxy : D x y) (hxz : D x z) : y = z := by
    have h : mul D D y z := ⟨x,symm x y hxy,hxz⟩
    rw [square] at h
    exact h
  refine ⟨f,?_,?_,?_⟩
  · intro x y
    exact ⟨fun h => unique x (f x) y (hf x) h,fun h => h ▸ hf x⟩
  · intro x
    exact unique (f x) (f (f x)) x (hf _) (symm x (f x) (hf x))
  · intro x h
    exact irreflexive x (by simpa only [h] using hf x)
end Graph

section Equivariance
variable {G : Type t} [Group G] {A : Type v} {Q : Type q}
variable [MulAction G A] [MulAction G Q]

theorem imageRelation_invariant (π : A → Q)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x) (R : A → A → Prop)
    (hR : ∀ (g : G) x y, R x y → R (g • x) (g • y)) :
    ∀ (g : G) q r, imageRelation π R q r → imageRelation π R (g • q) (g • r) := by
  rintro g _ _ ⟨x,y,rfl,rfl,hxy⟩
  exact ⟨g • x,g • y,equivπ g x,equivπ g y,hR g x y hxy⟩

theorem InvolutionGraph.equivariant {D : Q → Q → Prop} (I : InvolutionGraph D)
    (hD : ∀ (g : G) q r, D q r → D (g • q) (g • r)) :
    ∀ (g : G) q, I.map (g • q) = g • I.map q := by
  intro g q
  exact (I.graph _ _).mp (hD g q (I.map q) ((I.graph _ _).mpr rfl))

/-- Equivariance and actual quotient transitivity make the involution
graph ONE actual pair orbital, rather than only a union of orbitals. -/
theorem InvolutionGraph.actual_orbital {D : Q → Q → Prop} (I : InvolutionGraph D)
    (hD : ∀ (g : G) q r, D q r → D (g • q) (g • r))
    (trans : ∀ q r : Q, ∃ g : G, g • q = r) (q : Q) :
    D = GroupActions.orbital (G := G) q (I.map q) := by
  funext x y; apply propext
  constructor
  · intro hxy
    obtain ⟨g,hg⟩ := trans q x
    refine ⟨g,hg,?_⟩
    rw [← I.equivariant hD g q,hg]
    exact (I.graph x y).mp hxy
  · rintro ⟨g,rfl,rfl⟩
    exact hD g q (I.map q) ((I.graph _ _).mpr rfl)
end Equivariance
end CCO.ParityHasse.Relative
