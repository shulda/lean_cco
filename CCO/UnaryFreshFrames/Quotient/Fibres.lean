import CCO.AclOwners.Avoidance
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Set.Finite.Basic

/-! Actual quotient fibres for equivariant maps. The named-term source
instance is supplied in `Named`; these elementary lemmas use only group actions.
The relative index below is a quotient of an ACTUAL fibre, not a group index. -/
universe u v w z
namespace CCO.UnaryFreshFrames.Quotient

variable {G : Type u} [Group G] {M : Type v} {Q : Type w} {V : Type z}
variable [MulAction G M] [MulAction G Q] [MulAction G V]

def Equivariant (f : M → V) : Prop := ∀ (g : G) x, f (g • x) = g • f x

def Transitive : Prop := ∀ x y : M, ∃ g : G, g • x = y

def FibreValues (p : M → Q) (f : M → V) (b : Q) : Set V :=
  f '' {x | p x = b}

def KernelLe (p : M → Q) (f : M → V) : Prop :=
  ∀ x y, p x = p y → f x = f y

/-- Evaluation at one real point determines the ENTIRE equivariant function. -/
theorem equivariant_ext (ht : Transitive (G := G) (M := M)) (x : M)
    {f k : M → V} (hf : Equivariant (G := G) f) (hk : Equivariant (G := G) k)
    (he : f x = k x) : f = k := by
  funext y
  obtain ⟨g, rfl⟩ := ht x y
  rw [hf, hk, he]

/-- Finite point evaluations give finitely many semantic functions. No bound
on the number of syntactic terms or on the language is used. -/
theorem finite_semantic_functions (ht : Transitive (G := G) (M := M)) (x : M)
    (T : Set (M → V)) (he : ∀ f ∈ T, Equivariant (G := G) f)
    (hv : ((fun f : M → V => f x) '' T).Finite) : T.Finite := by
  apply Set.Finite.of_finite_image hv
  intro f hf k hk hfk
  exact equivariant_ext ht x (he f hf) (he k hk) hfk

/-- The quotient-point stabilizer acts transitively on its actual fibre. -/
theorem fibre_transitive (ht : Transitive (G := G) (M := M)) (p : M → Q)
    (hp : Equivariant (G := G) p) (x y : M) (he : p x = p y) :
    ∃ g : MulAction.stabilizer G (p x), g • x = y := by
  obtain ⟨g, hg⟩ := ht x y
  refine ⟨⟨g, ?_⟩, hg⟩
  change g • p x = p x
  rw [← hp, hg, he]

/-- C20: the stabilizer orbit is exactly the image of the same actual fibre. -/
theorem orbit_eq_fibreValues (ht : Transitive (G := G) (M := M)) (p : M → Q)
    (hp : Equivariant (G := G) p) (f : M → V)
    (hf : Equivariant (G := G) f) (x : M) :
    MulAction.orbit (MulAction.stabilizer G (p x)) (f x) = FibreValues p f (p x) := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨g • x, ?_, ?_⟩
    · change p ((g : G) • x) = p x
      rw [hp]
      exact g.property
    · exact hf g x
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨g, hg⟩ := fibre_transitive ht p hp x z hz.symm
    refine ⟨g, ?_⟩
    change (g : G) • f x = f z
    change (g : G) • x = z at hg
    rw [← hf, hg]

/-- The kernel classes inside one ACTUAL projection fibre biject with its
actual term-image values, proving the meaning of the relative index. -/
noncomputable def fibreKernelEquivValues (p : M → Q) (f : M → V) (b : Q) :
    Quotient (Setoid.ker (fun x : {x // p x = b} => f x.val)) ≃ FibreValues p f b :=
  (Setoid.quotientKerEquivRange _).trans (Set.equivOfEq (by
    ext y
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩))

/-- A single equality at one real point globalizes to the literal factor. -/
theorem factor_of_one_value (ht : Transitive (G := G) (M := M)) (p : M → Q)
    (hp : Equivariant (G := G) p) (f : M → V) (hf : Equivariant (G := G) f)
    (s : Q → V) (hs : Equivariant (G := G) s) (x : M) (h : f x = s (p x)) :
    f = s ∘ p := by
  apply equivariant_ext ht x hf
  · intro g y
    change s (p (g • y)) = g • s (p y)
    rw [hp g y, hs g (p y)]
  · exact h

/-- Noncontainment of actual kernels supplies two different values in EVERY
nonempty projection fibre; no finite-index premise is used. -/
theorem exists_other_fibre_value (ht : Transitive (G := G) (M := M)) (p : M → Q)
    (hp : Equivariant (G := G) p) (f : M → V) (hf : Equivariant (G := G) f)
    (hn : ¬ KernelLe p f) (x : M) :
    ∃ y, p y = p x ∧ f y ≠ f x := by
  classical
  obtain ⟨a, b, hab, hne⟩ : ∃ a b, p a = p b ∧ f a ≠ f b := by
    simpa only [KernelLe, not_forall, not_imp, exists_prop] using hn
  obtain ⟨g, hg⟩ := ht a x
  have hpx : p (g • b) = p x := by rw [hp, ← hab, ← hp, hg]
  refine ⟨g • b, hpx, ?_⟩
  intro he
  have hfa : g • f b = g • f a := by rw [← hf, ← hf, hg]; exact he
  exact hne (MulAction.injective g hfa).symm

/-- A genuine base-fixing element moves every nonforced fibre value. -/
theorem exists_stabilizer_moves (ht : Transitive (G := G) (M := M)) (p : M → Q)
    (hp : Equivariant (G := G) p) (f : M → V) (hf : Equivariant (G := G) f)
    (hn : ¬ KernelLe p f) (x : M) :
    ∃ g : MulAction.stabilizer G (p x), g • f x ≠ f x := by
  obtain ⟨y, hpy, hfy⟩ := exists_other_fibre_value ht p hp f hf hn x
  obtain ⟨g, hg⟩ := fibre_transitive ht p hp x y hpy.symm
  refine ⟨g, ?_⟩
  change (g : G) • f x ≠ f x
  change (g : G) • x = y at hg
  rw [← hf, hg]
  exact hfy

end CCO.UnaryFreshFrames.Quotient
