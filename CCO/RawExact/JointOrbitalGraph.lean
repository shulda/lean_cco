import CCO.RawExact.JointExactRequests

universe u v w z q t

namespace CCO.RawExact.JointBackAndForth

abbrev Row {K : Type z} (Q : K → Type q) := Σ k, Q k × Q k

def swapRow {K : Type z} {Q : K → Type q} (p : Row Q) : Row Q :=
  ⟨p.1, p.2.2, p.2.1⟩

@[simp] theorem swapRow_swapRow {K : Type z} {Q : K → Type q} (p : Row Q) :
    swapRow (swapRow p) = p := by
  cases p
  rfl

/-- Finite graphs with complete actual pair orbitals preserved. Keeping
both sides in one fibre makes literal inverse maps available. -/
def Graph (G : Type t) {K : Type z} (Q : K → Type q)
    [Group G] [∀ k, MulAction G (Q k)] :=
  {F : Finset (Row Q) // ∀ p ∈ F, ∀ q ∈ F,
    GroupActions.orbital (G := G) p.2.1 q.2.1 p.2.2 q.2.2}
  deriving Preorder

namespace Graph

variable {G : Type t} [Group G] {K : Type z} {Q : K → Type q}
variable [∀ k, MulAction G (Q k)]

noncomputable def comm (f : Graph G Q) : Graph G Q := by
  classical
  refine ⟨f.val.image swapRow, ?_⟩
  intro p hp q hq
  obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨g, hgp, hgq⟩ := f.property p' hp' q' hq'
  refine ⟨g⁻¹, ?_, ?_⟩
  · change g⁻¹ • p'.2.2 = p'.2.1
    rw [← hgp, inv_smul_smul]
  · change g⁻¹ • q'.2.2 = q'.2.1
    rw [← hgq, inv_smul_smul]

@[simp] theorem mem_comm (f : Graph G Q) (p : Row Q) :
    p ∈ f.comm.val ↔ swapRow p ∈ f.val := by
  classical
  change p ∈ f.val.image swapRow ↔ swapRow p ∈ f.val
  constructor
  · rintro h
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp h
    simpa only [swapRow_swapRow] using hr
  · intro h
    exact Finset.mem_image.mpr ⟨swapRow p, h, swapRow_swapRow p⟩

@[simp] theorem comm_comm (f : Graph G Q) : f.comm.comm = f := by
  apply Subtype.ext
  ext p
  simp only [mem_comm, swapRow_swapRow]

theorem comm_mono {f g : Graph G Q} (h : f ≤ g) : f.comm ≤ g.comm := by
  intro p hp
  exact (mem_comm g p).mpr (h ((mem_comm f p).mp hp))

/-- A finite graph is single-valued in each actual named sort. -/
theorem functional (f : Graph G Q) (k : K) (a b c : Q k)
    (hab : (⟨k, a, b⟩ : Row Q) ∈ f.val)
    (hac : (⟨k, a, c⟩ : Row Q) ∈ f.val) : b = c := by
  obtain ⟨g, hgb, hgc⟩ := f.property _ hab _ hac
  exact hgb.symm.trans hgc

/-- The inverse graph is also single-valued, so finite graph maps are
injections without any separate freshness premise. -/
theorem injective (f : Graph G Q) (k : K) (a b c : Q k)
    (hac : (⟨k, a, c⟩ : Row Q) ∈ f.val)
    (hbc : (⟨k, b, c⟩ : Row Q) ∈ f.val) : a = b := by
  obtain ⟨g, hga, hgb⟩ := f.property _ hac _ hbc
  have hEq : g • a = g • b := hga.trans hgb.symm
  have hInv := congrArg (fun r : Q k => g⁻¹ • r) hEq
  simpa only [inv_smul_smul] using hInv

end Graph

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- The C20 exact-kernel construction supplies genuine one-point
extension of these finite graphs. -/
theorem graph_one_point_extension
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G)
    (hHelly : HeterogeneousExactBallHelly S)
    {K : Type z} (Q : K → Type q) [∀ k, MulAction G (Q k)]
    (root : K → ι) (π : ∀ k, X (root k) → Q k)
    (ontoπ : ∀ k, Function.Surjective (π k))
    (equivπ : ∀ k (g : G) c, π k (g • c) = g • π k c)
    (E : ∀ k, NonemptyExact S (root k) (root k))
    (hE : ∀ k, GroupActions.kernel (π k) = evaluate S (E k).words)
    (f : Graph G Q) (a : Sigma Q) :
    ∃ (g : Graph G Q) (b : Q a.1),
      (⟨a.1, a.2, b⟩ : Row Q) ∈ g.val ∧ f ≤ g := by
  classical
  let I := ↥f.val
  let sort : I → ι := fun p => root p.val.1
  let Q' : I → Type q := fun p => Q p.val.1
  let π' : ∀ p : I, X (sort p) → Q' p := fun p => π p.val.1
  let source : ∀ p : I, Q' p := fun p => p.val.2.1
  let target : ∀ p : I, Q' p := fun p => p.val.2.2
  have hPairs : ∀ p q : I,
      GroupActions.orbital (G := G)
        (source p) (source q) (target p) (target q) :=
    fun p q => f.property p.val p.property q.val q.property
  obtain ⟨x, hx⟩ := ontoπ a.1 a.2
  obtain ⟨y, hy⟩ := joint_real_point_requests_of_exact_kernels S H hHelly
    sort Q' π' (fun p => ontoπ p.val.1) (fun p => equivπ p.val.1)
    (fun p => E p.val.1) (fun p => hE p.val.1)
    x source target hPairs
  have hNew : ∀ p ∈ f.val,
      GroupActions.orbital (G := G)
        a.2 p.2.1 (π a.1 y) p.2.2 := by
    intro p hp
    obtain ⟨g, hgx, hgp⟩ := hy ⟨p, hp⟩
    refine ⟨g, ?_, hgp⟩
    calc
      g • a.2 = g • π a.1 x := congrArg (fun z => g • z) hx.symm
      _ = π a.1 (g • x) := (equivπ a.1 g x).symm
      _ = π a.1 y := congrArg (π a.1) hgx
  have hSelf : GroupActions.orbital (G := G)
      a.2 a.2 (π a.1 y) (π a.1 y) := by
    obtain ⟨g, hg⟩ := S.original_sort_transitive_of_homogeneous H (root a.1) x y
    have hπ : g • a.2 = π a.1 y := by
      rw [← hx, ← equivπ, hg]
    exact ⟨g, hπ, hπ⟩
  let r : Row Q := ⟨a.1, a.2, π a.1 y⟩
  have hValid : ∀ p ∈ insert r f.val, ∀ q ∈ insert r f.val,
      GroupActions.orbital (G := G) p.2.1 q.2.1 p.2.2 q.2.2 := by
    intro p hp q hq
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hSelf
      · exact hNew q hq
    · rcases Finset.mem_insert.mp hq with rfl | hq
      · obtain ⟨g, hgnew, hgp⟩ := hNew p hp
        exact ⟨g, hgp, hgnew⟩
      · exact f.property p hp q hq
  exact ⟨⟨insert r f.val, hValid⟩, π a.1 y,
    Finset.mem_insert_self _ _, Finset.subset_insert _ _⟩

end CCO.RawExact.JointBackAndForth
