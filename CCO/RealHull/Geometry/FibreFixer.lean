import CCO.RealHull.Geometry.Fixer
import CCO.RealHull.Geometry.FibrePalette

/-! Fibre-closed means WHOLE original classes stay in the actual fibre.
It has no connection with RAW word exactness. The canonical spoke fixer and
its containment in the actual palette precede every finite-Hasse argument. -/
universe v w t
namespace CCO.RealHull.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable [DecidableEq M] (A : Finset M) (q : ↥A → Atom S)
variable {G : Type t} [Group G] [MulAction G M]

def FibreClosed (R : Support S) : Prop :=
  ∀ x : FibreSet S A q, ∀ y : M, supportEquiv S R x.val y → y ∈ FibreSet S A q

theorem fibreClosed_fixed (H : HomogeneousSource S G)
    [Nonempty (FibreSet S A q)] (R : Support S) (hclosed : FibreClosed S A q R)
    (a : ↥A) : Fixed S R (q a) := by
  change prod S (plus S R.val) {some (q a)} = {some (q a)}
  apply eq_singleton_of_nonempty_subset
    (prod_nonempty S H (show (plus S R.val).Nonempty from ⟨none,none_mem_plus S _⟩)
      (Set.singleton_nonempty _))
  rintro c ⟨x,y,z,hxy,hyz,hxz⟩
  obtain ⟨b⟩ := ‹Nonempty (FibreSet S A q)›
  obtain ⟨g,hgy,hgz⟩ := S.pair_homogeneous_of_homogeneous H y b.val z a.val
    ((Set.mem_singleton_iff.mp hyz).trans (b.property a).symm)
  have hrel : supportEquiv S R (g • x) b.val := by
    change col S (g • x) b.val ∈ plus S R.val
    have hh := col_invariant S H g x y
    rw [hgy] at hh
    exact hh ▸ hxy
  have hF := hclosed b (g • x) ((supportEquiv S R).val.symm hrel)
  have hcolour : col S (g • x) a.val = c := by
    have hh := col_invariant S H g x z
    rw [hgz] at hh
    exact hh.trans hxz
  exact hcolour.symm.trans (hF a)

theorem fixed_fibreClosed (R : Support S) (hfix : ∀ a : ↥A, Fixed S R (q a)) :
    FibreClosed S A q R := by
  intro x y hrel a
  have hxy : col S x.val y ∈ plus S R.val := hrel
  have hh : col S y a.val ∈ prod S (plus S R.val) {some (q a)} :=
    ⟨y,x.val,a.val,(col_symm S y x.val) ▸ hxy,x.property a,rfl⟩
  rw [hfix a] at hh
  exact Set.mem_singleton_iff.mp hh

def fibreSpokeFixer (H : HomogeneousSource S G) : Support S := spokeFixer S H (Set.range q)

theorem fibreSpokeFixer_fixed (H : HomogeneousSource S G) (a : ↥A) :
    Fixed S (fibreSpokeFixer S A q H) (q a) :=
  spokeFixer_fixed S H (Set.range q) ⟨a,rfl⟩

theorem fibreSpokeFixer_closed (H : HomogeneousSource S G) :
    FibreClosed S A q (fibreSpokeFixer S A q H) :=
  fixed_fibreClosed S A q _ (fibreSpokeFixer_fixed S A q H)

theorem fibreClosed_le_palette (H : HomogeneousSource S G)
    [Nonempty (FibreSet S A q)] (R : Support S) (hclosed : FibreClosed S A q R)
    {d : Atom S} (hd : d ∈ R.val) : ∀ a : ↥A, d ∈ square S (q a) := by
  obtain ⟨x⟩ := ‹Nonempty (FibreSet S A q)›
  obtain ⟨y,hxy⟩ := colour_serial S H (some d) x.val
  have hrel : supportEquiv S R x.val y := by
    change col S x.val y ∈ plus S R.val
    rw [hxy]
    exact (some_mem_plus S _ _).mpr hd
  have hy := hclosed x y hrel
  intro a
  exact (mem_row S _ _ _).mpr ⟨x.val,a.val,y,x.property a,(col_symm S a.val y).trans (hy a),hxy⟩

theorem fibreSpokeFixer_le_palette (H : HomogeneousSource S G)
    [Nonempty (FibreSet S A q)] {d : Atom S}
    (hd : d ∈ (fibreSpokeFixer S A q H).val) : ∀ a : ↥A, d ∈ square S (q a) :=
  fibreClosed_le_palette S A q H _ (fibreSpokeFixer_closed S A q H) hd

theorem fibreSpokeFixer_largest (H : HomogeneousSource S G) (R : Support S)
    (hfix : ∀ a : ↥A, Fixed S R (q a)) :
    R.val ⊆ (fibreSpokeFixer S A q H).val := by
  apply support_le_spokeFixer S H R (Set.range q)
  rintro p ⟨a,rfl⟩
  exact hfix a

theorem supportEquiv_empty (R : Support S) (hR : R.val = ∅) :
    supportEquiv S R = (⊥ : ParityHasse.Original.ColourEq S ()) := by
  apply ParityHasse.Original.ColourEq.ext
  intro x y
  change col S x y ∈ plus S R.val ↔ x = y
  rw [hR]
  simpa [plus] using col_none S x y

@[simp] theorem fibreSet_empty (q : ↥(∅ : Finset M) → Atom S) :
    FibreSet S ∅ q = Set.univ := by
  apply Set.ext
  intro x
  change (∀ a : ↥(∅ : Finset M), col S x a.val = some (q a)) ↔ True
  constructor
  · intro _; trivial
  · intro _ a
    exact isEmptyElim a

end CCO.RealHull.Geometry
