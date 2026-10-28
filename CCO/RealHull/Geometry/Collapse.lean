import CCO.RealHull.Geometry.Rectangle
import CCO.RealHull.Geometry.Fixer

/-! Mixed single-orbit collapse and self-side square collapse on the original
RAW algebra. Logical equality outputs are excluded only by their actual test. -/
universe v w t
namespace CCO.RealHull.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M]

@[simp] theorem none_mem_atom_prod (a b : Atom S) :
    none ∈ prod S {some a} {some b} ↔ a = b := by
  rw [none_mem_prod]
  simp [eq_comm]

theorem row_nonempty (H : HomogeneousSource S G) (a b : Atom S) (hne : a ≠ b) :
    (row S a b).Nonempty := by
  obtain ⟨c,hc⟩ := prod_nonempty S H (Set.singleton_nonempty (some a)) (Set.singleton_nonempty (some b))
  cases c with
  | none => exact False.elim (hne ((none_mem_atom_prod S a b).mp hc))
  | some c => exact ⟨c,hc⟩

theorem fixed_product_saturated (H : HomogeneousSource S G)
    {R : Support S} {p : Atom S} (hfix : Fixed S R p) (a : Atom S) :
    prod S (plus S R.val) (prod S {some a} {some p}) = prod S {some a} {some p} := by
  rw [← prod_assoc S H,prod_comm S (plus S R.val),prod_assoc S H,hfix]

theorem mixed_same_orbit (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,0,w} S)
    (R : Support S) {p a : Atom S} (hfix : Fixed S R p) (hne : a ≠ p)
    (hcover : square S a ∩ square S p ⊆ R.val)
    {c d : Atom S} (hc : c ∈ row S a p) (hd : d ∈ row S a p) :
    SupportOrbit S R c d := by
  classical
  by_contra hnot
  obtain ⟨b,hb,hsep⟩ := relative_separator S H cco R {a,p}
    (fun t ht => hcover ⟨ht a (by simp),ht p (by simp)⟩) c d hnot
  have hbc : p ∈ row S a c := (mem_row S _ _ _).mpr
    (triangle_swap_first S ((mem_row S _ _ _).mp hc))
  have hbd : p ∈ row S a d := (mem_row S _ _ _).mpr
    (triangle_swap_first S ((mem_row S _ _ _).mp hd))
  have hpc : a ∈ row S p c := (row_peirce S a p c).mp hc
  have hpd : a ∈ row S p d := (row_peirce S a p d).mp hd
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact Set.disjoint_left.mp hsep hbc hbd
  · have he : b = p := Finset.mem_singleton.mp hb
    subst b
    exact Set.disjoint_left.mp hsep hpc hpd

theorem mixed_orbit_at (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,0,w} S)
    (R : Support S) {p a : Atom S} (hfix : Fixed S R p) (hne : a ≠ p)
    (hcover : square S a ∩ square S p ⊆ R.val)
    {c : Atom S} (hc : c ∈ row S a p) :
    row S a p = {d | SupportOrbit S R c d} := by
  ext d
  constructor
  · exact fun hd => mixed_same_orbit S H cco R hfix hne hcover hc hd
  · intro hd
    have hsub : ({some c} : Set (FullColour S)) ⊆ prod S {some a} {some p} := by
      intro t ht
      exact Set.mem_singleton_iff.mp ht ▸ hc
    have hh := prod_mono S Set.Subset.rfl hsub hd
    rw [fixed_product_saturated S H hfix a] at hh
    exact hh

theorem mixed_orbit (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,0,w} S)
    (R : Support S) {p a : Atom S} (hfix : Fixed S R p) (hne : a ≠ p)
    (hcover : square S a ∩ square S p ⊆ R.val) :
    ∃ c : Atom S, c ∈ row S a p ∧ row S a p = {d | SupportOrbit S R c d} := by
  obtain ⟨c,hc⟩ := row_nonempty S H a p hne
  exact ⟨c,hc,mixed_orbit_at S H cco R hfix hne hcover hc⟩

theorem self_side_collapse (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,0,w} S)
    (R : Support S) {p c : Atom S} (hfix : Fixed S R p)
    (hc : c ∈ square S p) (hcover : square S c ∩ square S p ⊆ R.val) :
    prod S {some p} {some c} = {some p} ∧ square S c ⊆ R.val := by
  have hne : c ≠ p := by
    rintro rfl
    exact fixed_not_mem S hfix (hcover ⟨hc,hc⟩)
  have hpc : p ∈ row S c p := by
    have hh : p ∈ row S p c := (row_peirce S p p c).mp hc
    rwa [row_symm S p c] at hh
  have hrow := mixed_orbit_at S H cco R hfix hne hcover hpc
  have hsingle : row S c p = {p} := by
    rw [hrow]
    ext d
    exact fixed_orbit S hfix d
  have hraw : prod S {some c} {some p} = {some p} := by
    ext t
    cases t with
    | none => simp only [none_mem_atom_prod,Set.mem_singleton_iff]; simp [hne]
    | some d =>
      change d ∈ row S c p ↔ some d ∈ ({some p} : Set (FullColour S))
      rw [hsingle]
      simp
  have hpraw : prod S {some p} {some c} = {some p} := by rw [prod_comm]; exact hraw
  refine ⟨hpraw,?_⟩
  intro x hx
  have hdouble : prod S {some p} (prod S {some c} {some c}) = {some p} := by
    rw [← prod_assoc S H,hpraw,hpraw]
  have hxsub : ({some x} : Set (FullColour S)) ⊆ prod S {some c} {some c} := by
    intro t ht
    exact Set.mem_singleton_iff.mp ht ▸ hx
  have hsub : prod S {some p} {some x} ⊆ {some p} := by
    intro t ht
    have hh := prod_mono S (Set.Subset.rfl : ({some p} : Set (FullColour S)) ⊆ _) hxsub ht
    rw [hdouble] at hh
    exact hh
  have hpx := eq_singleton_of_nonempty_subset
    (prod_nonempty S H (Set.singleton_nonempty (some p)) (Set.singleton_nonempty (some x))) hsub
  have hp : some p ∈ prod S {some p} {some x} := by rw [hpx]; exact Set.mem_singleton _
  have hxp : x ∈ square S p := (optional_peirce S (some p) (some p) (some x)).mpr hp
  exact hcover ⟨hx,hxp⟩

end CCO.RealHull.Geometry
