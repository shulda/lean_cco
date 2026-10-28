import CCO.RealHull.Geometry.Algebra

/-! Global ORIGINAL invariant equivalence supports and their colour support
orbits. The optional logical equality remains in every represented product. -/

universe v w t
namespace CCO.RealHull.Geometry

open ParityHasse.Original
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

def plus (R : Set (Atom S)) : Set (FullColour S) := insert none (some '' R)

@[simp] theorem none_mem_plus (R : Set (Atom S)) : none ∈ plus S R := Set.mem_insert _ _
@[simp] theorem some_mem_plus (R : Set (Atom S)) (a : Atom S) : some a ∈ plus S R ↔ a ∈ R := by
  simp [plus]

def IsSupport (R : Set (Atom S)) : Prop := prod S (plus S R) (plus S R) ⊆ plus S R
abbrev Support := {R : Set (Atom S) // IsSupport S R}

def supportEquiv (R : Support S) : ColourEq S () :=
  ⟨{
    r := fun x y => col S x y ∈ plus S R.val
    iseqv := ⟨fun x => (col_none S x x).mpr rfl ▸ none_mem_plus S R.val,
      fun h => (col_symm S _ _) ▸ h,
      fun hxy hyz => R.property ⟨_,_,_,hxy,hyz,rfl⟩⟩
  }, fun x y x' y' hc => by
    change col S x y = col S x' y' at hc
    change (col S x y ∈ plus S R.val) ↔ (col S x' y' ∈ plus S R.val)
    rw [hc]⟩

def diversitySupport (E : ColourEq S ()) : Set (Atom S) :=
  {a | ∃ x y : M, E x y ∧ col S x y = some a}

theorem mem_diversitySupport (E : ColourEq S ()) {x y : M} {a : Atom S}
    (hc : col S x y = some a) : a ∈ diversitySupport S E ↔ E x y := by
  constructor
  · rintro ⟨u,v,huv,huvc⟩
    exact (E.property u v x y (huvc.trans hc.symm)).mp huv
  · intro hxy
    exact ⟨x,y,hxy,hc⟩

theorem mem_plus_diversitySupport (E : ColourEq S ()) (x y : M) :
    col S x y ∈ plus S (diversitySupport S E) ↔ E x y := by
  cases hc : col S x y with
  | none =>
    have he := (col_none S x y).mp hc
    subst y
    exact ⟨fun _ => E.val.refl x,fun _ => none_mem_plus S _⟩
  | some a => exact (some_mem_plus S _ a).trans (mem_diversitySupport S E hc)

def equivalenceSupport (E : ColourEq S ()) : Support S :=
  ⟨diversitySupport S E, by
    rintro c ⟨x,y,z,hxy,hyz,hxz⟩
    have hExy := (mem_plus_diversitySupport S E x y).mp hxy
    have hEyz := (mem_plus_diversitySupport S E y z).mp hyz
    exact hxz ▸ (mem_plus_diversitySupport S E x z).mpr (E.val.trans hExy hEyz)⟩

@[simp] theorem supportEquiv_equivalenceSupport (E : ColourEq S ()) :
    supportEquiv S (equivalenceSupport S E) = E := by
  apply ColourEq.ext
  exact mem_plus_diversitySupport S E

@[simp] theorem diversitySupport_supportEquiv (R : Support S) :
    diversitySupport S (supportEquiv S R) = R.val := by
  ext a
  obtain ⟨x,y,hc⟩ := colour_realized S (some a)
  rw [mem_diversitySupport S _ hc]
  change col S x y ∈ plus S R.val ↔ a ∈ R.val
  rw [hc,some_mem_plus]

theorem prod_support_self (R : Support S) :
    prod S (plus S R.val) (plus S R.val) = plus S R.val := by
  apply Set.Subset.antisymm R.property
  intro c hc
  obtain ⟨x,z,hxz⟩ := colour_realized S c
  exact ⟨x,x,z,(col_none S x x).mpr rfl ▸ none_mem_plus S _,hxz.symm ▸ hc,hxz⟩

def SupportOrbit (R : Support S) (u v : Atom S) : Prop :=
  some v ∈ prod S (plus S R.val) {some u}

theorem supportOrbit_refl (R : Support S) (u : Atom S) : SupportOrbit S R u u := by
  have hm : ({none} : Set (FullColour S)) ⊆ plus S R.val := by
    intro c hc
    exact Set.mem_singleton_iff.mp hc ▸ none_mem_plus S _
  have hbase : some u ∈ prod S {none} {some u} := by
    rw [prod_none_left]
    exact Set.mem_singleton _
  exact prod_mono S hm Set.Subset.rfl hbase

theorem supportOrbit_symm (R : Support S) {u v : Atom S}
    (h : SupportOrbit S R u v) : SupportOrbit S R v u := by
  obtain ⟨x,y,z,hR,hu,hv⟩ := h
  exact ⟨y,x,z,(col_symm S y x) ▸ hR,hv,Set.mem_singleton_iff.mp hu⟩

variable {G : Type t} [Group G] [MulAction G M]

theorem supportOrbit_trans (H : HomogeneousSource S G) (R : Support S) {u v z : Atom S}
    (huv : SupportOrbit S R u v) (hvz : SupportOrbit S R v z) : SupportOrbit S R u z := by
  have hsub : ({some v} : Set (FullColour S)) ⊆ prod S (plus S R.val) {some u} := by
    intro c hc
    exact Set.mem_singleton_iff.mp hc ▸ huv
  have ht := prod_mono S Set.Subset.rfl hsub hvz
  rw [← prod_assoc S H] at ht
  exact prod_mono S R.property Set.Subset.rfl ht

def supportOrbitSetoid (H : HomogeneousSource S G) (R : Support S) : Setoid (Atom S) where
  r := SupportOrbit S R
  iseqv := ⟨supportOrbit_refl S R, supportOrbit_symm S R, supportOrbit_trans S H R⟩

def Fixed (R : Support S) (p : Atom S) : Prop :=
  prod S (plus S R.val) {some p} = {some p}

theorem fixed_not_mem {R : Support S} {p : Atom S} (hfix : Fixed S R p) : p ∉ R.val := by
  intro hp
  have hn : none ∈ prod S (plus S R.val) {some p} :=
    (none_mem_prod S _ _).mpr ⟨some p,(some_mem_plus S _ _).mpr hp,Set.mem_singleton _⟩
  rw [hfix] at hn
  cases hn

theorem fixed_orbit {R : Support S} {p : Atom S} (hfix : Fixed S R p) (v : Atom S) :
    SupportOrbit S R p v ↔ v = p := by
  change some v ∈ prod S (plus S R.val) {some p} ↔ v = p
  rw [hfix]
  simp

end CCO.RealHull.Geometry
