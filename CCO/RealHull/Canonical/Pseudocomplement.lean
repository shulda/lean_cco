import CCO.RealHull.Geometry.Localisation
import CCO.RealHull.Geometry.GeneratedSupport

/-! Relative pseudocomplement in the ORIGINAL equality-inclusive support
algebra. No word exactness or infinite compactness enters these arguments. -/
universe v w t
namespace CCO.RealHull.Canonical
open Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M]

def pseudoSet (R : Support S) (P : Finset (Atom S)) : Set (Atom S) :=
  {a | square S a ∩ squareMeet S P ⊆ R.val}

theorem square_le_support (R : Support S) {a : Atom S} (ha : a ∈ R.val) :
    square S a ⊆ R.val := by
  have hs : ({some a} : Set (FullColour S)) ⊆ plus S R.val := by
    intro c hc
    exact Set.mem_singleton_iff.mp hc ▸ (some_mem_plus S _ _).mpr ha
  exact fun _ hx => (some_mem_plus S _ _).mp (R.property (prod_mono S hs hs hx))

theorem support_le_pseudo (R : Support S) (P : Finset (Atom S)) :
    R.val ⊆ pseudoSet S R P :=
  fun _ ha _ hx => square_le_support S R ha hx.1

theorem fixed_square_stable (H : HomogeneousSource S G) (R : Support S)
    {p : Atom S} (hp : Fixed S R p) :
    prod S (plus S R.val) (prod S {some p} {some p}) = prod S {some p} {some p} := by
  rw [← prod_assoc S H, hp]

theorem support_le_fixed_square (H : HomogeneousSource S G) (R : Support S)
    {p : Atom S} (hp : Fixed S R p) : R.val ⊆ square S p := by
  intro a ha
  have hn : ({none} : Set (FullColour S)) ⊆ prod S {some p} {some p} := by
    intro c hc
    have hnone := (none_mem_prod S {some p} {some p}).mpr
      ⟨some p,Set.mem_singleton _,Set.mem_singleton _⟩
    exact Set.mem_singleton_iff.mp hc ▸ hnone
  have hbase : some a ∈ prod S (plus S R.val) {none} := by
    rw [prod_none_right]
    exact (some_mem_plus S _ _).mpr ha
  have hh := prod_mono S Set.Subset.rfl hn hbase
  rwa [fixed_square_stable S H R hp] at hh

theorem supportOrbit_mem_iff (R : Support S) {a b : Atom S}
    (hab : SupportOrbit S R a b) : a ∈ R.val ↔ b ∈ R.val := by
  have aux : ∀ {a b : Atom S}, SupportOrbit S R a b → a ∈ R.val → b ∈ R.val := by
    intro a b h ha
    have hs : ({some a} : Set (FullColour S)) ⊆ plus S R.val := by
      intro c hc
      exact Set.mem_singleton_iff.mp hc ▸ (some_mem_plus S _ _).mpr ha
    exact (some_mem_plus S _ _).mp (R.property (prod_mono S Set.Subset.rfl hs h))
  exact ⟨aux hab,aux (supportOrbit_symm S R hab)⟩

/-- C25. Full optional equality is retained in the calculation; an equality
output would put the input in R, so it cannot occur outside R. -/
theorem equality_excluded_outside (R : Support S) {a : Atom S} (ha : a ∉ R.val) :
    none ∉ prod S (plus S R.val) {some a} := by
  intro h
  obtain ⟨d,hdR,hda⟩ := (none_mem_prod S _ _).mp h
  have he : d = some a := Set.mem_singleton_iff.mp hda
  exact ha ((some_mem_plus S _ a).mp (he ▸ hdR))

theorem fixed_square_outside_saturated (H : HomogeneousSource S G) (R : Support S)
    {p a b : Atom S} (hp : Fixed S R p) (ha : a ∈ square S p) (haR : a ∉ R.val)
    (hab : SupportOrbit S R a b) : b ∈ square S p ∧ b ∉ R.val := by
  have hs : ({some a} : Set (FullColour S)) ⊆ prod S {some p} {some p} := by
    intro c hc
    exact Set.mem_singleton_iff.mp hc ▸ ha
  have hh := prod_mono S Set.Subset.rfl hs hab
  rw [fixed_square_stable S H R hp] at hh
  exact ⟨hh,fun hb => haR ((supportOrbit_mem_iff S R hab).mpr hb)⟩

theorem fixed_meet_outside_saturated (H : HomogeneousSource S G) (R : Support S)
    (P : Finset (Atom S)) (hfix : ∀ p ∈ P, Fixed S R p)
    {a b : Atom S} (ha : a ∈ squareMeet S P) (haR : a ∉ R.val)
    (hab : SupportOrbit S R a b) : b ∈ squareMeet S P ∧ b ∉ R.val := by
  exact ⟨fun p hp => (fixed_square_outside_saturated S H R (hfix p hp) (ha p hp) haR hab).1,
    fun hb => haR ((supportOrbit_mem_iff S R hab).mpr hb)⟩

/-- C26, including the equality intermediate and the d=a branch. -/
theorem pseudo_square_closed (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,0,w} S)
    (R : Support S) (P : Finset (Atom S)) (hfix : ∀ p ∈ P, Fixed S R p)
    {a : Atom S} (ha : a ∈ pseudoSet S R P) {x : Atom S} (hx : x ∈ square S a) :
    x ∈ pseudoSet S R P := by
  classical
  intro t ht
  by_contra htR
  have hsub : ({some x} : Set (FullColour S)) ⊆ prod S {some a} {some a} := by
    intro c hc
    exact Set.mem_singleton_iff.mp hc ▸ hx
  have hh := prod_mono S hsub Set.Subset.rfl ht.1
  rw [prod_assoc S H] at hh
  obtain ⟨d,hd,htad⟩ := prod_choose_right S hh
  cases d with
  | none =>
    have hxa : x = a := (none_mem_atom_prod S a x).mp hd |>.symm
    rw [prod_none_right] at htad
    have hta : t = a := Option.some.inj (Set.mem_singleton_iff.mp htad)
    exact htR (ha ⟨by simpa only [hxa,hta] using hx, ht.2⟩)
  | some d =>
    by_cases hda : d = a
    · subst d
      exact htR (ha ⟨htad,ht.2⟩)
    have hxrow : x ∈ row S a d := by
      change some x ∈ prod S {some a} {some d}
      apply (row_peirce S x a d).mp
      rwa [row_symm S x a]
    have horb : SupportOrbit S R a d := by
      by_contra hn
      obtain ⟨p,hp,hsep⟩ := relative_separator S H cco R (insert a P)
        (fun c hc => ha ⟨hc a (Finset.mem_insert_self _ _),
          fun p hp => hc p (Finset.mem_insert_of_mem hp)⟩) a d hn
      have hmeet : (row S p a ∩ row S p d).Nonempty := by
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact ⟨x,hx,hxrow⟩
        · exact (rectangle S H p a d (Ne.symm hda)).mpr ⟨t,ht.2 p hp,htad⟩
      exact Set.disjoint_left.mp hsep hmeet.choose_spec.1 hmeet.choose_spec.2
    obtain ⟨t',ht'a,ht'R,ht't⟩ := orbit_folding S H R a d t horb htad htR
    have ht'S := (fixed_meet_outside_saturated S H R P hfix ht.2 htR
      (supportOrbit_symm S R ht't)).1
    exact ht'R (ha ⟨ht'a,ht'S⟩)

/-- C27. The original mixed product retains its true equality atom. -/
theorem pseudo_mixed_closed (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,0,w} S)
    (R : Support S) (P : Finset (Atom S)) (hfix : ∀ p ∈ P, Fixed S R p)
    {a b c : Atom S} (hab : a ≠ b) (ha : a ∈ pseudoSet S R P)
    (hb : b ∈ pseudoSet S R P) (hc : c ∈ row S a b) : c ∈ pseudoSet S R P := by
  classical
  intro t ht
  by_contra htR
  have hct : c ∈ row S c t := (row_peirce S c c t).mp ht.1
  have hs : ({some c} : Set (FullColour S)) ⊆ prod S {some a} {some b} := by
    intro e he
    exact Set.mem_singleton_iff.mp he ▸ hc
  have hh := prod_mono S hs Set.Subset.rfl hct
  rw [prod_assoc S H] at hh
  obtain ⟨d,hd,hcad⟩ := prod_choose_right S hh
  cases d with
  | none =>
    have hbt : b = t := (none_mem_atom_prod S b t).mp hd
    rw [prod_none_right] at hcad
    have hca : c = a := Option.some.inj (Set.mem_singleton_iff.mp hcad)
    have hba : b ∈ square S a := by
      rw [hca] at hc
      exact (row_peirce S b a a).mp (by rwa [row_symm S b a])
    exact htR (ha ⟨by simpa only [← hbt] using hba,ht.2⟩)
  | some d =>
    have htd : t ∈ row S b d := by
      apply (row_peirce S t b d).mp
      rwa [row_symm S t b]
    by_cases hdb : d = b
    · subst d
      exact htR (hb ⟨htd,ht.2⟩)
    have horb : SupportOrbit S R b d := by
      by_contra hn
      obtain ⟨p,hp,hsep⟩ := relative_separator S H cco R (insert a P)
        (fun e he => ha ⟨he a (Finset.mem_insert_self _ _),
          fun p hp => he p (Finset.mem_insert_of_mem hp)⟩) b d hn
      have hmeet : (row S p b ∩ row S p d).Nonempty := by
        rcases Finset.mem_insert.mp hp with rfl | hp
        · exact ⟨c,hc,hcad⟩
        · exact (rectangle S H p b d (Ne.symm hdb)).mpr ⟨t,ht.2 p hp,htd⟩
      exact Set.disjoint_left.mp hsep hmeet.choose_spec.1 hmeet.choose_spec.2
    obtain ⟨t',ht'b,ht'R,ht't⟩ := orbit_folding S H R b d t horb htd htR
    have ht'S := (fixed_meet_outside_saturated S H R P hfix ht.2 htR
      (supportOrbit_symm S R ht't)).1
    exact ht'R (hb ⟨ht'b,ht'S⟩)

def pseudoSupport (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,0,w} S)
    (R : Support S) (P : Finset (Atom S)) (hfix : ∀ p ∈ P, Fixed S R p) : Support S :=
  ⟨pseudoSet S R P, by
    rintro e ⟨x,y,z,hxy,hyz,hxz⟩
    cases ha : col S x y with
    | none =>
      have he : x = y := (col_none S x y).mp ha
      subst y
      exact hxz ▸ hyz
    | some a =>
      have haW := (some_mem_plus S _ _).mp (ha ▸ hxy)
      cases hb : col S y z with
      | none =>
        have he : y = z := (col_none S y z).mp hb
        subst z
        exact hxz ▸ hxy
      | some b =>
        have hbW := (some_mem_plus S _ _).mp (hb ▸ hyz)
        cases e with
        | none => exact none_mem_plus S _
        | some c =>
          have hc : c ∈ row S a b := ⟨x,y,z,ha,hb,hxz⟩
          apply (some_mem_plus S _ _).mpr
          by_cases he : a = b
          · subst b
            exact pseudo_square_closed S H cco R P hfix haW hc
          · exact pseudo_mixed_closed S H cco R P hfix he haW hbW hc⟩
end CCO.RealHull.Canonical
