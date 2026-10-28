import CCO.RealHull.Geometry.Supports

/-! The canonical original spoke fixer is globally composition-closed BEFORE
any finiteness, CCO or internal-equivalence argument. -/
universe v w t
namespace CCO.RealHull.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

theorem eq_singleton_of_nonempty_subset {A : Type*} {U : Set A} {a : A}
    (hne : U.Nonempty) (hsub : U ⊆ {a}) : U = {a} := by
  apply Set.Subset.antisymm hsub
  obtain ⟨x,hx⟩ := hne
  have hxa : x = a := Set.mem_singleton_iff.mp (hsub hx)
  intro y hy
  have hya : y = a := Set.mem_singleton_iff.mp hy
  exact hya.symm ▸ hxa ▸ hx

def spokeFixerSet (P : Set (Atom S)) : Set (Atom S) :=
  {d | ∀ p ∈ P, prod S {some p} {some d} = {some p}}

theorem mem_plus_spokeFixerSet (P : Set (Atom S)) (c : FullColour S) :
    c ∈ plus S (spokeFixerSet S P) ↔
      ∀ p ∈ P, prod S {some p} {c} = {some p} := by
  cases c with
  | none => simp only [none_mem_plus,prod_none_right,implies_true]
  | some d => rw [some_mem_plus]; rfl

variable {G : Type t} [Group G] [MulAction G M]

def spokeFixer (H : HomogeneousSource S G) (P : Set (Atom S)) : Support S :=
  ⟨spokeFixerSet S P, by
    rintro c ⟨x,y,z,hxy,hyz,hxz⟩
    apply (mem_plus_spokeFixerSet S P c).mpr
    intro p hp
    have ha := (mem_plus_spokeFixerSet S P (col S x y)).mp hxy p hp
    have hb := (mem_plus_spokeFixerSet S P (col S y z)).mp hyz p hp
    have hc : ({c} : Set (FullColour S)) ⊆ prod S {col S x y} {col S y z} := by
      intro r hr
      exact Set.mem_singleton_iff.mp hr ▸ ⟨x,y,z,rfl,rfl,hxz⟩
    have hsub : prod S {some p} {c} ⊆ {some p} := by
      have heq : prod S {some p} (prod S {col S x y} {col S y z}) = {some p} := by
        rw [← prod_assoc S H,ha,hb]
      intro r hr
      have hh := prod_mono S (Set.Subset.rfl : ({some p} : Set (FullColour S)) ⊆ _) hc hr
      rw [heq] at hh
      exact hh
    exact eq_singleton_of_nonempty_subset
      (prod_nonempty S H (Set.singleton_nonempty _) (Set.singleton_nonempty _)) hsub⟩

theorem spokeFixer_fixed (H : HomogeneousSource S G) (P : Set (Atom S))
    {p : Atom S} (hp : p ∈ P) : Fixed S (spokeFixer S H P) p := by
  change prod S (plus S (spokeFixerSet S P)) {some p} = {some p}
  apply eq_singleton_of_nonempty_subset
    (prod_nonempty S H (show (plus S (spokeFixerSet S P)).Nonempty from ⟨none,none_mem_plus S _⟩)
      (Set.singleton_nonempty _))
  rintro c ⟨x,y,z,hxy,hyz,hxz⟩
  have hf := (mem_plus_spokeFixerSet S P (col S x y)).mp hxy p hp
  have hc : c ∈ prod S {col S x y} {some p} := ⟨x,y,z,rfl,hyz,hxz⟩
  rw [prod_comm S {col S x y},hf] at hc
  exact hc

theorem support_le_spokeFixer (H : HomogeneousSource S G) (R : Support S)
    (P : Set (Atom S)) (hfix : ∀ p ∈ P, Fixed S R p) :
    R.val ⊆ (spokeFixer S H P).val := by
  intro d hd p hp
  apply eq_singleton_of_nonempty_subset
    (prod_nonempty S H (Set.singleton_nonempty _) (Set.singleton_nonempty _))
  have hsub : ({some d} : Set (FullColour S)) ⊆ plus S R.val := by
    intro c hc
    exact Set.mem_singleton_iff.mp hc ▸ (some_mem_plus S _ _).mpr hd
  have hh := prod_mono S (Set.Subset.rfl : ({some p} : Set (FullColour S)) ⊆ _) hsub
  have hpr : prod S {some p} (plus S R.val) = {some p} :=
    (prod_comm S _ _).trans (hfix p hp)
  rw [hpr] at hh
  exact hh

end CCO.RealHull.Geometry
