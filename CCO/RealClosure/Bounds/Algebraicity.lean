import CCO.RealClosure.Bounds.Directions
import CCO.RealHull.Canonical.Source
import CCO.RealHull.Geometry.Globalisation

/-! Real algebraicity is the FINITE ACTUAL pointwise-base stabilizer orbit;
definability is its actual fixed-point condition. The canonical hull supplies
its precise original minimal-direction criterion, without exactness of Gamma.
-/
universe v w t
namespace CCO.RealClosure.Bounds
open ParityHasse.Original RealHull.Geometry RealHull.Canonical
variable {M : Type v}

def orbitOver (G : Type t) [Group G] [MulAction G M] (A : Finset M) (x : M) : Set M :=
  {y | ∃ g : G, (∀ a ∈ A, g • a = a) ∧ g • x = y}
def Acl (G : Type t) [Group G] [MulAction G M] (A : Finset M) : Set M :=
  {x | (orbitOver G A x).Finite}
def Dcl (G : Type t) [Group G] [MulAction G M] (A : Finset M) : Set M :=
  {x | ∀ g : G, (∀ a ∈ A, g • a = a) → g • x = x}

variable (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M]

theorem self_mem_orbit (A : Finset M) (x : M) : x ∈ orbitOver G A x :=
  ⟨1,fun _ _ => one_smul _ _,one_smul _ _⟩
theorem parameter_mem_dcl (A : Finset M) {x : M} (hx : x ∈ A) : x ∈ Dcl G A :=
  fun _ hg => hg x hx

theorem dcl_subset_acl (A : Finset M) : Dcl G A ⊆ Acl G A := by
  intro x hx
  apply (Set.finite_singleton x).subset
  rintro y ⟨g,hg,rfl⟩
  exact Set.mem_singleton_iff.mpr (hx g hg)

theorem parameter_mem_acl (A : Finset M) {x : M} (hx : x ∈ A) : x ∈ Acl G A :=
  dcl_subset_acl A (parameter_mem_dcl A hx)

theorem acl_mono {A B : Finset M} (hAB : A ⊆ B) : Acl G A ⊆ Acl G B := by
  intro x hx
  apply hx.subset
  rintro y ⟨g,hg,hgy⟩
  exact ⟨g,fun a ha => hg a (hAB ha),hgy⟩

theorem acl_finite_source [Finite M] (A : Finset M) : Acl G A = Set.univ := by
  ext x
  exact iff_of_true (Set.toFinite _) trivial

variable [DecidableEq M]

/-- The actual complete spoke fibre is the actual stabilizer orbit. -/
theorem algebraic_fibre_finite (H : HomogeneousSource S G)
    (A : Finset M) (x : M) (hx : x ∉ A) (ha : x ∈ Acl G A) :
    Finite (FibreSet S A (actualSpokes S A x hx)) := by
  have heq : orbitOver G A x = FibreSet S A (actualSpokes S A x hx) :=
    fibre_orbit_eq S A _ H (actualFibrePoint S A x hx)
  have hf : (FibreSet S A (actualSpokes S A x hx)).Finite := heq ▸ ha
  exact hf.to_subtype

/-- C09: original finite classes, with no exactness hypothesis on Gamma. -/
theorem algebraic_iff_canonical_finite (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (A : Finset M) (x : M) (hx : x ∉ A) :
    x ∈ Acl G A ↔ FiniteClasses S
      (supportEquiv S (canonicalSupport S A (actualSpokes S A x hx))) := by
  constructor
  · intro ha
    let q := actualSpokes S A x hx
    letI : Nonempty (FibreSet S A q) := ⟨actualFibrePoint S A x hx⟩
    letI : Finite (FibreSet S A q) := algebraic_fibre_finite S H A x hx ha
    exact fun z => (canonical_class_finite_bound S A q H cco z).1
  · intro hfinite
    have hh : Finite (actualHull S A x) := by
      rw [actualHull,dif_neg hx,canonicalHull_eq_class S A _ (actualFibrePoint S A x hx)]
      exact hfinite x
    exact finite_hull_implies_finite_orbit S H A x hx (Set.finite_coe_iff.mp hh)

theorem finiteClasses_iff_no_direction (E : ColourEq S ()) :
    FiniteClasses S E ↔ ∀ D : Direction S, ¬ D.val ≤ E := by
  constructor
  · intro h D hDE
    exact D.property.1 (finiteClasses_of_le S hDE h)
  · intro h
    by_contra hn
    obtain ⟨D,hD⟩ := exists_direction_le S hn
    exact h D hD

theorem le_canonical_iff (E : ColourEq S ()) (A : Finset M) (q : ↥A → Atom S) :
    E ≤ supportEquiv S (canonicalSupport S A q) ↔ ∀ a : ↥A, E ≤ gammaEq S (q a) := by
  constructor
  · intro h a x y hxy
    exact (canonical_equiv_iff S A q x y).mp (h hxy) a
  · intro h x y hxy
    exact (canonical_equiv_iff S A q x y).mpr (fun a => h a hxy)

/-- Every minimal infinite direction is excluded by an ACTUAL spoke. -/
theorem algebraic_iff_directions (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (A : Finset M) (x : M) (hx : x ∉ A) :
    x ∈ Acl G A ↔ ∀ D : Direction S, ∃ a : ↥A,
      ¬ D.val ≤ gammaEq S (actualSpokes S A x hx a) := by
  rw [algebraic_iff_canonical_finite S H cco A x hx,finiteClasses_iff_no_direction S]
  constructor
  · intro h D
    by_contra hn
    apply h D
    apply (le_canonical_iff S D.val A _).mpr
    intro a
    by_contra ha
    exact hn ⟨a,ha⟩
  · intro h D hle
    obtain ⟨a,ha⟩ := h D
    exact ha ((le_canonical_iff S D.val A _).mp hle a)

/-- C10: one actual parameter per direction, with finite/parameter cases. -/
theorem bounded_character (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (A : Finset M) {x : M} (hx : x ∈ Acl G A) :
    ∃ B : Finset M, B ⊆ A ∧ B.card ≤ directionCount S ∧ x ∈ Acl G B := by
  classical
  by_cases hfin : Finite M
  · letI := hfin
    exact ⟨∅,Finset.empty_subset _,Nat.zero_le _,by rw [acl_finite_source]; trivial⟩
  · letI : Infinite M := not_finite_iff_infinite.mp hfin
    by_cases hxA : x ∈ A
    · refine ⟨{x},Finset.singleton_subset_iff.mpr hxA,?_,parameter_mem_acl _ (Finset.mem_singleton_self _)⟩
      simpa only [Finset.card_singleton] using (Nat.succ_le_iff.mpr (directionCount_pos S))
    · have hdir := (algebraic_iff_directions S H cco A x hxA).mp hx
      choose f hf using hdir
      letI : Fintype (Direction S) := Fintype.ofFinite _
      let B : Finset M := Finset.univ.image (fun D : Direction S => (f D).val)
      have hBA : B ⊆ A := by
        intro a ha
        obtain ⟨D,_,rfl⟩ := Finset.mem_image.mp ha
        exact (f D).property
      have hxB : x ∉ B := fun h => hxA (hBA h)
      refine ⟨B,hBA,?_,?_⟩
      · exact (Finset.card_image_le).trans (by simp only [Finset.card_univ,directionCount,Nat.card_eq_fintype_card]; exact le_rfl)
      · apply (algebraic_iff_directions S H cco B x hxB).mpr
        intro D
        let b : ↥B := ⟨(f D).val,Finset.mem_image.mpr ⟨D,Finset.mem_univ _,rfl⟩⟩
        refine ⟨b,?_⟩
        have hspoke : actualSpokes S B x hxB b = actualSpokes S A x hxA (f D) :=
          Option.some.inj ((actualSpokes_colour S B x hxB b).symm.trans
            (actualSpokes_colour S A x hxA (f D)))
        rw [hspoke]
        exact hf D

theorem acl_bounded_union (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (A : Finset M) :
    Acl G A = ⋃ (B : Finset M) (_ : B ⊆ A) (_ : B.card ≤ directionCount S), Acl G B := by
  ext x
  constructor
  · intro hx
    obtain ⟨B,hBA,hcard,hxB⟩ := bounded_character S H cco A hx
    exact Set.mem_iUnion.mpr ⟨B,Set.mem_iUnion.mpr ⟨hBA,Set.mem_iUnion.mpr ⟨hcard,hxB⟩⟩⟩
  · intro hx
    obtain ⟨B,hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hBA,hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨_,hxB⟩ := Set.mem_iUnion.mp hx
    exact acl_mono hBA hxB
end CCO.RealClosure.Bounds
