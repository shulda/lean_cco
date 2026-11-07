import CCO.ExactCRT.SourceLattice
import CCO.RealClosure.SAP.MIReconstruction

/-! B057 C29-C30: reconstruction INSIDE the represented FULL RAW exact
lattice. The direct `ww` envelope must first supply `IsExactEq`; this
module never assumes that every original invariant equivalence is exact,
or that an exact-lattice MI is a named FULL-lattice coordinate. -/

universe u v w t
namespace CCO.GuardedOldSeams
open CCO.ExactCRT
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

/-- The actual accepted exact/Helly/CRT source instance, independently
of SAP, terminality, or any assertion about ALL invariant equivalences. -/
theorem represented_exact_distributive (i : ι) :
    Nonempty (DistribLattice (ExactEq S H cco i)) :=
  ⟨exactDistribLattice S H cco i⟩

/-- All proper meet-irreducibles above this ACTUAL exact equivalence.
`InfIrred` excludes Top; the family is empty when the equivalence is Top. -/
abbrev representedExactMIFamily {i : ι} (E : ExactEq S H cco i) :=
  {J : ExactEq S H cco i // E ≤ J ∧ InfIrred J}

/-- A finite intersection in the actual exact subtype has its literal
pointwise meaning as an intersection of represented old relations. -/
theorem represented_exact_finset_inf_apply {i : ι}
    (family : Finset (ExactEq S H cco i)) (x y : X i) :
    (family.inf id).val x y ↔ ∀ J ∈ family, J.val x y := by
  classical
  induction family using Finset.induction_on with
  | empty =>
    rw [Finset.inf_empty]
    constructor
    · intro _ J hJ
      exact False.elim (by simpa using hJ)
    · intro _
      trivial
  | @insert J family hJ ih =>
    rw [Finset.inf_insert]
    change (J.val x y ∧ (family.inf id).val x y) ↔ _
    constructor
    · rintro ⟨hJxy,hFamily⟩ K hK
      rcases Finset.mem_insert.mp hK with hK | hK
      · subst K
        exact hJxy
      · exact ih.mp hFamily K hK
    · intro h
      refine ⟨h J (Finset.mem_insert_self J family), ?_⟩
      exact ih.mpr (fun K hK => h K (Finset.mem_insert_of_mem hK))

/-- Finite exact MI reconstruction, including the ordinary empty Top
meet. The ambient type is EXACT, not the full invariant lattice. -/
theorem represented_exact_miMeet_eq {i : ι} (E : ExactEq S H cco i) :
    CCO.RealClosure.SAP.FiniteLattice.miMeet E = E :=
  CCO.RealClosure.SAP.FiniteLattice.miMeet_eq E

/-- Literal source TF1 at every actual original pair. No quotient section
or assumed intersection representation is a premise. -/
theorem represented_exact_mi_pointwise {i : ι}
    (E : ExactEq S H cco i) (x y : X i) :
    E.val x y ↔ ∀ J : ExactEq S H cco i,
      E ≤ J → InfIrred J → J.val x y := by
  classical
  letI : Fintype (ExactEq S H cco i) := Fintype.ofFinite _
  have hMeet := represented_exact_miMeet_eq S H cco E
  have hPair := congrArg (fun J : ExactEq S H cco i => J.val x y) hMeet
  calc
    E.val x y ↔ (CCO.RealClosure.SAP.FiniteLattice.miMeet E).val x y :=
      (Iff.of_eq hPair).symm
    _ ↔ ∀ J : ExactEq S H cco i, E ≤ J → InfIrred J → J.val x y := by
      change ((Finset.univ.filter fun J : ExactEq S H cco i =>
        E ≤ J ∧ InfIrred J).inf id).val x y ↔ _
      rw [represented_exact_finset_inf_apply S H cco]
      constructor
      · intro h J hEJ hJ
        exact h J (Finset.mem_filter.mpr ⟨Finset.mem_univ J,hEJ,hJ⟩)
      · intro h J hJ
        exact h J (Finset.mem_filter.mp hJ).2.1 (Finset.mem_filter.mp hJ).2.2

/-- The actual represented-MI intersection as a FULL equality-inclusive
old equivalence relation. This object admits an empty coordinate family. -/
def representedExactMIIntersection {i : ι} (E : ExactEq S H cco i) :
    Setoid (X i) :=
  CCO.ExactCRT.Abstract.familyMeet
    (fun J : representedExactMIFamily S H cco E => J.val.val)

/-- Actual relation equality, rather than only an order-embedding into
coordinates or an assumed exactness of every original invariant. -/
theorem represented_exact_mi_intersection_eq {i : ι}
    (E : ExactEq S H cco i) :
    representedExactMIIntersection S H cco E = E.val := by
  apply Setoid.ext
  intro x y
  constructor
  · intro h
    apply (represented_exact_mi_pointwise S H cco E x y).mpr
    intro J hEJ hJ
    exact h ⟨J,hEJ,hJ⟩
  · intro h J
    exact (represented_exact_mi_pointwise S H cco E x y).mp h
      J.val J.property.1 J.property.2

/-- Empty represented-MI family has the ambient universal relation as
its meet, even in the one-element exact lattice. -/
theorem represented_exact_eq_top_of_no_mi {i : ι}
    (E : ExactEq S H cco i)
    (none : ∀ J : ExactEq S H cco i, E ≤ J → ¬InfIrred J) :
    E = ⊤ :=
  CCO.RealClosure.SAP.FiniteLattice.eq_top_of_no_mi E none

/-- A direct `ww` proof may enter the actual exact lattice through this
constructor-facing form. No general all-invariants-exact premise enters. -/
theorem represented_exact_mi_of_isExact {i : ι}
    (E : Setoid (X i)) (hE : IsExactEq S E) (x y : X i) :
    E x y ↔ ∀ J : ExactEq S H cco i,
      (∀ a b, E a b → J.val a b) → InfIrred J → J.val x y :=
  represented_exact_mi_pointwise S H cco ⟨E,hE⟩ x y

/-- For a nonidentity envelope, no represented MI above it can be the
logical equality kernel. This says nothing about naming that quotient. -/
theorem represented_exact_above_nonidentity_ne_bot {i : ι}
    (E J : ExactEq S H cco i) (nonidentity : (⊥ : ExactEq S H cco i) < E)
    (above : E ≤ J) : J ≠ ⊥ := by
  intro hJ
  exact (not_le_of_gt nonidentity) (hJ ▸ above)

end
end CCO.GuardedOldSeams
