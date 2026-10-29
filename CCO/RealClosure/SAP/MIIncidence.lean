import CCO.RealClosure.SAP.Monolith
import CCO.RealClosure.SAP.MIReconstruction

/-! C23–24: the ACTUALLY REALISED complete proper nonidentity MI tuple.
The full invariant lattice may be nondistributive. No arbitrary tuple
realization, automorphism section or quotient homogeneity is asserted. -/
universe v w t
namespace CCO.RealClosure.SAP
variable {M : Type v} {G : Type t} [Group G] [MulAction G M]
namespace InvariantEq

abbrev NonidentityMI (G : Type t) [Group G] (M : Type v) [MulAction G M] :=
  {E : InvariantEq G M // E ≠ ⊥ ∧ InfIrred E}

def miKernel : InvariantEq G M :=
  familyMeet (fun J : NonidentityMI G M => J.val)

theorem miKernel_eq_monolith (S : Source.{v,w} M) (H : S.Homogeneous (G := G))
    (sap : S.AgeSAP) [Infinite M] :
    (miKernel : InvariantEq G M) = monolith := by
  letI := finite S H
  have hm := monolith_property S H sap
  apply le_antisymm
  · apply (FiniteLattice.le_iff_forall_mi monolith miKernel).mpr
    intro J hLJ hJ
    have hne := (FiniteLattice.monolith_le_iff_ne_bot hm.1 hm.2 J).mp hLJ
    exact fun _ _ h => h ⟨J,hne,hJ⟩
  · exact le_familyMeet (fun J => hm.2 J.val J.property.1)

def quotientMap (E : InvariantEq G M) (g : G) : Quotient E.val → Quotient E.val :=
  Quotient.map (fun x => g • x) (fun _ _ h => E.property g _ _ h)

def Tuple (G : Type t) [Group G] (M : Type v) [MulAction G M] :=
  ∀ J : NonidentityMI G M, Quotient J.val.val

def tuple (x : M) : Tuple G M := fun J => Quotient.mk J.val.val x

def tupleAction (g : G) (q : Tuple G M) : Tuple G M :=
  fun J => quotientMap J.val g (q J)

@[simp] theorem tupleAction_tuple (g : G) (x : M) :
    tupleAction g (tuple (G := G) x) = tuple (g • x) := rfl

def tupleStabilizer (x : M) : Subgroup G where
  carrier := {g | tuple (g • x) = tuple (G := G) x}
  one_mem' := by simp only [one_smul,Set.mem_setOf_eq]
  mul_mem' := by
    intro g h hg hh
    funext J
    apply Quotient.sound
    have hgx : J.val (g • x) x := Quotient.exact (congrFun hg J)
    have hhx : J.val (h • x) x := Quotient.exact (congrFun hh J)
    change J.val ((g*h) • x) x
    rw [mul_smul]
    exact J.val.val.trans (J.val.property g _ _ hhx) hgx
  inv_mem' := by
    intro g hg
    funext J
    apply Quotient.sound
    have hgx : J.val (g • x) x := Quotient.exact (congrFun hg J)
    have hinv := J.val.property g⁻¹ _ _ hgx
    simp only [inv_smul_smul] at hinv
    exact J.val.val.symm hinv

theorem tuple_eq_iff (x y : M) :
    tuple (G := G) x = tuple y ↔ (miKernel : InvariantEq G M) x y := by
  constructor
  · intro h J
    exact Quotient.exact (congrFun h J)
  · intro h
    funext J
    exact Quotient.sound (h J)

/-- The fibre equality concerns a real tuple Phi(x), with every original
proper nonidentity MI included and identity explicitly excluded. -/
theorem tuple_fibre_eq (S : Source.{v,w} M) (H : S.Homogeneous (G := G))
    (sap : S.AgeSAP) [Infinite M] (x : M) :
    {y | tuple (G := G) y = tuple x} = {y | (monolith : InvariantEq G M) x y} := by
  ext y
  change tuple (G := G) y = tuple x ↔ (monolith : InvariantEq G M) x y
  rw [tuple_eq_iff,miKernel_eq_monolith S H sap]
  exact ⟨monolith.val.symm,monolith.val.symm⟩

theorem mem_tupleStabilizer_iff (S : Source.{v,w} M) (H : S.Homogeneous (G := G))
    (sap : S.AgeSAP) [Infinite M] (x : M) (g : G) :
    g ∈ tupleStabilizer x ↔ (monolith : InvariantEq G M) x (g • x) := by
  change tuple (G := G) (g • x) = tuple x ↔ _
  rw [tuple_eq_iff,miKernel_eq_monolith S H sap]
  exact ⟨monolith.val.symm,monolith.val.symm⟩

/-- Fixing the actual quotient tuple is EXACTLY preserving its entire
monolith class setwise, for the original ambient action. -/
theorem tupleStabilizer_iff_setwise (S : Source.{v,w} M) (H : S.Homogeneous (G := G))
    (sap : S.AgeSAP) [Infinite M] (x : M) (g : G) :
    g ∈ tupleStabilizer x ↔
      ∀ y : M, (monolith : InvariantEq G M) x (g • y) ↔ (monolith : InvariantEq G M) x y := by
  rw [mem_tupleStabilizer_iff S H sap]
  constructor
  · intro hx y
    constructor
    · intro hy
      have hxy : (monolith : InvariantEq G M) (g • x) (g • y) :=
        monolith.val.trans (monolith.val.symm hx) hy
      exact (apply_smul_iff monolith g x y).mp hxy
    · intro hy
      exact monolith.val.trans hx (monolith.property g x y hy)
  · intro h
    exact (h x).mpr (monolith.val.refl x)

theorem tuple_stabilizer_orbit (S : Source.{v,w} M) (H : S.Homogeneous (G := G))
    (sap : S.AgeSAP) [Infinite M] (x : M) :
    {y | ∃ g : G, g ∈ tupleStabilizer x ∧ g • x = y} =
      {y | (monolith : InvariantEq G M) x y} := by
  ext y
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact (mem_tupleStabilizer_iff S H sap x g).mp hg
  · intro hy
    obtain ⟨g,hg⟩ := Source.Homogeneous.transitive S H x y
    exact ⟨g,(mem_tupleStabilizer_iff S H sap x g).mpr (hg ▸ hy),hg⟩

theorem tuple_fibre_infinite (S : Source.{v,w} M) (H : S.Homogeneous (G := G))
    (sap : S.AgeSAP) [Infinite M] (x : M) :
    Set.Infinite {y | tuple (G := G) y = tuple x} := by
  rw [tuple_fibre_eq S H sap]
  exact monolith_class_infinite S H sap x

theorem tuple_stabilizer_orbit_infinite (S : Source.{v,w} M)
    (H : S.Homogeneous (G := G)) (sap : S.AgeSAP) [Infinite M] (x : M) :
    Set.Infinite {y | ∃ g : G, g ∈ tupleStabilizer x ∧ g • x = y} := by
  rw [tuple_stabilizer_orbit S H sap]
  exact monolith_class_infinite S H sap x

theorem empty_mi_monolith_top (S : Source.{v,w} M) (H : S.Homogeneous (G := G))
    (sap : S.AgeSAP) [Infinite M] [IsEmpty (NonidentityMI G M)] :
    (monolith : InvariantEq G M) = ⊤ := by
  rw [← miKernel_eq_monolith S H sap]
  apply ext
  intro x y
  exact iff_of_true (fun J => isEmptyElim J) trivial

theorem empty_mi_fibre (x : M) [IsEmpty (NonidentityMI G M)] :
    {y | tuple (G := G) y = tuple x} = Set.univ := by
  ext y
  exact iff_of_true (funext (fun J => isEmptyElim J)) trivial

end InvariantEq
end CCO.RealClosure.SAP
