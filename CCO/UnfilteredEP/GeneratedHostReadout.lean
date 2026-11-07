import CCO.APRamseyReadout.HostReadout
import CCO.FullCode.CofinalEP

/-!
# A root-generated hidden host is the actual canonical visible support

The full arbitrary-host realization of B061 retains every compatible root.
When the old host is root-generated, its canonical support embedding is
onto. This gives the literal support equivalence needed to transport each
competing full order back onto the SAME chosen old hidden carrier.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w p z l k r
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section

section General
variable {L : Language.{l}} {V : Type v} {W : Type w}
variable {C : Structure L V} {D : Structure L W} {scheme : RootScheme L}

/-- A displayed mapped root retains every coordinate, including the
true equality cases between different coordinate presentations. -/
theorem root_coordinate_in_range (f : Structure.Embedding C D)
    (a : Root C scheme) (b : Root D scheme) (same : a.map f = b)
    (j : Fin (scheme.arity b.tag)) : b.coordinate j ∈ Set.range f.point := by
  subst b
  exact ⟨a.coordinate j,rfl⟩

/-- Inverting a bijective induced map retains full partial domains,
not merely the unary edges whose output was previously selected. -/
def inverseInduced (f : Structure.Embedding C D) (onto : Function.Surjective f.point) :
    Structure.Embedding D C := by
  let e : V ≃ W := Equiv.ofBijective f.point ⟨f.injective,onto⟩
  refine {
    point := e.symm
    injective := e.symm.injective
    sort_eq := ?_
    map_func := ?_
    reflect_func := ?_
    unary_iff := ?_
    binary_iff := ?_ }
  · intro x
    exact (f.sort_eq (e.symm x)).symm.trans
      (congrArg D.sort (e.apply_symm_apply x))
  · intro F x y hy
    have hy' : e (e.symm y) ∈ D.func F (e (e.symm x)) := by
      simpa only [e.apply_symm_apply] using hy
    obtain ⟨z,hz,he⟩ := f.reflect_func F (e.symm x) (e (e.symm y)) hy'
    exact (f.injective he) ▸ hz
  · intro F x y hy
    refine ⟨e y,?_,e.symm_apply_apply y⟩
    have hh := f.map_func F (e.symm x) y hy
    change e y ∈ D.func F (e (e.symm x)) at hh
    simpa only [e.apply_symm_apply] using hh
  · intro U x
    have hh := f.unary_iff U (e.symm x)
    exact hh.symm.trans (Iff.of_eq (congrArg (D.unary U) (e.apply_symm_apply x)))
  · intro R x y
    have hh := f.binary_iff R (e.symm x) (e.symm y)
    exact hh.symm.trans (Iff.of_eq (congrArg₂ (D.binary R)
      (e.apply_symm_apply x) (e.apply_symm_apply y)))

@[simp] theorem inverseInduced_apply (f : Structure.Embedding C D)
    (onto : Function.Surjective f.point) (x : V) :
    (inverseInduced f onto).point (f.point x) = x :=
  (Equiv.ofBijective f.point ⟨f.injective,onto⟩).symm_apply_apply x

@[simp] theorem apply_inverseInduced (f : Structure.Embedding C D)
    (onto : Function.Surjective f.point) (x : W) :
    f.point ((inverseInduced f onto).point x) = x :=
  (Equiv.ofBijective f.point ⟨f.injective,onto⟩).apply_symm_apply x

end General

variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)
variable {W : Type z} {C : CCO.UnarySupport.Structure (Sig B ht) W} [LinearOrder W]
variable (R : HostReadout B ht F C)
local notation "Γ" => actualTupleInterpretation B ht F

/-- Every whole host root has its full coordinate list in the image of
the same canonical support map. No independent representative is chosen. -/
theorem host_root_coordinates_in_support_range :
    (Object.full (CoordinateModel B ht C) (tupleScheme B ht F)).coordinates ⊆
      Set.range R.support.point := by
  rintro _ ⟨r,j,rfl⟩
  exact root_coordinate_in_range R.support
    (((Γ).object R.old).markedRoot (R.roots r)) r (R.support_root r) j

/-- C77's root-generated old host is EXACTLY the support of all its
visible roots. Empty and orphan-origin hosts are covered as well. -/
theorem generated_host_support_surjective
    (generated : RootGenerated (CoordinateModel B ht C) (tupleScheme B ht F)) :
    Function.Surjective R.support.point := by
  intro x
  have all := (CoordinateModel B ht C).closure_minimal R.support.range_closed
    (host_root_coordinates_in_support_range B ht F R)
  apply all
  change x ∈ (Object.full (CoordinateModel B ht C) (tupleScheme B ht F)).support
  rw [generated]
  trivial

/-- The exact whole-support equivalence, on the existing old host.
It is independent of any choice of competing expansion. -/
def generatedHostSupportEquiv
    (generated : RootGenerated (CoordinateModel B ht C) (tupleScheme B ht F)) :
    (Γ).support R.old ≃ W :=
  Equiv.ofBijective R.support.point
    ⟨R.support.injective,generated_host_support_surjective B ht F R generated⟩

/-- The inverse is a full induced OLD hidden map, so it carries all
unexpanded fine cylinders and partial unary domains onto the same support. -/
def generatedHostSupportInverse
    (generated : RootGenerated (CoordinateModel B ht C) (tupleScheme B ht F)) :
    Structure.Embedding (CoordinateModel B ht C) ((Γ).supportStructure R.old) :=
  inverseInduced R.support (generated_host_support_surjective B ht F R generated)

end
end CCO.UnfilteredEP
