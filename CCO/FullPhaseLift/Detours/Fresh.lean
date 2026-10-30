import CCO.PairSafeSplit.SAP.Gates
import CCO.PairSafeSplit.Infinity.TypeFibres

/-! B048 C09/C11. Whole original gate fibres and genuine fresh inverse
bridge representatives. No disjointness of the two quotient classes is
assumed, and no new-source SAP is used. -/

universe u v w t
namespace CCO.FullPhaseLift.Detours
open APCharacter RigidGroupoid.Geometry ParityHasse.Original
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)

/-- The inverse image of one quotient endpoint is the ENTIRE source
kernel class, rather than a selected representative or a finite section. -/
theorem bridge_fibre_eq_class {i j : ι} {K : Kernel S i} {L : Kernel S j}
    (R : Arrow S K L) (y : X j) :
    {x | R.rel x y} = {x | K.rel (R.inv.pointImage H y) x} := by
  have h0 : R.rel (R.inv.pointImage H y) y := R.inv.pointImage_spec H y
  ext x
  constructor
  · intro h
    rw [← R.source]
    exact ⟨y,h0,h⟩
  · intro h
    rw [← R.left]
    exact ⟨R.inv.pointImage H y,K.setoid.symm h,h0⟩

include H in
theorem bridge_fibre_infinite (sap : AgeSAP S) {i j : ι}
    {K : Kernel S i} {L : Kernel S j} (hK : K.setoid ≠ ⊥)
    (R : Arrow S K L) (y : X j) : Set.Infinite {x | R.rel x y} := by
  let E : ColourEq S i := ⟨K.setoid,ParityHasse.Relative.Exact.colourInvariant S H K.exact⟩
  have hE : (⊥ : ColourEq S i) < E := by
    apply lt_of_le_of_ne bot_le
    intro he
    exact hK (congrArg Subtype.val he).symm
  rw [bridge_fibre_eq_class S H R y]
  exact PairSafeSplit.Infinity.equivalence_class_infinite S H sap E hE _

variable {S H} {C : ExactCalculus S} {r : ι} {A : Kernel S r}

theorem source_kernel_ne_bot (P : SourcePhase S H C A) (sap : AgeSAP S) :
    A.setoid ≠ ⊥ := by
  intro he
  apply PairSafeSplit.SAP.reached_kernel_ne_bot P sap (Reached.root A)
  apply Subtype.ext
  change (Reached.kernel H C (Reached.root A)).setoid = ⊥
  rw [Reached.root_kernel]
  exact he

/-- Freshness is expressed on actual TAGGED points. Repeated original
sort labels and coinciding inverse-image classes require no special case. -/
theorem fresh_source_representatives (P : SourcePhase S H C A) (sap : AgeSAP S)
    (b c : Reached S A) (x : X b.val) (y : X c.val)
    (F : Set (Sigma X)) (hF : F.Finite) :
    ∃ u v : X r,
      (Reached.rootArrow H C b).rel u x ∧
      (Reached.rootArrow H C c).rel v y ∧
      (⟨r,u⟩ : Sigma X) ∉ F ∧ (⟨r,v⟩ : Sigma X) ∉ Set.insert ⟨r,u⟩ F := by
  classical
  have hinj : Function.Injective (Sigma.mk r : X r → Sigma X) := by
    intro x y h
    exact eq_of_heq (Sigma.mk.inj h).2
  have hK := source_kernel_ne_bot P sap
  have hU := bridge_fibre_infinite S H sap hK (Reached.rootArrow H C b) x
  have hV := bridge_fibre_infinite S H sap hK (Reached.rootArrow H C c) y
  have hf : Set.Finite {u : X r | (⟨r,u⟩ : Sigma X) ∈ F} := hF.preimage hinj.injOn
  obtain ⟨u,hu,huf⟩ := hU.exists_notMem_finite hf
  have hf' : Set.Finite {v : X r | (⟨r,v⟩ : Sigma X) ∈ Set.insert ⟨r,u⟩ F} :=
    (hF.insert _).preimage hinj.injOn
  obtain ⟨v,hv,hvf⟩ := hV.exists_notMem_finite hf'
  exact ⟨u,v,hu,hv,huf,hvf⟩

include H in
/-- Every inhabited old named sort is infinite under old SAP, hence a
fresh point can also be chosen for the inactive two-edge case. -/
theorem fresh_point (sap : AgeSAP S) (i : ι) (F : Set (Sigma X)) (hF : F.Finite) :
    ∃ x : X i, (⟨i,x⟩ : Sigma X) ∉ F := by
  classical
  let x : X i := Classical.choice (S.nonemptySort i)
  let B : FiniteInduced (X := X) := ⟨∅,Set.finite_empty⟩
  have hi := PairSafeSplit.Infinity.typeFibre_infinite S H sap B x (by simp [B])
  have hinj : Function.Injective (Sigma.mk i : X i → Sigma X) := by
    intro x y h
    exact eq_of_heq (Sigma.mk.inj h).2
  obtain ⟨y,_,hy⟩ := hi.exists_notMem_finite (hF.preimage hinj.injOn)
  exact ⟨y,hy⟩

end
end CCO.FullPhaseLift.Detours
