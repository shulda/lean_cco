import CCO.PairSafeSplit.SAP.Markings
import CCO.APCharacter.SourceAge.Identification
import CCO.PairSafeSplit.Terminal.TypeReflection
import CCO.OwnerTransversal.TypedOrbitSAP

/-! B047 C29--C33. Old SAP gives infinite same-mark old type fibres.
The actual marked Fraïssé source is already identified with literal unary
subtypes of the SAME old carriers. Its whole proved homogeneity therefore
turns those witnesses into infinite marked stabilizer orbits, and one
simultaneous avoidance move proves SAP of the ENTIRE new age. -/

universe u v w t
namespace CCO.PairSafeSplit.SAP
open APCharacter RigidGroupoid.Geometry
open APCharacter.SourceAge.UnarySource
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}
variable (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (I : Identification S H (P.completion_property cco))

/-- Actual whole-new-source stabilizer infinitude. `I` is the same proved
old-reduct identification used in the public B044 source, not an arbitrary
globally homogeneous seed marking. No new-source STRONG theorem is used. -/
theorem unary_source_orbit_infinite (sap : AgeSAP S)
    (B : FiniteInduced (X := Rank.Point (β I) (tag I))) (x : NewPoint I)
    (hx : x ∉ B.vertices) :
    (RealAction.orbitOver (G := FullGroup I) B.vertices x).Infinite := by
  classical
  rcases x with ⟨c,x⟩
  have hxOld : (⟨c.1,x.val⟩ : Sigma X) ∉ (oldBase I B).vertices := by
    rintro ⟨p,hp,he⟩
    apply hx
    have hh : p = (⟨c,x⟩ : NewPoint I) := (oldEquiv I).injective he
    exact hh ▸ hp
  let U := Infinity.markedTypeFibre S (oldBase I B)
    (fun y : X c.1 => mark I ⟨c.1,y⟩) x.val
  have hu : U.Infinite := marked_fibre_infinite P sap (mark I) (global_marking I)
    (oldBase I B) x.val hxOld
  let lift : U → NewPoint I := fun y =>
    ⟨c,⟨y.val,by
      apply Subtype.ext
      exact y.property.2.trans (congrArg Subtype.val x.property)⟩⟩
  have hlift : Function.Injective lift := by
    intro y z he
    apply Subtype.ext
    have hh := congrArg (oldEquiv I) he
    exact eq_of_heq (Sigma.mk.inj hh).2
  have htype (y : U) : RealAction.SameTypeOver (source I) B ⟨c,x⟩ (lift y) := by
    apply sameType_of_old I B ⟨c,x⟩ (lift y) rfl
    exact y.property.1
  intro hfinite
  letI := hfinite.to_subtype
  let f : U → RealAction.orbitOver (G := FullGroup I) B.vertices ⟨c,x⟩ :=
    fun y => ⟨lift y,RealAction.sameTypeOver_orbit (source I) (homogeneous I) B _ _ (htype y)⟩
  have hinj : Function.Injective f := by
    intro y z he
    exact hlift (congrArg Subtype.val he)
  have hufin : Finite U := Finite.of_injective f hinj
  exact hu (Set.finite_coe_iff.mp hufin)

/-- The actual maximal-character source preserves SAP. Its proof uses
only original SAP plus actual gate/marking geometry and already proved
whole marked homogeneity, before every new STRONG injectivisation/readout. -/
theorem unary_source_sap (sap : AgeSAP S) : AgeSAP (source I) := by
  apply OwnerTransversal.ageSAP_of_infinite_stabilizer_orbits (source I) (homogeneous I)
  exact unary_source_orbit_infinite P cco I sap

end
end CCO.PairSafeSplit.SAP
