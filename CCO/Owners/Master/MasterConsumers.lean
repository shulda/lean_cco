import CCO.Owners.Master.SourceExport

/-! Genuine downstream uses of the simultaneous master: all finite
coordinate requests are realized inside its ONE real carrier, and its
actual full finite quotient actions lift an ENTIRE prescribed target
automorphism together with an arbitrary compatible point motion. -/

universe v w t z
namespace CCO.Owners.Master
noncomputable section
open RawExact ExactCRT Provider Product

variable {A : Type v} {S : AtomicSource.{0,v,w} Unit (fun _ => A)}
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable {H : HomogeneousSource S G} {cco : SemanticCCO.{0,v,v,w} S}
variable {T : Set A} (M : ActualMaster.{v,w,t,z} S H cco T)

local instance consumerInvariant (E : Exact S H cco) : CanonicalQuotients.Invariant G E.val :=
  Product.exactInvariant S H cco E

/-- M3 yields every prescribed full-target action, rather than merely
an unspecified point-transitive subgroup or some owner motion. -/
theorem ActualMaster.prescribed_points (E F : Exact S H cco) (hEF : E ≤ F) :
    GroupActions.PrescribedLift
      (exactImageQuotient (G := G) M.carrier E.val F.val hEF).action
      (exactImageQuotient (G := G) M.carrier E.val F.val hEF).projection := by
  let Q := exactImageQuotient (G := G) M.carrier E.val F.val hEF
  obtain ⟨a,ha⟩ := M.nonempty
  letI : Nonempty ((Quotient.mk'' : A → Quotient E.val) '' M.carrier) :=
    ⟨⟨Quotient.mk'' a,⟨a,ha,rfl⟩⟩⟩
  exact (GroupActions.prescribed_action_point_lifting Q.action Q.projection Q.surjective
    (fun g x => (Q.action_projection g x).symm)).mp (M.m3 E F hEF)

/-- The actual finite image of the family meet supplies ONE real point
of the master carrier for all requested coordinates simultaneously.
Empty, repeated and incomparable families use this same statement. -/
theorem ActualMaster.realizes {I : Type z} [Fintype I] (E : I → Exact S H cco)
    (q : ∀ i, Quotient (E i).val)
    (member : ∀ i, q i ∈ (Quotient.mk'' : A → Quotient (E i).val) '' M.carrier)
    (compat : Abstract.Compatible (fun i => (E i).val) q) :
    ∃ a ∈ M.carrier, ∀ i, Quotient.mk'' a = q i := by
  obtain ⟨x,hx⟩ := (M.m4 E).2 ⟨q,compat,member⟩
  obtain ⟨a,ha,hax⟩ := x.property
  refine ⟨a,ha,?_⟩
  intro i
  calc
    _ = Abstract.coordinates (fun i => (E i).val) x.val i :=
      congrArg (fun r => Abstract.coordinates (fun i => (E i).val) r i) hax
    _ = q i := congrArg (fun r : FiniteImages.CompatibleTuple M.carrier
      (fun i => (E i).val) => r.val i) hx

/-- One and the same finite master witnesses an arbitrary complete
coordinate request AND a fully prescribed finite quotient point motion.
No additional extension, point-lifting or coherence provider is supplied. -/
theorem ActualMaster.coordinates_and_motion {I : Type z} [Fintype I]
    (E : I → Exact S H cco) (q : ∀ i, Quotient (E i).val)
    (member : ∀ i, q i ∈ (Quotient.mk'' : A → Quotient (E i).val) '' M.carrier)
    (compat : Abstract.Compatible (fun i => (E i).val) q)
    (J K : Exact S H cco) (hJK : J ≤ K)
    (x y : (Quotient.mk'' : A → Quotient J.val) '' M.carrier)
    (γ : OrbitalAut G (Quotient K.val)
      (Subtype.val : ((Quotient.mk'' : A → Quotient K.val) '' M.carrier) → Quotient K.val))
    (motion : γ • (exactImageQuotient (G := G) M.carrier J.val K.val hJK).projection x =
      (exactImageQuotient (G := G) M.carrier J.val K.val hJK).projection y) :
    ∃ a ∈ M.carrier, ∃ β : OrbitalAut G (Quotient J.val)
      (Subtype.val : ((Quotient.mk'' : A → Quotient J.val) '' M.carrier) → Quotient J.val),
      (∀ i, Quotient.mk'' a = q i) ∧
      (exactImageQuotient (G := G) M.carrier J.val K.val hJK).action β = γ ∧ β • x = y := by
  obtain ⟨a,ha,hq⟩ := M.realizes E q member compat
  obtain ⟨β,hβ,hmove⟩ := M.prescribed_points J K hJK x y γ motion
  exact ⟨a,ha,β,hq,hβ,hmove⟩

end
end CCO.Owners.Master
