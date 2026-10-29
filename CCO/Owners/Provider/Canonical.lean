import CCO.Owners.Provider.Source
import CCO.Owners.Product.SourceGeometry

/-! A reusable finite induced witness and its literal canonical exact
quotient instance. No exactness or ambient-lift provider remains open. -/
universe v w t
namespace CCO.Owners.Provider
open Product RawExact ExactCRT RawExact.CanonicalQuotients
variable {A O : Type v} {G : Type t} [Group G] [MulAction G A] [MulAction G O]

structure OwnerWitness (S : AtomicSource.{0,v,w} Unit (fun _ => A))
    (H : HomogeneousSource S G) (π : A → O)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (B : Set O) (T : Set A) (overT : ∀ x : T, π x.val ∈ B) where
  carrier : Set A
  finite : carrier.Finite
  contains : T ⊆ carrier
  closed : FullPacketClosed S H carrier
  over : ∀ x : carrier, π x.val ∈ B
  onto : Function.Surjective (ownerProjection π carrier B over)
  extensions : ∀ r : OwnerRequest (G := G) π T B overT,
    ∃ β : OrbitalAut G A (Subtype.val : carrier → A),
      (∀ x : r.part.domain,
        (β.val ⟨x.val.val,contains x.val.property⟩).val = (r.part.map x).val) ∧
      (inducedQuotient π equivπ carrier B over onto).action β = r.owner
  prescribed : GroupActions.PrescribedLift
    (inducedQuotient π equivπ carrier B over onto).action (ownerProjection π carrier B over)
  onto_action : Function.Surjective (inducedQuotient π equivπ carrier B over onto).action
  kernel : GroupActions.FibreTransitive
    (inducedQuotient π equivπ carrier B over onto).action (ownerProjection π carrier B over)

theorem actual_owner_witness [Countable A]
    (S : AtomicSource.{0,v,w} Unit (fun _ => A))
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
    (ep : OrdinaryEPPA G A)
    (π : A → O) (ontoπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (K : NonemptyExact S () ()) (hK : GroupActions.kernel π = evaluate S K.words)
    (B : Set O) (hB : B.Finite) (nonemptyB : B.Nonempty)
    (closedB : ∀ u ∈ B, ∀ v, ownerPacket S H π ontoπ equivπ u v → v ∈ B)
    (T : Set A) (hT : T.Finite) (overT : ∀ x : T, π x.val ∈ B) :
    Nonempty (OwnerWitness S H π equivπ B T overT) := by
  obtain ⟨D,hD,inc,closed,over,onto,ext,points,surj,kernel⟩ :=
    actual_owner_provider S H cco ep π ontoπ equivπ K hK B hB nonemptyB closedB T hT overT
  exact ⟨⟨D,hD,inc,closed,over,onto,ext,points,surj,kernel⟩⟩

namespace OwnerWitness
variable {S : AtomicSource.{0,v,w} Unit (fun _ => A)} {H : HomogeneousSource S G}
variable {π : A → O} {equivπ : ∀ (g : G) x, π (g • x) = g • π x}
variable {B : Set O} {T : Set A} {overT : ∀ x : T, π x.val ∈ B}
variable (W : OwnerWitness S H π equivπ B T overT)

noncomputable def quotient := inducedQuotient π equivπ W.carrier B W.over W.onto

/-- Empty REAL requests still prescribe every permutation of the whole B. -/
theorem empty_real_lift (γ : OrbitalAut G O (Subtype.val : B → O)) :
    ∃ β : OrbitalAut G A (Subtype.val : W.carrier → A), W.quotient.action β = γ := by
  obtain ⟨β,_,hb⟩ := W.extensions (emptyRequest π T B overT γ)
  exact ⟨β,hb⟩

/-- The packet conclusion is literally about complete ambient packets
inside the actual finite induced witness. -/
theorem packet_transport (β : OrbitalAut G A (Subtype.val : W.carrier → A))
    (x : W.carrier) :
    (fun z : W.carrier => (β.val z).val) ''
        {z : W.carrier | RealClosure.Bounds.finitePacket S H x.val z.val} =
      {y : A | RealClosure.Bounds.finitePacket S H (β.val x).val y} :=
  full_packet_image S H W.carrier W.closed β x

end OwnerWitness

section Canonical
variable (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (E : ExactEq S H cco ())
local instance canonicalInvariant : Invariant G E.val := Product.exactInvariant S H cco E

/-- The actual quotient projection and its action retain the original
ambient group; there is no independently chosen owner action. -/
def canonicalProjection : A → Quotient E.val := Quotient.mk''

theorem canonicalProjection_equivariant (g : G) (x : A) :
    canonicalProjection S H cco E (g • x) = g • canonicalProjection S H cco E x := rfl

/-- Literal X/E source instance: exactness and all ambient requests are
discharged; only ordinary EPPA and the existing countability premise remain. -/
theorem canonical_owner_provider [Countable A] (ep : OrdinaryEPPA G A)
    (B : Set (Quotient E.val)) (hB : B.Finite) (nonemptyB : B.Nonempty)
    (closedB : ∀ u ∈ B, ∀ v,
      ownerPacket S H (canonicalProjection S H cco E) Quotient.mk''_surjective
        (canonicalProjection_equivariant S H cco E) u v → v ∈ B)
    (T : Set A) (hT : T.Finite)
    (overT : ∀ x : T, canonicalProjection S H cco E x.val ∈ B) :
    Nonempty (OwnerWitness S H (canonicalProjection S H cco E)
      (canonicalProjection_equivariant S H cco E) B T overT) := by
  let K := exactPresentation S E.property
  have hker : GroupActions.kernel (canonicalProjection S H cco E) = evaluate S K.words := by
    rw [exactPresentation_represents S E.property]
    funext x y
    exact propext Quotient.eq
  exact actual_owner_witness S H cco ep (canonicalProjection S H cco E)
    Quotient.mk''_surjective (canonicalProjection_equivariant S H cco E) K hker
    B hB nonemptyB closedB T hT overT

end Canonical
end CCO.Owners.Provider
