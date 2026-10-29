import CCO.HKNReservoir.SourceEncoding
import CCO.HKNReservoir.MorphismBridge
import CCO.SafeReadings.TransversalPure
import CCO.OwnerTransversal.PrescribedActions

universe v w t
namespace CCO.HKNReservoir
noncomputable section
open AllThoseEPPA ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)

abbrev SourceGamma := SafeReadings.TransversalPure.Gamma S H R B

def sourceTag (Δ : Subgroup (SourceGamma S H R B)) : Δ →* Equiv.Perm ↥B :=
  (SafeReadings.TransversalPure.tagHom S H R B).comp Δ.subtype

def sourceAction (Δ : Subgroup (SourceGamma S H R B)) :
    (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())).Action Δ :=
  action (sourceTag S H R B Δ)

variable (Δ : Subgroup (SourceGamma S H R B))

def liftNamedPerm (e : Equiv.Perm (NamedCarrier S H R B)) : Equiv.Perm (SourceCarrier S H R B) where
  toFun x := ULift.up (e x.down)
  invFun x := ULift.up (e.symm x.down)
  left_inv x := ULift.ext _ _ (e.symm_apply_apply x.down)
  right_inv x := ULift.ext _ _ (e.apply_symm_apply x.down)

def sourceAutOfNamed (γ : Δ) (e : Equiv.Perm (NamedCarrier S H R B))
    (ho : ∀ x, ownerLabel S H R B (e x) = (sourceTag S H R B Δ) γ (ownerLabel S H R B x))
    (hc : ∀ x y, col S (e x).val (e y).val = col S x.val y.val)
    (hm : ∀ g x, e (packetPoint S H R B hB g x) = packetPoint S H R B hB g (e x)) :
    Structure.Automorphism (sourceAction S H R B Δ) (sourceStructure S H R B hB) :=
  (ExactAut.mk (tag:=sourceTag S H R B Δ) (D:=sourceData S H R B hB) γ (liftNamedPerm S H R B e) (fun x => ho x.down)
    (fun a x y => Iff.of_eq (congrArg (· = some a) (hc x.down y.down)))
    (fun g x => ULift.ext _ _ (hm g x.down))).toAutomorphism

@[simp] theorem sourceAutOfNamed_lang (γ : Δ) (e : Equiv.Perm (NamedCarrier S H R B)) (ho hc hm) :
    (sourceAutOfNamed S H R B hB Δ γ e ho hc hm).lang = γ := rfl
@[simp] theorem sourceAutOfNamed_apply (γ : Δ) (e : Equiv.Perm (NamedCarrier S H R B)) (ho hc hm) (x : SourceCarrier S H R B) :
    sourceAutOfNamed S H R B hB Δ γ e ho hc hm x = ULift.up (e x.down) := rfl

/-- Every prescribed pure owner component is realized separately.
There is no homomorphic choice of lifts and no ambient EPPA assumption. -/
theorem ambientLift (γ : Δ) :
    ∃ σ : Structure.Automorphism (sourceAction S H R B Δ) (sourceStructure S H R B hB), σ.lang = γ := by
  let empty : Empty → NamedCarrier S H R B := Empty.elim
  obtain ⟨_,e,_,_,_,ho,hc,hm⟩ := prescribed_named_action S H R B hB empty empty γ.val
    (fun i => nomatch i) (fun i => nomatch i)
  have heo (x) : ownerLabel S H R B (e x) = sourceTag S H R B Δ γ (ownerLabel S H R B x) := Subtype.ext (ho x)
  exact ⟨sourceAutOfNamed S H R B hB Δ γ e heo hc hm,rfl⟩

/-- Actual named-owner automorphisms become literal-language source automorphisms. -/
def namedAut (f : NamedAut S H R B) :
    Structure.Automorphism (sourceAction S H R B Δ) (sourceStructure S H R B hB) :=
  sourceAutOfNamed S H R B hB Δ 1 f.val
    (fun x => by change ownerLabel S H R B (f.val x) = ownerLabel S H R B x; exact Subtype.ext (NamedAut.owner_fixed f x))
    (NamedAut.colour_fixed f) (namedAut_commutes S H R B hB f)

@[simp] theorem namedAut_lang (f : NamedAut S H R B) : (namedAut S H R B hB Δ f).lang = 1 := rfl
@[simp] theorem namedAut_apply (f : NamedAut S H R B) (x : SourceCarrier S H R B) :
    namedAut S H R B hB Δ f x = ULift.up (f.val x.down) := rfl

variable {S H R B hB Δ}

theorem source_embedding_owner (f : Structure.Embedding (sourceAction S H R B Δ)
    (sourceStructure S H R B hB) (sourceStructure S H R B hB)) (x : SourceCarrier S H R B) :
    (sourceData S H R B hB).owner (f x) = sourceTag S H R B Δ f.lang ((sourceData S H R B hB).owner x) :=
  (exactMapOfEmbedding (sourceTag S H R B Δ) f).owner x

theorem source_embedding_move (f : Structure.Embedding (sourceAction S H R B Δ)
    (sourceStructure S H R B hB) (sourceStructure S H R B hB)) (g : ResidualData.PacketGroup S H) (x : SourceCarrier S H R B) :
    f ((sourceData S H R B hB).move g x) = (sourceData S H R B hB).move g (f x) :=
  (exactMapOfEmbedding (sourceTag S H R B Δ) f).move g x

theorem source_embedding_colour (f : Structure.Embedding (sourceAction S H R B Δ)
    (sourceStructure S H R B hB) (sourceStructure S H R B hB)) (x y : SourceCarrier S H R B) :
    col S (f x).down.val (f y).down.val = col S x.down.val y.down.val := by
  have hf := (exactMapOfEmbedding (sourceTag S H R B Δ) f).fine
  cases hs : col S x.down.val y.down.val with
  | none =>
    cases ht : col S (f x).down.val (f y).down.val with
    | none => rfl
    | some a =>
      have hh := (hf a x y).mp ht
      change col S x.down.val y.down.val = some a at hh
      rw [hs] at hh
      cases hh
  | some a => exact (hf a x y).mpr hs

end
end CCO.HKNReservoir
