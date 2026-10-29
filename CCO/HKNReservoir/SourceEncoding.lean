import CCO.HKNReservoir.HKNLanguage
import CCO.OwnerTransversal.InflationBasic

universe u v w x t
namespace CCO.HKNReservoir
open AllThoseEPPA

namespace Data
variable {B : Type u} {K : Type v} {Atom : Type w} {V : Type x}

def restrict (D : Data B K Atom V) (A : Set V) (hA : (encode D).IsClosed A) : Data B K Atom A where
  owner x := D.owner x.val
  fine a x y := D.fine a x.val y.val
  move k x := ⟨D.move k x.val,(isClosed_encode_iff D A).mp hA k x.val x.property⟩

@[simp] theorem restrict_owner (D : Data B K Atom V) (A : Set V) (hA) (x : A) :
    (D.restrict A hA).owner x = D.owner x.val := rfl
@[simp] theorem restrict_fine (D : Data B K Atom V) (A : Set V) (hA) (a : Atom) (x y : A) :
    (D.restrict A hA).fine a x y ↔ D.fine a x.val y.val := Iff.rfl
@[simp] theorem restrict_move (D : Data B K Atom V) (A : Set V) (hA) (k : K) (x : A) :
    ((D.restrict A hA).move k x).val = D.move k x.val := rfl

theorem encode_restrict (D : Data B K Atom V) (A : Set V) (hA : (encode D).IsClosed A) :
    encode (D.restrict A hA) = (encode D).induce A hA := by
  apply (show ∀ (C E : Structure (Signature B K Atom) A), @C.rel = @E.rel → @C.func = @E.func → C=E from by
    intro C E hr hf
    rcases C with ⟨cr,cf⟩
    rcases E with ⟨er,ef⟩
    dsimp only at hr hf
    exact congrArg₂ (@Structure.mk (Signature B K Atom) A) hr hf)
  · funext n R xs
    cases R <;> rfl
  · funext n F xs
    cases F with
    | translate k =>
      ext y
      change y = _ ↔ y.val = D.move k (xs 0).val
      exact ⟨fun he => congrArg Subtype.val he,fun he => Subtype.ext he⟩
end Data

noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)

/-- The source carrier already has the common E01/E02 universe. -/
abbrev SourceCarrier := ULift.{max v w} (NamedCarrier S H R B)

def sourceData : Data ↥B (ResidualData.PacketGroup S H) (S.Atom () ()) (SourceCarrier S H R B) where
  owner x := ownerLabel S H R B x.down
  fine a x y := col S x.down.val y.down.val = some a
  move g x := ULift.up (packetPoint S H R B hB g x.down)

def sourceStructure : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) (SourceCarrier S H R B) :=
  encode (sourceData S H R B hB)

/-- A finite closed source is encoded by restriction; this equals the
literal closed induced structure, not merely a homomorphic reduct. -/
def finiteSourceData (A : Set (SourceCarrier S H R B)) (hA : (sourceStructure S H R B hB).IsClosed A) :=
  (sourceData S H R B hB).restrict A hA

theorem finiteSourceStructure (A : Set (SourceCarrier S H R B)) (hA : (sourceStructure S H R B hB).IsClosed A) :
    encode (finiteSourceData S H R B hB A hA) = (sourceStructure S H R B hB).induce A hA :=
  Data.encode_restrict _ A hA

@[simp] theorem source_move_one (x : SourceCarrier S H R B) : (sourceData S H R B hB).move 1 x = x := by
  apply ULift.ext
  exact packetPoint_one S H R B hB x.down

theorem source_move_mul (g h : ResidualData.PacketGroup S H) (x : SourceCarrier S H R B) :
    (sourceData S H R B hB).move (g*h) x =
      (sourceData S H R B hB).move g ((sourceData S H R B hB).move h x) := by
  apply ULift.ext
  exact packetPoint_mul S H R B hB g h x.down

theorem source_move_free (x : SourceCarrier S H R B) :
    Function.Injective (fun g => (sourceData S H R B hB).move g x) := by
  intro g h he
  exact Inflation.named_action_free S H R B hB x.down (congrArg ULift.down he)

theorem source_fine_complete {x y : SourceCarrier S H R B} (hxy : x ≠ y) :
    ∃ a : S.Atom () (), (sourceData S H R B hB).fine a x y := by
  have hn : col S x.down.val y.down.val ≠ none := by
    intro he
    exact hxy (ULift.ext _ _ (Subtype.ext ((col_none S _ _).mp he)))
  cases hc : col S x.down.val y.down.val with
  | none => exact False.elim (hn hc)
  | some a => exact ⟨a,hc⟩

end
end CCO.HKNReservoir
