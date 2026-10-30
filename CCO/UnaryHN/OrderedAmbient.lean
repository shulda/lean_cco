import CCO.UnaryHN.NativeTransferBasis
import PartiteConstruction.Ramsey.AllThosePartialFiniteModels
import PartiteConstruction.Structure.Order

/-! The actual ordered native classes and the genuine functional HN2.19
binding. Orders are arbitrary global strict linear orders on the SAME carrier. -/

universe u v w
namespace CCO.UnaryHN.Native
open StructuralRamsey
open StructuralRamsey.Structure

def OrderedClass {L : Language.{u}} (K : Class.{u,v} L) :
    Class.{u,v} L.withLinearOrder :=
  fun {V} C => ∃ (old : Structure L V) (o : LinearOrder V),
    K old ∧ C = @Structure.withLinearOrder L V old o.toLT

def AllOrderedModels (L : Language.{u}) : Class.{u,v} L.withLinearOrder :=
  OrderedClass (fun C => C.SingletonValued)

theorem orderedClass_mono {L : Language.{u}} {K R : Class.{u,v} L}
    (h : ∀ {V : Type v} (C : Structure L V), K C → R C) :
    ∀ {V : Type v} (C : Structure L.withLinearOrder V),
      OrderedClass K C → OrderedClass R C := by
  rintro V C ⟨old, o, hold, rfl⟩
  exact ⟨old, o, h old hold, rfl⟩

theorem allOrderedModels_ramsey (L : Language.{u}) : Ramsey (AllOrderedModels.{u,v} L) := by
  intro V W hV hW A B hA hB κ hκ hκn
  rcases hA with ⟨A₀, oA, hA₀, rfl⟩
  rcases hB with ⟨B₀, oB, hB₀, rfl⟩
  letI : LinearOrder V := oA
  letI : LinearOrder W := oB
  obtain ⟨X, hX, oX, C, hC, hArrow⟩ :=
    allThoseRamseyClasses_theorem_2_19_partialFunctions A₀ B₀ hA₀ hB₀ κ
  exact ⟨X, hX, @Structure.withLinearOrder L X C oX.toLT,
    ⟨C, oX, hC, rfl⟩, hArrow⟩

theorem withLinearOrder_irreducible {L : Language.{u}} {V : Type v}
    (A : Structure L V) [LinearOrder V] : A.withLinearOrder.Irreducible := by
  classical
  rw [irreducible_iff_noProperFreeDecomposition]
  rintro ⟨d⟩
  have hL := d.leftProper
  have hR := d.rightProper
  push_neg at hL hR
  obtain ⟨x, hx⟩ := hL
  obtain ⟨y, hy⟩ := hR
  have hne : x ≠ y := by
    intro heq
    rcases d.free.covers x with ⟨z, hz⟩ | ⟨z, hz⟩
    · exact hx z hz.symm
    · exact hy z (hz.symm.trans heq)
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · have hr : A.withLinearOrder.rel (.inr ()) ![x, y] := hxy
    rcases (d.free.rel_iff (.inr ()) ![x, y]).mp hr with
      ⟨xs, _, he⟩ | ⟨xs, _, he⟩
    · exact hx (xs 0) (congrFun he 0).symm
    · exact hy (xs 1) (congrFun he 1).symm
  · have hr : A.withLinearOrder.rel (.inr ()) ![y, x] := hyx
    rcases (d.free.rel_iff (.inr ()) ![y, x]).mp hr with
      ⟨xs, _, he⟩ | ⟨xs, _, he⟩
    · exact hx (xs 1) (congrFun he 1).symm
    · exact hy (xs 0) (congrFun he 0).symm

theorem orderedClass_allIrreducible {L : Language.{u}} (K : Class.{u,v} L) :
    AllIrreducible (OrderedClass K) := by
  rintro V C ⟨old, o, _, rfl⟩
  letI := o
  exact withLinearOrder_irreducible old

end CCO.UnaryHN.Native
