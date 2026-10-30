import CCO.FullPhaseLift.Detours.Fresh
import CCO.FullPhaseLift.Detours.Cylinders
import CCO.FullPhaseLift.Detours.Marking
import CCO.PairSafeSplit.Strong.WordFamily

/-! B048 C11–C15/C17, actual private detour WITNESSES. Only the consecutive
edges will be specified by the full-language adapter; the stored root
colour and actual tuple are witness data, never additional gadget edges. -/
universe u v w t
namespace CCO.FullPhaseLift.Detours
open APCharacter RigidGroupoid.Geometry
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}
variable (P : SourcePhase S H C A)

structure ActivePath (b c : Reached S A) (a : S.Atom b.val c.val) (ε η : Bit) where
  x : X b.val
  y : X c.val
  u : X r
  v : X r
  mark : Sigma X → Bit
  global : P.masks.GlobalMarking mark
  root_colour : S.colour x y = some a
  left_bit : mark ⟨b.val,x⟩ = ε
  right_bit : mark ⟨c.val,y⟩ = η
  distinct : Function.Injective (![⟨b.val,x⟩,⟨r,u⟩,⟨r,v⟩,⟨c.val,y⟩] : Fin 4 → Sigma X)
  left_bridge : (Reached.rootArrow H C b).rel u x
  right_bridge : (Reached.rootArrow H C c).rel v y
  left : S.Atom b.val r
  middle : S.Atom r r
  right : S.Atom r c.val
  left_colour : S.colour x u = some left
  middle_colour : S.colour u v = some middle
  right_colour : S.colour v y = some right

namespace ActivePath
variable {P} {b c : Reached S A} {a : S.Atom b.val c.val} {ε η : Bit}
variable (W : ActivePath P b c a ε η)

def word : PositiveWord S b.val c.val := .cons W.left (.cons W.middle (.single W.right))
def point : Fin 4 → Sigma X := ![⟨b.val,W.x⟩,⟨r,W.u⟩,⟨r,W.v⟩,⟨c.val,W.y⟩]

include W in
theorem root_allowed : P.allows (some a) ε η := by
  have h := W.global.2 ⟨b.val,W.x⟩ ⟨c.val,W.y⟩
  rwa [W.root_colour,W.left_bit,W.right_bit] at h

theorem root_mem_profile (sap : AgeSAP S) : a ∈ PositiveWord.profile S W.word := by
  apply (PairSafeSplit.Strong.profile_iff_represented S H sap W.word W.root_colour).mpr
  exact ⟨W.u,W.left_colour,W.v,W.middle_colour,W.right_colour⟩

theorem represented_bound : ∀ x y, PositiveWord.represented S W.word x y →
    cylinder S (Reached.kernel H C b) (Reached.kernel H C c) a x y :=
  three_edge_bound S H (Reached.rootArrow H C b) (Reached.rootArrow H C c)
    a W.left W.middle W.right W.x W.y W.u W.v W.left_bridge W.right_bridge
    W.root_colour W.left_colour W.middle_colour W.right_colour

theorem phase_safe (sap : AgeSAP S) :
    PositiveWord.profile S W.word ⊆ {d | P.allows (some d) ε η} := by
  intro d hd
  obtain ⟨x,y,hxy⟩ := S.realized d
  have hrep := (PairSafeSplit.Strong.profile_iff_represented S H sap W.word hxy).mp hd
  have h := cylinder_allows P b c a ε η W.root_allowed x y (W.represented_bound x y hrep)
  rwa [hxy] at h

theorem consecutive_allowed :
    P.allows (some W.left) ε (W.mark ⟨r,W.u⟩) ∧
    P.allows (some W.middle) (W.mark ⟨r,W.u⟩) (W.mark ⟨r,W.v⟩) ∧
    P.allows (some W.right) (W.mark ⟨r,W.v⟩) η := by
  refine ⟨?_,?_,?_⟩
  · have h := W.global.2 ⟨b.val,W.x⟩ ⟨r,W.u⟩
    rwa [W.left_colour,W.left_bit] at h
  · have h := W.global.2 ⟨r,W.u⟩ ⟨r,W.v⟩
    rwa [W.middle_colour] at h
  · have h := W.global.2 ⟨r,W.v⟩ ⟨c.val,W.y⟩
    rwa [W.right_colour,W.right_bit] at h
end ActivePath

/-- The two source inverse-image classes may coincide. Sequential
avoidance inside their infinite actual fibres still gives four distinct
actual points and a three-edge diversity path. -/
theorem exists_active_path (sap : AgeSAP S) (b c : Reached S A)
    (a : S.Atom b.val c.val) (ε η : Bit) (ha : P.allows (some a) ε η) :
    Nonempty (ActivePath P b c a ε η) := by
  classical
  obtain ⟨x,y,mark,hxy,hm,hx,hy⟩ := allowed_root_pair P a ε η ha
  let F : Set (Sigma X) := {⟨b.val,x⟩,⟨c.val,y⟩}
  obtain ⟨u,v,hu,hv,huf,hvf⟩ := fresh_source_representatives P sap b c x y F (by
    exact (Set.finite_singleton _).insert _)
  have hxyNe : (⟨b.val,x⟩ : Sigma X) ≠ ⟨c.val,y⟩ := S.atomRel_ne hxy
  have hux : (⟨r,u⟩ : Sigma X) ≠ ⟨b.val,x⟩ := by intro h; exact huf (Or.inl h)
  have huy : (⟨r,u⟩ : Sigma X) ≠ ⟨c.val,y⟩ := by intro h; exact huf (Or.inr h)
  have hvu : (⟨r,v⟩ : Sigma X) ≠ ⟨r,u⟩ := by intro h; apply hvf; exact Or.inl h
  have hvx : (⟨r,v⟩ : Sigma X) ≠ ⟨b.val,x⟩ := by intro h; exact hvf (Or.inr (Or.inl h))
  have hvy : (⟨r,v⟩ : Sigma X) ≠ ⟨c.val,y⟩ := by intro h; exact hvf (Or.inr (Or.inr h))
  obtain ⟨ra,hra⟩ := S.some_colour_of_ne x u hux.symm
  obtain ⟨d,hd⟩ := S.some_colour_of_ne u v hvu.symm
  obtain ⟨rb,hrb⟩ := S.some_colour_of_ne v y hvy
  refine ⟨⟨x,y,u,v,mark,hm,hxy,hx,hy,?_,hu,hv,ra,d,rb,hra,hd,hrb⟩⟩
  intro k l h
  fin_cases k <;> fin_cases l <;>
    first | rfl | exact (hxyNe h).elim | exact (hxyNe h.symm).elim |
      exact (hux h).elim | exact (hux h.symm).elim | exact (huy h).elim | exact (huy h.symm).elim |
      exact (hvu h).elim | exact (hvu h.symm).elim | exact (hvx h).elim | exact (hvx h.symm).elim |
      exact (hvy h).elim | exact (hvy h.symm).elim

structure InactivePath (i j : ι) (a : S.Atom i j) (ε η : Bit) where
  x : X i
  y : X j
  z : X r
  mark : Sigma X → Bit
  global : P.masks.GlobalMarking mark
  root_colour : S.colour x y = some a
  left_bit : mark ⟨i,x⟩ = ε
  right_bit : mark ⟨j,y⟩ = η
  inactive : ¬Nonempty (Bridge S A i) ∨ ¬Nonempty (Bridge S A j)
  distinct : Function.Injective (![⟨i,x⟩,⟨r,z⟩,⟨j,y⟩] : Fin 3 → Sigma X)
  left : S.Atom i r
  right : S.Atom r j
  left_colour : S.colour x z = some left
  right_colour : S.colour z y = some right

namespace InactivePath
variable {P} {i j : ι} {a : S.Atom i j} {ε η : Bit}
variable (W : InactivePath P i j a ε η)
def word : PositiveWord S i j := .cons W.left (.single W.right)
def point : Fin 3 → Sigma X := ![⟨i,W.x⟩,⟨r,W.z⟩,⟨j,W.y⟩]

theorem root_mem_profile : a ∈ PositiveWord.profile S W.word :=
  ⟨W.left,rfl,W.right,rfl,W.x,W.z,W.y,W.left_colour,W.right_colour,W.root_colour⟩

theorem phase_safe : PositiveWord.profile S W.word ⊆ {d | P.allows (some d) ε η} := by
  intro d _
  apply P.inactive_masks_full ε η _ _ W.inactive (some d)
  · rw [← W.left_bit]
    exact W.global.1 ⟨i,W.x⟩
  · rw [← W.right_bit]
    exact W.global.1 ⟨j,W.y⟩

theorem consecutive_allowed : P.allows (some W.left) ε (W.mark ⟨r,W.z⟩) ∧
    P.allows (some W.right) (W.mark ⟨r,W.z⟩) η := by
  constructor
  · have h := W.global.2 ⟨i,W.x⟩ ⟨r,W.z⟩
    rwa [W.left_colour,W.left_bit] at h
  · have h := W.global.2 ⟨r,W.z⟩ ⟨j,W.y⟩
    rwa [W.right_colour,W.right_bit] at h
end InactivePath

theorem exists_inactive_path (sap : AgeSAP S) {i j : ι}
    (inactive : ¬Nonempty (Bridge S A i) ∨ ¬Nonempty (Bridge S A j))
    (a : S.Atom i j) (ε η : Bit) (ha : P.allows (some a) ε η) :
    Nonempty (InactivePath P i j a ε η) := by
  classical
  obtain ⟨x,y,mark,hxy,hm,hx,hy⟩ := allowed_root_pair P a ε η ha
  let F : Set (Sigma X) := {⟨i,x⟩,⟨j,y⟩}
  obtain ⟨z,hz⟩ := fresh_point (S := S) (H := H) sap r F (by exact (Set.finite_singleton _).insert _)
  have hxyNe : (⟨i,x⟩ : Sigma X) ≠ ⟨j,y⟩ := S.atomRel_ne hxy
  have hzx : (⟨r,z⟩ : Sigma X) ≠ ⟨i,x⟩ := by intro h; exact hz (Or.inl h)
  have hzy : (⟨r,z⟩ : Sigma X) ≠ ⟨j,y⟩ := by intro h; exact hz (Or.inr h)
  obtain ⟨p,hp⟩ := S.some_colour_of_ne x z hzx.symm
  obtain ⟨q,hq⟩ := S.some_colour_of_ne z y hzy
  refine ⟨⟨x,y,z,mark,hm,hxy,hx,hy,inactive,?_,p,q,hp,hq⟩⟩
  intro k l h
  fin_cases k <;> fin_cases l <;>
    first | rfl | exact (hxyNe h).elim | exact (hxyNe h.symm).elim |
      exact (hzx h).elim | exact (hzx h.symm).elim | exact (hzy h).elim | exact (hzy h.symm).elim

end
end CCO.FullPhaseLift.Detours
