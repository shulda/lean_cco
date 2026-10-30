import CCO.APCharacter.Totality

/-! Original maximality makes the whole gate prime under finite meets of
strictly larger exact bisaturated same-sort domains. Closure separation is
applied at the original real level, never by reverse quotient descent. -/
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace CCO.APCharacter
open RigidGroupoid.Geometry RigidGroupoid.Phase
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}
namespace SourcePhase
variable (P : SourcePhase S H C A)

include P in
theorem gate_meet_not_kernel (cco : SemanticCCO.{u,v,max u v,w} S)
    (b : Reached S A) (R T : TRel X b.val b.val)
    (hR : FullExact S R) (hT : FullExact S T)
    (hKR : ∀ x y, (Reached.kernel H C b).rel x y → R x y)
    (hKT : ∀ x y, (Reached.kernel H C b).rel x y → T x y)
    (satR : ParityHasse.Relative.Bisaturated (Reached.kernel H C b).setoid R)
    (satT : ParityHasse.Relative.Bisaturated (Reached.kernel H C b).setoid T)
    (outR : ∃ x y, R x y ∧ ¬(Reached.kernel H C b).rel x y)
    (outT : ∃ x y, T x y ∧ ¬(Reached.kernel H C b).rel x y) :
    (fun x y => R x y ∧ T x y) ≠ (Reached.kernel H C b).rel := by
  intro hMeet
  let K := Reached.kernel H C b
  let Kc : ParityHasse.Original.ColourEq S b.val :=
    ⟨K.setoid,ParityHasse.Relative.Exact.colourInvariant S H K.exact⟩
  let CR := ParityHasse.Relative.closureEq S H Kc R
    (ParityHasse.Relative.Exact.colourInvariant S H hR) satR
  let CT := ParityHasse.Relative.closureEq S H Kc T
    (ParityHasse.Relative.Exact.colourInvariant S H hT) satT
  let KR : Kernel S b.val := ⟨CR.val,
    ParityHasse.Relative.closure_exact S H cco Kc K.exact R hR hKR⟩
  let KT : Kernel S b.val := ⟨CT.val,
    ParityHasse.Relative.closure_exact S H cco Kc K.exact T hT hKT⟩
  have leR : K ≤ KR := fun x y hxy => ⟨0,hxy⟩
  have leT : K ≤ KT := fun x y hxy => ⟨0,hxy⟩
  have strictR : K < KR := by
    refine lt_iff_le_and_ne.mpr ⟨leR,?_⟩
    intro he
    obtain ⟨x,y,hxy,hn⟩ := outR
    have hp : KR.rel x y := ⟨1,by rw [ParityHasse.Relative.power_one K.setoid R satR]; exact hxy⟩
    rw [← he] at hp
    exact hn hp
  have strictT : K < KT := by
    refine lt_iff_le_and_ne.mpr ⟨leT,?_⟩
    intro he
    obtain ⟨x,y,hxy,hn⟩ := outT
    have hp : KT.rel x y := ⟨1,by rw [ParityHasse.Relative.power_one K.setoid T satT]; exact hxy⟩
    rw [← he] at hp
    exact hn hp
  let odd := P.atSort b
  obtain ⟨x,y,hxy⟩ := odd.exact.nonempty S
  have hpR := P.atSort_dominant b KR strictR x y hxy
  have hpT := P.atSort_dominant b KT strictT x y hxy
  have hsep := ParityHasse.Relative.closure_separation S H cco Kc K.exact
    R T hR hT hKR hKT satR satT hMeet
  have hp : K.rel x y := Eq.mp (congrFun (congrFun hsep x) y) ⟨hpR,hpT⟩
  exact P.atSort_nonidentity b (odd.eq_of_common_real_pair H (Arrow.id K) hxy hp)

structure ProperDomain (b : Reached S A) where
  rel : TRel X b.val b.val
  exact : FullExact S rel
  contains : ∀ x y, (Reached.kernel H C b).rel x y → rel x y
  saturated : ParityHasse.Relative.Bisaturated (Reached.kernel H C b).setoid rel
  outside : ∃ x y, rel x y ∧ ¬(Reached.kernel H C b).rel x y

namespace ProperDomain
variable {P} {b : Reached S A}

def top (P : SourcePhase S H C A) (b : Reached S A) : ProperDomain (H := H) (C := C) b where
  rel := TRel.top X b.val b.val
  exact := fullExact_top S _ _
  contains := fun _ _ _ => trivial
  saturated := ⟨by
    funext x y
    apply propext
    exact ⟨fun _ => trivial,fun _ => ⟨x,(Reached.kernel H C b).setoid.refl x,trivial⟩⟩,
    by
    funext x y
    apply propext
    exact ⟨fun _ => trivial,fun _ => ⟨y,trivial,(Reached.kernel H C b).setoid.refl y⟩⟩⟩
  outside := by
    obtain ⟨x,y,hxy⟩ := (P.atSort b).exact.nonempty S
    refine ⟨x,y,trivial,?_⟩
    intro hk
    exact P.atSort_nonidentity b ((P.atSort b).eq_of_common_real_pair H (Arrow.id _) hxy hk)

def meet (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
    (D E : ProperDomain (H := H) (C := C) b) : ProperDomain (H := H) (C := C) b where
  rel x y := D.rel x y ∧ E.rel x y
  exact := fullExact_meet S D.exact E.exact (by
    let x := Classical.choice (S.nonemptySort b.val)
    exact ⟨x,x,D.contains x x ((Reached.kernel H C b).setoid.refl x),
      E.contains x x ((Reached.kernel H C b).setoid.refl x)⟩)
  contains := fun x y hxy => ⟨D.contains x y hxy,E.contains x y hxy⟩
  saturated := ⟨by
    funext x y
    apply propext
    constructor
    · rintro ⟨z,hxz,hzy⟩
      exact ⟨D.saturated.left hxz hzy.1,E.saturated.left hxz hzy.2⟩
    · intro hxy
      exact ⟨x,(Reached.kernel H C b).setoid.refl x,hxy⟩,
    by
    funext x y
    apply propext
    constructor
    · rintro ⟨z,hxz,hzy⟩
      exact ⟨D.saturated.right hxz.1 hzy,E.saturated.right hxz.2 hzy⟩
    · intro hxy
      exact ⟨y,hxy,(Reached.kernel H C b).setoid.refl y⟩⟩
  outside := by
    have hn := P.gate_meet_not_kernel cco b D.rel E.rel D.exact E.exact
      D.contains E.contains D.saturated E.saturated D.outside E.outside
    by_contra hh
    apply hn
    funext x y
    apply propext
    constructor
    · intro hxy
      exact Classical.byContradiction fun hk => hh ⟨x,y,hxy,hk⟩
    · intro hxy
      exact ⟨D.contains x y hxy,E.contains x y hxy⟩

def meetList (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
    (b : Reached S A) : List (ProperDomain (H := H) (C := C) b) → ProperDomain (H := H) (C := C) b
  | [] => top P b
  | d :: ds => meet P cco d (meetList P cco b ds)

theorem meetList_relation (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
    (D : List (ProperDomain (H := H) (C := C) b)) :
    (meetList P cco b D).rel = fun x y => ∀ d ∈ D, d.rel x y := by
  induction D with
  | nil => funext x y; exact propext ⟨fun _ d hd => False.elim (List.not_mem_nil hd),fun _ => trivial⟩
  | cons d ds ih =>
    change (fun x y => d.rel x y ∧ (meetList P cco b ds).rel x y) = _
    rw [ih]
    funext x y
    simp only [List.mem_cons,forall_eq_or_imp]

end ProperDomain

end SourcePhase
end
end CCO.APCharacter
