import CCO.RankInduction.AmalgamationBridge
import CCO.RankInduction.KernelSplit

/-! The unique-direction branch calls the actual normalized relative
constructor with its literal singleton Top owner. Only ordinary EPPA of
the strict fine quotient is recursive. -/

universe v w t
namespace CCO.RankInduction
noncomputable section
open RawExact ExactCRT Owners.Product Owners.Provider
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization AclOwners RelativeMI

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] [Countable M] [DecidableEq M] [Infinite M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (normalized : NoFiniteExactKernel S) (D : Direction S)
variable (unique : ∀ D' : Direction S, D' = D)

include H cco normalized unique in
theorem one_direction_acl (A0 : Finset M) :
    FiniteLift.aclSet G (↑A0 : Set M) = RealClosure.Bounds.packetClosure S H A0 :=
  (fullRealAcl_eq S H A0).symm.trans
    (normalized_absolute_acl S H (semanticCCO_change_universe S cco) normalized D unique A0)

local instance topOwnerAction : MulAction G (Coarse S H (⊤ : ColourEq S ())) :=
  originalQuotientAction S H ⊤

omit [Countable M] [DecidableEq M] [Infinite M] in
theorem top_owner_subsingleton : Subsingleton (Coarse S H (⊤ : ColourEq S ())) := by
  refine ⟨?_⟩
  intro x y
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b => exact Quotient.sound trivial

include cco normalized unique in
theorem top_owner_witness (ep : letI := originalQuotientAction S H D.val
      OrdinaryEPPA G (Quotient D.val.val))
    (safe : Set (S.Atom () ()))
    (hs : FiniteLift.StrongClosedAmalgamation G (FiniteLift.aclSet G) (S.menuRel safe))
    (A0 : Finset M) (nonemptyA : A0.Nonempty) :
    ∃ (B : Finset (Coarse S H (⊤ : ColourEq S ())))
      (over : ∀ x : ↥A0, coarseOwner S H ⊤ x.val ∈ B),
      Nonempty (OriginalWitness S H ⊤ A0 B over safe) := by
  classical
  have := top_owner_subsingleton S H
  obtain ⟨a,ha⟩ := nonemptyA
  let B : Finset (Coarse S H (⊤ : ColourEq S ())) := {coarseOwner S H ⊤ a}
  have over : ∀ x : ↥A0, coarseOwner S H ⊤ x.val ∈ B := by
    intro x
    exact Finset.mem_singleton.mpr (Subsingleton.elim _ _)
  have eppaB : CoarseEPPAFor S H ⊤ A0 B := by
    intro p _ _
    exact ⟨1,fun _ => Subsingleton.elim _ _⟩
  have orbit : CoarseOrbitCover S H ⊤ A0 B over := by
    intro b
    exact ⟨1,⟨a,ha⟩,Subsingleton.elim _ _⟩
  have closedB : ∀ b ∈ B, ∀ c,
      ownerPacket S H (coarseOwner S H ⊤) Quotient.mk''_surjective (fun _ _ => rfl) b c → c ∈ B := by
    intro _ _ c _
    exact Finset.mem_singleton.mpr (Subsingleton.elim _ _)
  exact ⟨B,over,normalized_relative_mi S H ⊤ (semanticCCO_change_universe S cco)
    normalized D unique (isExactEq_top S ()) le_top ep safe
    (finset_strong_closed S H safe hs) A0 ⟨a,ha⟩ B over eppaB orbit closedB⟩

include cco normalized unique in
theorem one_direction_closed_witness
    (ep : letI := originalQuotientAction S H D.val
      OrdinaryEPPA G (Quotient D.val.val))
    (safe : Set (S.Atom () ()))
    (hs : FiniteLift.StrongClosedAmalgamation G (FiniteLift.aclSet G) (S.menuRel safe))
    (A0 : Finset M) (nonemptyA : A0.Nonempty) :
    ∃ W : Set M, Witness S G safe (↑A0) W ∧ FiniteLift.aclSet G W = W := by
  classical
  have := top_owner_subsingleton S H
  obtain ⟨B,over,⟨W⟩⟩ := top_owner_witness S H cco normalized D unique ep safe hs A0 nonemptyA
  have aclA := one_direction_acl S H cco normalized D unique A0
  refine ⟨W.carrier,⟨W.finite,?_,?_,?_⟩,?_⟩
  · rw [aclA]
    exact W.contains
  · intro p dom ran
    let q : OrbitalPartial (G := G) (Subtype.val : ↥A0 → M) := {
      domain := {x | W.sourcePoint x ∈ p.domain}
      map x := ⟨(p.map ⟨W.sourcePoint x.val,x.property⟩).val,ran _⟩
      injective := by
        intro x y hxy
        have hv : (p.map ⟨W.sourcePoint x.val,x.property⟩).val =
            (p.map ⟨W.sourcePoint y.val,y.property⟩).val :=
          congrArg (fun a : ↥A0 => a.val) hxy
        have h := p.injective (Subtype.ext hv)
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : p.domain => z.val.val) h
      pair x y := p.pair ⟨W.sourcePoint x.val,x.property⟩ ⟨W.sourcePoint y.val,y.property⟩ }
    let r : OriginalRequest S H ⊤ A0 B over := {
      part := q
      owner := 1
      compatible := fun _ => Subsingleton.elim _ _ }
    obtain ⟨β,-,hβ⟩ := W.extensions r
    refine ⟨β,?_⟩
    intro x
    let a : ↥A0 := ⟨x.val.val,dom x.property⟩
    have ha : W.sourcePoint a = x.val := Subtype.ext rfl
    let x' : q.domain := ⟨a,by change W.sourcePoint a ∈ p.domain; rw [ha]; exact x.property⟩
    have hp := hβ x'
    change (β.val (W.sourcePoint a)).val = (p.map ⟨W.sourcePoint a,x'.property⟩).val at hp
    apply Subtype.ext
    simpa only [ha] using hp
  · intro Z hZ z hz
    have unsafeZ : UnsafeSet S (Subtype.val : W.carrier → M) safe Z := by
      intro x hx y hy hxy a hcol ha
      exact hZ.2 x hx y hy hxy ⟨a,ha,hcol⟩
    obtain ⟨β,hβ,hz'⟩ := W.rooted Z unsafeZ z hz
    refine ⟨β,?_,hz'⟩
    intro x hx
    rw [aclA]
    exact hβ x hx
  · apply Set.Subset.antisymm
    · intro x hx
      let U := W.finite.toFinset
      have hU : (↑U : Set M) = W.carrier := W.finite.coe_toFinset
      rw [← hU,one_direction_acl S H cco normalized D unique U] at hx
      obtain ⟨y,hy,hF⟩ := hx
      exact W.closed y (hU ▸ hy) x hF
    · exact FiniteLift.subset_aclSet G W.carrier

omit [Countable M] [DecidableEq M] [Infinite M] in
theorem one_direction_fine_kernel_proper :
    (⟨D.val.val,direction_exact S H (semanticCCO_change_universe S cco) D⟩ : ExactEq S H cco ()) ≠ ⊥ := by
  intro he
  apply D.property.1
  have hD : D.val = ⊥ := by
    apply ColourEq.ext
    intro x y
    exact Iff.of_eq (congrArg (fun E : ExactEq S H cco () => E.val.r x y) he)
  rw [hD]
  exact finiteClasses_bot S

include normalized unique in
theorem one_direction_under_lower (lower : Lower S G H cco)
    (safe : Set (S.Atom () ()))
    (hs : FiniteLift.StrongClosedAmalgamation G (FiniteLift.aclSet G) (S.menuRel safe))
    (A0 : Set M) (finiteA : A0.Finite) (nonemptyA : A0.Nonempty) :
    ∃ W : Set M, Witness S G safe A0 W ∧ FiniteLift.aclSet G W = W := by
  classical
  let E : ExactEq S H cco () :=
    ⟨D.val.val,direction_exact S H (semanticCCO_change_universe S cco) D⟩
  have proper : E ≠ ⊥ := one_direction_fine_kernel_proper S H cco D
  have ep : letI := originalQuotientAction S H D.val
      OrdinaryEPPA G (Quotient D.val.val) := (lower E proper).2.1
  let A := finiteA.toFinset
  have hA : (↑A : Set M) = A0 := finiteA.coe_toFinset
  have nonempty : A.Nonempty := by
    obtain ⟨a,ha⟩ := nonemptyA
    exact ⟨a,(finiteA.mem_toFinset).mpr ha⟩
  obtain ⟨W,hW,hclosed⟩ := one_direction_closed_witness S H cco normalized D unique
    ep safe hs A nonempty
  exact ⟨W,hA ▸ hW,hclosed⟩

end
end CCO.RankInduction
