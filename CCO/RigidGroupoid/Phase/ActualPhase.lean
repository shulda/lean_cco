import CCO.RigidGroupoid.Phase.SourceCharacter
import CCO.RigidGroupoid.Phase.ActualOrbitals
import CCO.RigidGroupoid.Phase.AbstractSeeds
import CCO.RigidGroupoid.Geometry.Source
import CCO.Finite

/-! C31: the abstract characters and seed functions act on the actual
kernel quotient classes of the original source. Every structural provider
is discharged. Bits pull back to original real points and remain constant
on their actual gate classes. No marked AP/SAP/CCO or kernel action is asserted. -/

universe u v w t
namespace CCO.RigidGroupoid.Phase
open Geometry CategoryTheory
noncomputable section

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G) (C : ExactCalculus S)

theorem actual_action_free {i : ι} (A : Kernel S i) :
    letI := Reached.groupoid H C (A := A)
    Abstract.Free (Reached.pointFunctor H C A) := by
  letI := Reached.groupoid H C (A := A)
  intro b c R T q he
  exact R.eq_of_agree_at H T q he

theorem actual_global_marking {i : ι} (A : Kernel S i)
    (χ : letI := Reached.groupoid H C (A := A); Abstract.Character (Reached S A)) :
    letI := Reached.groupoid H C (A := A)
    ∃ mark, Abstract.IsMarking (Reached.pointFunctor H C A) χ mark := by
  letI := Reached.groupoid H C (A := A)
  exact Abstract.exists_marking _ (actual_action_free S H C A) χ

/-- Actual rigid orbital graphs force their displayed character difference. -/
theorem actual_rigid_difference {i : ι} (A : Kernel S i)
    (χ : letI := Reached.groupoid H C (A := A); Abstract.Character (Reached S A))
    (mark : Reached.Point H C A → Abstract.Bit)
    (hm : letI := Reached.groupoid H C (A := A)
      Abstract.IsMarking (Reached.pointFunctor H C A) χ mark)
    {b c : Reached S A}
    (R : Arrow S (Reached.kernel H C b) (Reached.kernel H C c))
    (q : (Reached.kernel H C b).Class) :
    letI := Reached.groupoid H C (A := A)
    mark ⟨c,R.quotientMap H q⟩ - mark ⟨b,q⟩ = χ.value R := by
  letI := Reached.groupoid H C (A := A)
  exact Abstract.rigid_difference _ χ hm R q

/-- The nonrigid premise is stated in terms of the ACTUAL original G-pair
orbital, not merely a chosen abstract support classification. -/
theorem actual_nonrigid_both_differences {i : ι} (A : Kernel S i)
    (χ : letI := Reached.groupoid H C (A := A); Abstract.Character (Reached S A))
    (b c : Reached S A) (q : (Reached.kernel H C b).Class)
    (r : (Reached.kernel H C c).Class)
    (hnon : letI := (Reached.kernel H C b).action H
      letI := (Reached.kernel H C c).action H
      ∀ R : Arrow S (Reached.kernel H C b) (Reached.kernel H C c),
        GroupActions.orbital (G := G) q r ≠ (fun x y => R.quotientMap H x = y))
    (δ : Abstract.Bit) :
    letI := Reached.groupoid H C (A := A)
    ∃ mark, Abstract.IsMarking (Reached.pointFunctor H C A) χ mark ∧
      mark ⟨c,r⟩ = mark ⟨b,q⟩ + δ := by
  letI := Reached.groupoid H C (A := A)
  apply Abstract.different_orbits_both_differences _ (actual_action_free S H C A) χ
  exact nonrigid_different_orbits S H q r hnon

/-- Literal finite quotient-point sets already impose consistency of
different real representatives of a single gate class. -/
theorem actual_finite_seed_extension_iff {i : ι} (A : Kernel S i)
    (χ : letI := Reached.groupoid H C (A := A); Abstract.Character (Reached S A))
    (s : Finset (Reached.Point H C A)) (ε : s → Abstract.Bit) :
    letI := Reached.groupoid H C (A := A)
    (∃ mark, Abstract.IsMarking (Reached.pointFunctor H C A) χ mark ∧
      ∀ p : s, mark p.val = ε p) ↔
    ∀ (p q : s)
      (R : Arrow S (Reached.kernel H C p.val.1) (Reached.kernel H C q.val.1)),
      R.quotientMap H p.val.2 = q.val.2 → ε q = ε p + χ.value R := by
  letI := Reached.groupoid H C (A := A)
  exact Abstract.finite_seed_extension_iff _ (actual_action_free S H C A) χ s ε

/-- Pullback on ALL original named sorts. Unreached sorts receive a harmless
zero bit; on every reached sort the bit is read from its actual kernel class. -/
def originalMarking {i : ι} (A : Kernel S i)
    (mark : Reached.Point H C A → Abstract.Bit) (p : Sigma X) : Abstract.Bit := by
  classical
  exact if h : Nonempty (Bridge S A p.1) then
    mark ⟨⟨p.1,h⟩,(Reached.kernel H C ⟨p.1,h⟩).project p.2⟩ else 0

theorem originalMarking_reached {i : ι} (A : Kernel S i)
    (mark : Reached.Point H C A → Abstract.Bit) (b : Reached S A) (x : X b.val) :
    originalMarking S H C A mark ⟨b.val,x⟩ =
      mark ⟨b,(Reached.kernel H C b).project x⟩ := by
  classical
  rcases b with ⟨j,hj⟩
  unfold originalMarking
  rw [dif_pos hj]

theorem originalMarking_constant {i : ι} (A : Kernel S i)
    (mark : Reached.Point H C A → Abstract.Bit) (b : Reached S A)
    (x y : X b.val) (hxy : (Reached.kernel H C b).rel x y) :
    originalMarking S H C A mark ⟨b.val,x⟩ =
      originalMarking S H C A mark ⟨b.val,y⟩ := by
  rw [originalMarking_reached, originalMarking_reached]
  exact congrArg (fun q => mark ⟨b,q⟩) (Quotient.sound hxy)

/-- Conflicting bits on two representatives of one actual quotient point
cannot be supplied by a global marking. This is genuine equality consistency,
not a missing diversity or extra holonomy condition. -/
theorem real_representative_consistency {i : ι} (A : Kernel S i)
    (mark : Reached.Point H C A → Abstract.Bit) (b : Reached S A)
    (x y : X b.val) (hxy : (Reached.kernel H C b).rel x y)
    (εx εy : Abstract.Bit)
    (hx : originalMarking S H C A mark ⟨b.val,x⟩ = εx)
    (hy : originalMarking S H C A mark ⟨b.val,y⟩ = εy) : εx = εy :=
  hx.symm.trans ((originalMarking_constant S H C A mark b x y hxy).trans hy)

theorem originalMarking_arrow_equation {i : ι} (A : Kernel S i)
    (χ : letI := Reached.groupoid H C (A := A); Abstract.Character (Reached S A))
    (mark : Reached.Point H C A → Abstract.Bit)
    (hm : letI := Reached.groupoid H C (A := A)
      Abstract.IsMarking (Reached.pointFunctor H C A) χ mark)
    {b c : Reached S A}
    (R : Arrow S (Reached.kernel H C b) (Reached.kernel H C c))
    (x : X b.val) (y : X c.val) (hxy : R.rel x y) :
    letI := Reached.groupoid H C (A := A)
    originalMarking S H C A mark ⟨c.val,y⟩ =
      originalMarking S H C A mark ⟨b.val,x⟩ + χ.value R := by
  letI := Reached.groupoid H C (A := A)
  rw [originalMarking_reached, originalMarking_reached]
  have he := hm R ((Reached.kernel H C b).project x)
  change mark ⟨c,R.quotientMap H ((Reached.kernel H C b).project x)⟩ = _ at he
  rw [(R.quotientMap_eq_iff H x y).mpr hxy] at he
  exact he

/-- Every ACTUAL finite original induced structure has an expansion by bits
obtained from one global quotient marking. Its reduct is literally the same
finite induced structure, including empty sets and unreached original sorts. -/
theorem finite_original_reduct_surjective {i : ι} (A : Kernel S i)
    (χ : letI := Reached.groupoid H C (A := A); Abstract.Character (Reached S A))
    (D : FiniteInduced (X := X)) :
    letI := Reached.groupoid H C (A := A)
    ∃ ε : D.vertices → Abstract.Bit,
      ∃ mark, Abstract.IsMarking (Reached.pointFunctor H C A) χ mark ∧
        ∀ p : D.vertices, ε p = originalMarking S H C A mark p.val := by
  letI := Reached.groupoid H C (A := A)
  obtain ⟨mark,hm⟩ := actual_global_marking S H C A χ
  exact ⟨fun p => originalMarking S H C A mark p.val, mark,hm,fun _ => rfl⟩

/-- A distinguished nonidentity arrow is the ONLY extra source input for
choosing a detecting character. The actual finite connected free action and
all isotropy/character/seed providers are constructed above. -/
theorem actual_source_phase {i : ι} (A : Kernel S i) (o : Reached S A)
    (t : Arrow S (Reached.kernel H C o) (Reached.kernel H C o))
    (ht : t ≠ Arrow.id (Reached.kernel H C o)) :
    letI := Reached.groupoid H C (A := A)
    ∃ χ : Abstract.Character (Reached S A),
      χ.value t = 1 ∧ ∃ mark, Abstract.IsMarking (Reached.pointFunctor H C A) χ mark := by
  letI := Reached.groupoid H C (A := A)
  obtain ⟨χ,hχ,_⟩ := actual_source_character S H C A o t ht
  obtain ⟨mark,hm⟩ := actual_global_marking S H C A χ
  exact ⟨χ,hχ,mark,hm⟩

/-- Standing original homogeneous CCO instance, retaining its countability
convention without postulating homogeneity or CCO of any quotient. -/
theorem standing_source_phase (cco : SemanticCCO.{u,v,max u v,w} S)
    (_countableSorts : ∀ j, Countable (X j)) {i : ι} (A : Kernel S i)
    (o : Reached S A)
    (t : Arrow S
      (Reached.kernel H (exactCalculus_of_homogeneous_CCO S H cco) o)
      (Reached.kernel H (exactCalculus_of_homogeneous_CCO S H cco) o))
    (ht : t ≠ Arrow.id (Reached.kernel H (exactCalculus_of_homogeneous_CCO S H cco) o)) :
    let C := exactCalculus_of_homogeneous_CCO S H cco
    letI := Reached.groupoid H C (A := A)
    ∃ χ : Abstract.Character (Reached S A), χ.value t = 1 ∧
      ∃ mark, Abstract.IsMarking (Reached.pointFunctor H C A) χ mark :=
  actual_source_phase S H (exactCalculus_of_homogeneous_CCO S H cco) A o t ht

/-- A downstream original-source consumer with BOTH the detecting character
and the marking of an arbitrary given finite original induced structure
constructed, rather than supplied as extra inputs. -/
theorem standing_finite_marked_reduct (cco : SemanticCCO.{u,v,max u v,w} S)
    (_countableSorts : ∀ j, Countable (X j)) {i : ι} (A : Kernel S i)
    (o : Reached S A)
    (t : Arrow S
      (Reached.kernel H (exactCalculus_of_homogeneous_CCO S H cco) o)
      (Reached.kernel H (exactCalculus_of_homogeneous_CCO S H cco) o))
    (ht : t ≠ Arrow.id (Reached.kernel H (exactCalculus_of_homogeneous_CCO S H cco) o))
    (D : FiniteInduced (X := X)) :
    let C := exactCalculus_of_homogeneous_CCO S H cco
    letI := Reached.groupoid H C (A := A)
    ∃ χ : Abstract.Character (Reached S A), χ.value t = 1 ∧
      ∃ ε : D.vertices → Abstract.Bit,
        ∃ mark, Abstract.IsMarking (Reached.pointFunctor H C A) χ mark ∧
          ∀ p : D.vertices, ε p = originalMarking S H C A mark p.val := by
  let C := exactCalculus_of_homogeneous_CCO S H cco
  letI := Reached.groupoid H C (A := A)
  obtain ⟨χ,hχ,_⟩ := actual_source_character S H C A o t ht
  exact ⟨χ,hχ,finite_original_reduct_surjective S H C A χ D⟩

end
end CCO.RigidGroupoid.Phase
