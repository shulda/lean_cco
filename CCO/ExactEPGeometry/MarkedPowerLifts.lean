import CCO.ExactEPGeometry.OriginalPowers
import CCO.ExactEPGeometry.MarkedJoins

/-!
# B062 C32: original exact-power lifts preserve their real child trace

Given an actual old RAW exact domain D whose genuinely represented marked
child trace is an equivalence, old diagonal containment follows from
the previously proved real C31 theorem. The finite original RAW exact
powers stabilize by the accepted source finiteness result. Each positive
power has exactly the SAME marked trace, using genuine AP-only C22 with
two nonempty displayed-child witnesses at every multiplication.

This does not assume an old exact domain lift exists for every current
exact domain (separate C23–C28), nor does it assert arbitrary prefix
iteration or quotient SAP.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter RigidGroupoid.Geometry
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)

/-- Positive old powers of a represented original D all have precisely
the original actual CURRENT equivalence trace on the displayed child.
The source D need not itself be an old equivalence. -/
theorem markedChild_originalPower_iff
    {C : ExactCalculus S} {r : ι} {A : Kernel S r}
    (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (D : RawExact.NonemptyExact S i i) (ε : Bit)
    (hCurrent : RawSymmetric.EquivRel
      (markedChildRelation S H (P.completion_property cco)
        (RawExact.evaluate S D.words) ε))
    (n : ℕ) :
    ∀ a b : MarkedChild S H (P.completion_property cco) i ε,
      markedChildRelation S H (P.completion_property cco)
        (originalPower (RawExact.evaluate S D.words) n) ε a b ↔
      markedChildRelation S H (P.completion_property cco)
        (RawExact.evaluate S D.words) ε a b := by
  induction n with
  | zero =>
      intro a b
      exact Iff.rfl
  | succ n ih =>
      intro a b
      let R := RawExact.evaluate S D.words
      have hExactPower : FullExact S (originalPower R n) :=
        originalPower_exact S C R ⟨D,rfl⟩ n
      obtain ⟨F,hF⟩ := hExactPower
      have hInputPower : ∃ x y : Age.Limit S H (P.completion_property cco),
          markedTrace S H (P.completion_property cco)
            (RawExact.evaluate S F.words) ε ε x y := by
        refine ⟨a.val,a.val,?_⟩
        have hPow : markedChildRelation S H (P.completion_property cco)
            (originalPower R n) ε a a :=
          (ih a a).mpr (hCurrent.refl a)
        change markedTrace S H (P.completion_property cco)
          (RawExact.evaluate S F.words) ε ε a.val a.val
        rw [hF]
        exact hPow
      have hInputD : ∃ x y : Age.Limit S H (P.completion_property cco),
          markedTrace S H (P.completion_property cco)
            (RawExact.evaluate S D.words) ε ε x y :=
        ⟨a.val,a.val,hCurrent.refl a⟩
      have hTP :=
        marked_trace_product S H P cco F D ε ε ε
          hInputPower hInputD a.val b.val
      have hProductEq : TRel.comp
          (RawExact.evaluate S F.words) (RawExact.evaluate S D.words) =
          originalPower R (n+1) := by
        rw [hF]
        rfl
      rw [hProductEq] at hTP
      constructor
      · intro h
        obtain ⟨m, hLeft, hRight⟩ := hTP.mpr h
        let mid : MarkedChild S H (P.completion_property cco) i ε :=
          ⟨m,hLeft.2.1⟩
        have hLeftPower : markedChildRelation S H (P.completion_property cco)
            (originalPower R n) ε a mid := by
          change markedTrace S H (P.completion_property cco)
            (originalPower R n) ε ε a.val m
          rw [← hF]
          exact hLeft
        exact hCurrent.trans a mid b ((ih a mid).mp hLeftPower) hRight
      · intro h
        apply hTP.mp
        refine ⟨b.val, ?_, hCurrent.refl b⟩
        have hPow : markedChildRelation S H (P.completion_property cco)
            (originalPower R n) ε a b := (ih a b).mpr h
        change markedTrace S H (P.completion_property cco)
          (RawExact.evaluate S F.words) ε ε a.val b.val
        rw [hF]
        exact hPow

/-- C32 on one actual child AFTER obtaining an original exact-domain
lift D: its trace is a current equivalence, and the conclusion supplies
a genuine old FULL-exact EQUIVALENCE with identical current trace.
The existence of D from arbitrary current exact profiles remains C27. -/
theorem markedChild_stable_exact_equivalence_lift
    {C : ExactCalculus S} {r : ι} {A : Kernel S r}
    (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (D : RawExact.NonemptyExact S i i) (ε : Bit)
    (a : MarkedChild S H (P.completion_property cco) i ε)
    (hCurrent : RawSymmetric.EquivRel
      (markedChildRelation S H (P.completion_property cco)
        (RawExact.evaluate S D.words) ε)) :
    ∃ E : RawExact.NonemptyExact S i i,
      RawSymmetric.EquivRel (RawExact.evaluate S E.words) ∧
      ∀ x y : MarkedChild S H (P.completion_property cco) i ε,
        markedChildRelation S H (P.completion_property cco)
          (RawExact.evaluate S E.words) ε x y ↔
        markedChildRelation S H (P.completion_property cco)
          (RawExact.evaluate S D.words) ε x y := by
  let R := RawExact.evaluate S D.words
  have hDiag : markedTrace S H (P.completion_property cco)
      (RawExact.evaluate S D.words) ε ε a.val a.val :=
    hCurrent.refl a
  have hOldRef : ∀ x : X i, R x x :=
    (old_exact_reflexive_symmetric_of_marked_diagonal S H P cco
      D ε a.val hDiag).1
  have hExact : FullExact S R := ⟨D,rfl⟩
  obtain ⟨n,hStable⟩ := originalPower_stabilizes S H C R hExact hOldRef
  obtain ⟨E,hE⟩ := originalPower_exact S C R hExact n
  have hOldEquiv : RawSymmetric.EquivRel (RawExact.evaluate S E.words) := by
    rw [hE]
    exact originalPower_equiv_of_stable S H C R hExact hOldRef n hStable
  refine ⟨E,hOldEquiv,?_⟩
  intro x y
  rw [hE]
  exact markedChild_originalPower_iff S H P cco D ε hCurrent n x y

end
end CCO.ExactEPGeometry
