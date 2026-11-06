import CCO.ExactEPGeometry.ExactTraceTransport

/-!
# B062 (TP across prefixes): literal typed trace products compose

This is an independent, fully semantic composition interface. Its axiom-free
proof does NOT infer (TP) from arbitrary unary refinement. Each stage must
discharge its own (TP) theorem with both nonempty input-trace hypotheses.
The canonical AP-only marked-age step discharges that using the real C22.

The result concerns the entire represented composite of actual relations,
not just the palettes of allowed pairs, and preserves the SPECIFIED middle
unary sort in every displayed product.
-/

universe u v w

namespace CCO.ExactEPGeometry

open APCharacter.Towers

/-- Actual (TP) for a single named reduct, with exactly the two guards
required by the pinned source. The middle witness on the left belongs
to the DISPLAYED current sort; the witness on the right is an old point. -/
structure ExactTraceProduct
    {ι κ : Type u} {X : ι → Type v} {Y : κ → Type v}
    (S : AtomicSource.{u,v,w} ι X)
    (T : AtomicSource.{u,v,w} κ Y)
    (P : UnaryReduct S T) : Prop where
  product :
    ∀ {i j k : κ}
      (D : RawExact.NonemptyExact S (P.parent i) (P.parent j))
      (E : RawExact.NonemptyExact S (P.parent j) (P.parent k)),
      (∃ x : Y i, ∃ y : Y j,
        RawExact.evaluate S D.words (P.point i x) (P.point j y)) →
      (∃ y : Y j, ∃ z : Y k,
        RawExact.evaluate S E.words (P.point j y) (P.point k z)) →
      ∀ x : Y i, ∀ z : Y k,
        (∃ y : Y j,
          RawExact.evaluate S D.words (P.point i x) (P.point j y) ∧
          RawExact.evaluate S E.words (P.point j y) (P.point k z)) ↔
        TRel.comp (RawExact.evaluate S D.words)
          (RawExact.evaluate S E.words)
          (P.point i x) (P.point k z)

namespace ExactTraceProduct

variable {ι κ ν : Type u}
variable {X : ι → Type v} {Y : κ → Type v} {Z : ν → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {T : AtomicSource.{u,v,w} κ Y}
variable {U : AtomicSource.{u,v,w} ν Z}

/-- Zero stages preserve exact displayed-middle products literally. -/
theorem identity (S : AtomicSource.{u,v,w} ι X) :
    ExactTraceProduct S S (UnaryReduct.identity S) := by
  constructor
  intro i j k D E _ _ x z
  exact Iff.rfl

/-- Induct the source (TP) equation through an ACTUAL intermediate
homogeneous source. First represent the two OLD exact factors as nonempty
intermediate exact domains, then use the intermediate and next-stage (TP)
in succession. The required nonempty traces at both stages are witnessed
by the SAME real source pairs, never by formal atomic-set intersections. -/
theorem compose
    (P : UnaryReduct S T) (Q : UnaryReduct T U)
    (hP : ExactTraceTransport S T P)
    (tpP : ExactTraceProduct S T P)
    (hQ : ExactTraceTransport T U Q)
    (tpQ : ExactTraceProduct T U Q) :
    ExactTraceProduct S U (P.compose Q) := by
  constructor
  intro i j k D E hD hE x z
  obtain ⟨a,b,hab⟩ := hD
  obtain ⟨b',c,hbc⟩ := hE
  have hDMiddle :
      ∃ a' : Y (Q.parent i), ∃ b'' : Y (Q.parent j),
        RawExact.evaluate S D.words
          (P.point (Q.parent i) a') (P.point (Q.parent j) b'') :=
    ⟨Q.point i a,Q.point j b,hab⟩
  have hEMiddle :
      ∃ b'' : Y (Q.parent j), ∃ c' : Y (Q.parent k),
        RawExact.evaluate S E.words
          (P.point (Q.parent j) b'') (P.point (Q.parent k) c') :=
    ⟨Q.point j b',Q.point k c,hbc⟩
  obtain ⟨DM,hDM⟩ := hP.old_to_new D hDMiddle
  obtain ⟨EM,hEM⟩ := hP.old_to_new E hEMiddle
  have hDNext :
      ∃ a' : Z i, ∃ b'' : Z j,
        RawExact.evaluate T DM.words (Q.point i a') (Q.point j b'') :=
    ⟨a,b,(hDM (Q.point i a) (Q.point j b)).mpr hab⟩
  have hENext :
      ∃ b'' : Z j, ∃ c' : Z k,
        RawExact.evaluate T EM.words (Q.point j b'') (Q.point k c') :=
    ⟨b',c,(hEM (Q.point j b') (Q.point k c)).mpr hbc⟩
  have hNext := tpQ.product DM EM hDNext hENext x z
  have hMiddle := tpP.product D E hDMiddle hEMiddle
    (Q.point i x) (Q.point k z)
  constructor
  · rintro ⟨y,hxy,hyz⟩
    have hCompMiddle :
        TRel.comp (RawExact.evaluate T DM.words)
          (RawExact.evaluate T EM.words) (Q.point i x) (Q.point k z) :=
      hNext.mp ⟨y,(hDM (Q.point i x) (Q.point j y)).mpr hxy,
        (hEM (Q.point j y) (Q.point k z)).mpr hyz⟩
    obtain ⟨v,hDv,hEv⟩ := hCompMiddle
    exact hMiddle.mp ⟨v,
      (hDM (Q.point i x) v).mp hDv,
      (hEM v (Q.point k z)).mp hEv⟩
  · intro hOldComp
    obtain ⟨v,hDv,hEv⟩ := hMiddle.mpr hOldComp
    have hCompMiddle :
        TRel.comp (RawExact.evaluate T DM.words)
          (RawExact.evaluate T EM.words) (Q.point i x) (Q.point k z) :=
      ⟨v,(hDM (Q.point i x) v).mpr hDv,
        (hEM v (Q.point k z)).mpr hEv⟩
    obtain ⟨y,hDy,hEy⟩ := hNext.mpr hCompMiddle
    exact ⟨y,(hDM (Q.point i x) (Q.point j y)).mp hDy,
      (hEM (Q.point j y) (Q.point k z)).mp hEy⟩

end ExactTraceProduct
end CCO.ExactEPGeometry
