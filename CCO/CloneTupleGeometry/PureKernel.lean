import CCO.CloneSAP.Quotient
import CCO.ParityHasse.Original.Equivalences

/-!
# B060 N01: pure clone kernels sit below every nonidentity FULL equivalence

This is the actual cloned named source, not an abstract quotient with an
assumed nontrivial kernel. The result is FULL: logical equality is retained
as a relation, and no STRONG identity letter is introduced.

The argument uses only the concrete original-colour-preserving clone
construction, rather than SAP, semantic CCO or a generic Ramsey lift.
-/

universe u v w
namespace CCO.CloneTupleGeometry

open CCO.ParityHasse.Original

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) (i : ι)

/-- B060 N01, C02–C05, pure source instance.
A nonidentity FULL original colour-invariant equivalence on the actual
infinite clone cover contains every real pair of the clone kernel.
The extra clone in the cross-owner case is explicit; no choice of
representatives or quotient SAP is assumed. -/
theorem pure_clone_kernel_le_nontrivial
    (E : ColourEq (CloneSAP.source S) i) (hE : E ≠ ⊥) :
    ∀ x y : CloneSAP.Carrier X i,
      (CloneSAP.kernelSetoid (X := X) i).r x y → E x y := by
  classical
  have hnontrivial :
      ∃ p q : CloneSAP.Carrier X i, E p q ∧ p ≠ q := by
    by_contra hn
    apply hE
    apply ColourEq.ext
    intro p q
    constructor
    · intro hpq
      by_contra hpqne
      exact hn ⟨p, q, hpq, hpqne⟩
    · intro hpq
      change p = q at hpq
      subst q
      exact E.val.refl p
  obtain ⟨p, q, hpq, hpqne⟩ := hnontrivial
  have hclone :
      ∃ a b : CloneSAP.Carrier X i, E a b ∧
        (CloneSAP.source S).colour a b = some (.inr ⟨rfl⟩) := by
    by_cases howner : p.1 = q.1
    · have hindex : p.2 ≠ q.2 := by
        intro h
        exact hpqne (Prod.ext howner h)
      exact ⟨p, q, hpq,
        (CloneSAP.source_clone_iff S p q).mpr ⟨howner, hindex⟩⟩
    · cases hcol : S.colour p.1 q.1 with
      | none =>
          have hsame : p.1 = q.1 := by
            have hh := (S.colour_none_iff p.1 q.1).mp hcol
            simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hh
          exact (howner hsame).elim
      | some a =>
          let p' : CloneSAP.Carrier X i := (p.1, p.2 + 1)
          have hc : (CloneSAP.source S).colour p q = some (.inl a) :=
            (CloneSAP.colour_old_iff S p q a).mpr hcol
          have hc' : (CloneSAP.source S).colour p' q = some (.inl a) :=
            (CloneSAP.colour_old_iff S p' q a).mpr hcol
          have hp'q : E p' q :=
            (E.property p q p' q (hc.trans hc'.symm)).mp hpq
          have hpp' : E p p' := E.val.trans hpq (E.val.symm hp'q)
          have hpp'col :
              (CloneSAP.source S).colour p p' = some (.inr ⟨rfl⟩) :=
            (CloneSAP.source_clone_iff S p p').mpr
              ⟨rfl, Nat.ne_of_lt (Nat.lt_succ_self _)⟩
          exact ⟨p, p', hpp', hpp'col⟩
  obtain ⟨a, b, hab, hc⟩ := hclone
  intro x y hxy
  change x.1 = y.1 at hxy
  by_cases hsame : x = y
  · subst y
    exact E.val.refl x
  have hindex : x.2 ≠ y.2 := by
    intro h
    exact hsame (Prod.ext hxy h)
  have hc' : (CloneSAP.source S).colour x y = some (.inr ⟨rfl⟩) :=
    (CloneSAP.source_clone_iff S x y).mpr ⟨hxy, hindex⟩
  exact (E.property a b x y (hc.trans hc'.symm)).mp hab

end CCO.CloneTupleGeometry
