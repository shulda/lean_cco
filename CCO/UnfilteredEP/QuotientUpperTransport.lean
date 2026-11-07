import CCO.TransitionClosure.OriginalTransportTargetFull
import CCO.QuotientTransport.Lattice

/-! B064 C44: every actual equivariant quotient bijection transports the
ENTIRE upper interval of FULL original invariant equivalences. This is
independent of Ramsey, EP, source terminality and finite MI charts. -/

universe u v w t
namespace CCO.UnfilteredEP
open ParityHasse.Original TransitionClosure QuotientTransport
noncomputable section

namespace QuotientInvariantTransport
variable {G : Type t} [Group G] {A B : Type v}
variable [MulAction G A] [MulAction G B]
variable (D : InvEq G A) (E : InvEq G B)
variable (e : Quotient D.val ≃ Quotient E.val)
variable (equivariant : ∀ g q, e (D.act g q) = E.act g (e q))

include equivariant in
theorem inverse_equivariant (g : G) (q : Quotient E.val) :
    e.symm (E.act g q) = D.act g (e.symm q) := by
  apply e.injective
  rw [e.apply_symm_apply,equivariant,e.apply_symm_apply]

/-- Conjugation of ALL invariant quotient setoids, retaining literal
relations and actual quotient points. -/
def iso : Transport.QuotientInvariantEq D ≃o Transport.QuotientInvariantEq E where
  toFun F := ⟨Setoid.comap e.symm F.val,by
    intro g q r h
    change F.val (e.symm (E.act g q)) (e.symm (E.act g r))
    rw [inverse_equivariant D E e equivariant,inverse_equivariant D E e equivariant]
    exact F.property g _ _ h⟩
  invFun F := ⟨Setoid.comap e F.val,by
    intro g q r h
    change F.val (e (D.act g q)) (e (D.act g r))
    rw [equivariant,equivariant]
    exact F.property g _ _ h⟩
  left_inv F := by
    apply Subtype.ext
    apply Setoid.ext
    intro q r
    change F.val (e.symm (e q)) (e.symm (e r)) ↔ F.val q r
    simp only [Equiv.symm_apply_apply]
  right_inv F := by
    apply Subtype.ext
    apply Setoid.ext
    intro q r
    change F.val (e (e.symm q)) (e (e.symm r)) ↔ F.val q r
    simp only [Equiv.apply_symm_apply]
  map_rel_iff' := by
    intro F K
    constructor
    · intro h q r hqr
      have hh := @h (e q) (e r)
      change F.val (e.symm (e q)) (e.symm (e r)) →
        K.val (e.symm (e q)) (e.symm (e r)) at hh
      have hh' : F.val q r → K.val q r := by
        simpa only [Equiv.symm_apply_apply] using hh
      exact hh' hqr
    · intro h q r hqr
      exact @h _ _ hqr
end QuotientInvariantTransport

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) {i j : ι}
variable (D : ColourEq S i) (E : ColourEq S j)

/-- Restriction of the actual FULL source invariant-lattice isomorphism. -/
def colourUpperInvariantIso :
    {J : ColourEq S i // D ≤ J} ≃o
      {J : InvEq G (X i) // originalColourEqAsInvEq S H D ≤ J} where
  toFun J := ⟨originalColourEqAsInvEq S H J.val,J.property⟩
  invFun J := ⟨(originalFullColourEqInvEqOrderIso S H).symm J.val,J.property⟩
  left_inv J := Subtype.ext ((originalFullColourEqInvEqOrderIso S H).left_inv J.val)
  right_inv J := Subtype.ext ((originalFullColourEqInvEqOrderIso S H).right_inv J.val)
  map_rel_iff' := Iff.rfl

/-- Explicit same-original-group equivariance. B040's action is the
literal quotient action: on representatives it sends [x] to [g*x]. -/
def QuotientEquivariant (e : Quotient D.val ≃ Quotient E.val) : Prop :=
  ∀ g q, e ((originalColourEqAsInvEq S H D).act g q) =
    (originalColourEqAsInvEq S H E).act g (e q)

/-- C44: all full upper equivalences transport in both directions. -/
def quotientUpperIso (e : Quotient D.val ≃ Quotient E.val)
    (equivariant : QuotientEquivariant S H D E e) :
    {J : ColourEq S i // D ≤ J} ≃o {K : ColourEq S j // E ≤ K} :=
  (colourUpperInvariantIso S H D).trans
    ((Transport.quotientCorrespondence (originalColourEqAsInvEq S H D)).trans
      ((QuotientInvariantTransport.iso (originalColourEqAsInvEq S H D)
        (originalColourEqAsInvEq S H E) e equivariant).trans
        ((Transport.quotientCorrespondence (originalColourEqAsInvEq S H E)).symm.trans
          (colourUpperInvariantIso S H E).symm)))

/-- Transported full relations have the exact descended quotient meaning. -/
theorem quotientUpperIso_relation (e : Quotient D.val ≃ Quotient E.val)
    (equivariant : QuotientEquivariant S H D E e)
    (J : {J : ColourEq S i // D ≤ J}) (q r : Quotient D.val) :
    Transport.descend (E := originalColourEqAsInvEq S H E) (originalColourEqAsInvEq S H (quotientUpperIso S H D E e equivariant J).val)
      (quotientUpperIso S H D E e equivariant J).property (e q) (e r) ↔
    Transport.descend (E := originalColourEqAsInvEq S H D) (originalColourEqAsInvEq S H J.val) J.property q r := by
  let CD := Transport.quotientCorrespondence (originalColourEqAsInvEq S H D)
  let CE := Transport.quotientCorrespondence (originalColourEqAsInvEq S H E)
  let F := (QuotientInvariantTransport.iso (originalColourEqAsInvEq S H D)
    (originalColourEqAsInvEq S H E) e equivariant)
    (CD (colourUpperInvariantIso S H D J))
  have same := congrArg Subtype.val (CE.apply_symm_apply F)
  have relation := Iff.of_eq (congrArg (fun K : Setoid (Quotient E.val) => K (e q) (e r)) same)
  change (Transport.descend (E := originalColourEqAsInvEq S H E)
      (originalColourEqAsInvEq S H (quotientUpperIso S H D E e equivariant J).val)
      (quotientUpperIso S H D E e equivariant J).property (e q) (e r)) ↔
    (Transport.descend (E := originalColourEqAsInvEq S H D)
      (originalColourEqAsInvEq S H J.val) J.property)
      (e.symm (e q)) (e.symm (e r)) at relation
  simpa only [Equiv.symm_apply_apply] using relation

end
end CCO.UnfilteredEP
