import CCO.AclOwners.ProjectionAlgebraicity

/-! Full finite inverse-image intersections and absolute closure.
No owner-closure premise or compatible-tuple surjectivity is used. -/
universe v w t z q
namespace CCO.AclOwners
open RealClosure.Bounds ParityHasse.Original FinitePackets.Normalization RawExact

section Pure
variable {M : Type v} {I : Type z} [Finite I] {Q : I → Type q}

/-- All actual inverse images of the finite targets are retained. -/
def fullPreimage (π : ∀ i, M → Q i) (D : ∀ i, Finset (Q i)) : Set M :=
  {x | ∀ i, π i x ∈ D i}

theorem fullPreimage_finite (π : ∀ i, M → Q i) (K : Setoid M)
    (hK : ∀ x y, K x y ↔ ∀ i, π i x = π i y)
    (hfib : ∀ x, Finite {y // K x y}) (D : ∀ i, Finset (Q i)) :
    (fullPreimage π D).Finite := by
  apply finite_of_finite_joint_images π K hK hfib
  intro i
  apply (D i).finite_toSet.subset
  rintro q ⟨x,hx,rfl⟩
  exact hx i
end Pure

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

/-- A displayed finite full preimage is absolutely closed whenever ALL
of its finite quotient targets are absolutely closed. The arbitrary
common owner, if any, need not itself be closed or harmless. -/
theorem exact_fullPreimage_closed [Countable M] [DecidableEq M]
    (cco : SemanticCCO.{0,v,0,w} S) {I : Type z} [Finite I]
    (J : I → ColourEq S ()) (B : ∀ _ : I, NonemptyExact S () ())
    (hB : ∀ i, evaluate S (B i).words = (J i).val.r)
    (D : ∀ i, Finset (Quotient (J i).val)) (W : Finset M)
    (hW : ∀ x, x ∈ W ↔ ∀ i, (Quotient.mk'' x : Quotient (J i).val) ∈ D i) :
    letI : ∀ i, MulAction G (Quotient (J i).val) := fun i => originalQuotientAction S H (J i)
    letI : ∀ i, DecidableEq (Quotient (J i).val) := fun _ => Classical.decEq _
    (∀ i, Acl G (D i) = (D i : Set (Quotient (J i).val))) →
    Acl G W = (W : Set M) := by
  classical
  letI : ∀ i, MulAction G (Quotient (J i).val) := fun i => originalQuotientAction S H (J i)
  letI : ∀ i, DecidableEq (Quotient (J i).val) := fun _ => Classical.decEq _
  intro hD
  ext x
  constructor
  · intro hx
    apply (hW x).mpr
    intro i
    have hp := exact_projection_algebraic S H (J i) (B i) (hB i) cco W x hx
    have hsub : W.image (Quotient.mk'' : M → Quotient (J i).val) ⊆ D i := by
      intro q hq
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hq
      exact (hW a).mp ha i
    have hm := acl_mono hsub hp
    rw [hD i] at hm
    exact hm
  · exact parameter_mem_acl W

/-- Source C24/C25, with a nonempty actual intersection as in the
pinned theorem. The pure finiteness theorem above also covers emptiness. -/
theorem exact_closed_preimages [Countable M] [DecidableEq M]
    (cco : SemanticCCO.{0,v,0,w} S) {I : Type z} [Finite I]
    (J : I → ColourEq S ()) (B : ∀ _ : I, NonemptyExact S () ())
    (hB : ∀ i, evaluate S (B i).words = (J i).val.r)
    (hfib : ∀ x, Finite {y // jointKernel S J x y})
    (D : ∀ i, Finset (Quotient (J i).val))
    (hne : (fullPreimage (fun i => (Quotient.mk'' : M → Quotient (J i).val)) D).Nonempty) :
    letI : ∀ i, MulAction G (Quotient (J i).val) := fun i => originalQuotientAction S H (J i)
    letI : ∀ i, DecidableEq (Quotient (J i).val) := fun _ => Classical.decEq _
    (∀ i, Acl G (D i) = (D i : Set (Quotient (J i).val))) →
    ∃ W : Finset M, W.Nonempty ∧
      (∀ x, x ∈ W ↔ ∀ i, (Quotient.mk'' x : Quotient (J i).val) ∈ D i) ∧
      Acl G W = (W : Set M) := by
  classical
  letI : ∀ i, MulAction G (Quotient (J i).val) := fun i => originalQuotientAction S H (J i)
  letI : ∀ i, DecidableEq (Quotient (J i).val) := fun _ => Classical.decEq _
  intro hD
  let U := fullPreimage (fun i => (Quotient.mk'' : M → Quotient (J i).val)) D
  have hfin : U.Finite := fullPreimage_finite _ (jointKernel S J) (by
    intro x y
    change (∀ i, J i x y) ↔ ∀ i, (Quotient.mk'' x : Quotient (J i).val) = Quotient.mk'' y
    simp only [Quotient.eq]) hfib D
  let W := hfin.toFinset
  have hW (x : M) : x ∈ W ↔ ∀ i, (Quotient.mk'' x : Quotient (J i).val) ∈ D i :=
    hfin.mem_toFinset
  refine ⟨W,?_,hW,exact_fullPreimage_closed S H cco J B hB D W hW hD⟩
  obtain ⟨x,hx⟩ := hne
  exact ⟨x,(hW x).mpr hx⟩
end CCO.AclOwners
