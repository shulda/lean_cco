import CCO.AclOwners.HarmlessOwners
import CCO.RawExact.FiniteRealignment

/-! The owner algebraicity API uses the FULL original colour automorphism
stabilizer, even when G is merely an arbitrary finite-homogeneity witness.
Finite realignment includes representatives of every named imaginary and
requires no exactness of its kernel or onto map of automorphism groups. -/

universe v w t z
namespace CCO.AclOwners
open RealClosure.Bounds ParityHasse.Original

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

/-- The actual full source automorphism orbit with individually fixed real
and imaginary parameters. -/
def fullOwnerOrbit {I : Type z} (A : Finset M) (K : I → ColourEq S ())
    (q : ∀ i, Quotient (K i).val) (x : M) : Set M :=
  {y | ∃ f : RawExact.OriginalAutomorphism S,
    (∀ a ∈ A, f.equiv () a = a) ∧
    (∀ i, (K i) (q i).out (f.equiv () (q i).out)) ∧ f.equiv () x = y}

def FullOwnerAcl {I : Type z} (A : Finset M) (K : I → ColourEq S ())
    (q : ∀ i, Quotient (K i).val) : Set M :=
  {x | (fullOwnerOrbit S A K q x).Finite}

/-- Full real acl, with no named imaginary parameters. -/
def FullRealAcl (A : Finset M) : Set M :=
  FullOwnerAcl S A (fun i : Fin 0 => Fin.elim0 i)
    (fun i : Fin 0 => Fin.elim0 i)

variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
include H

/-- The finite original witness group and the FULL original automorphism
group have identical point orbits over all finite displayed parameters. -/
theorem fullOwnerOrbit_eq {I : Type z} [Finite I] (A : Finset M)
    (K : I → ColourEq S ()) (q : ∀ i, Quotient (K i).val) (x : M) :
    fullOwnerOrbit S A K q x = ownerOrbit S (G := G) A K q x := by
  classical
  ext y
  constructor
  · rintro ⟨f,hA,hK,hx⟩
    let J := Option ↥A ⊕ I
    let pt : J → M := fun j => match j with
      | .inl none => x
      | .inl (some a) => a.val
      | .inr i => (q i).out
    obtain ⟨g,hg⟩ := RawExact.finite_original_realignment S H f (fun _ : J => ()) pt
    refine ⟨g,?_,?_,?_⟩
    · intro a ha
      exact (hg (.inl (some ⟨a,ha⟩))).trans (hA a ha)
    · intro i
      change (K i) (q i).out (g • (q i).out)
      rw [hg (.inr i)]
      exact hK i
    · exact (hg (.inl none)).trans hx
  · rintro ⟨g,hA,hK,hx⟩
    let e : M ≃ M := {
      toFun := fun x => g • x
      invFun := fun x => g⁻¹ • x
      left_inv := inv_smul_smul g
      right_inv := smul_inv_smul g }
    let f : RawExact.OriginalAutomorphism S := {
      equiv := fun _ => e
      preserves_colours := by
        intro i j a b
        cases i; cases j
        exact S.colourInvariant_of_homogeneous H g a b }
    exact ⟨f,hA,hK,hx⟩

theorem fullOwnerAcl_eq {I : Type z} [Finite I] (A : Finset M)
    (K : I → ColourEq S ()) (q : ∀ i, Quotient (K i).val) :
    FullOwnerAcl S A K q = OwnerAcl S (G := G) A K q := by
  ext x
  exact Iff.of_eq (congrArg Set.Finite (fullOwnerOrbit_eq S H A K q x))

theorem fullRealAcl_eq (A : Finset M) : FullRealAcl S A = Acl G A := by
  rw [FullRealAcl, fullOwnerAcl_eq S H]
  ext x
  change (ownerOrbit S (G := G) A (fun i : Fin 0 => Fin.elim0 i)
    (fun i : Fin 0 => Fin.elim0 i) x).Finite ↔ (orbitOver G A x).Finite
  have he : ownerOrbit S (G := G) A (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i) x = orbitOver G A x := by
    ext y
    constructor
    · rintro ⟨g,hg,_,hgy⟩
      exact ⟨g,hg,hgy⟩
    · rintro ⟨g,hg,hgy⟩
      exact ⟨g,hg,fun i => Fin.elim0 i,hgy⟩
  rw [he]

omit H in
/-- Harmlessness in literal FULL source automorphism semantics. -/
def FullHarmless (K : ColourEq S ()) : Prop :=
  ∀ (A : Finset M) (n : ℕ) (q : Fin n → Quotient K.val),
    FullOwnerAcl S A (fun _ : Fin n => K) q = FullRealAcl S A

variable [DecidableEq M] [sourceCountable : Countable M]
include sourceCountable

/-- Harmlessness iff ALL minimal infinite full invariant directions are
contained, stated entirely using FULL original automorphism stabilizers. -/
theorem full_harmless_iff_containsDirections (cco : SemanticCCO.{0,v,0,w} S)
    [Infinite M] (K : ColourEq S ()) : FullHarmless S K ↔ ContainsDirections S K := by
  have he : FullHarmless S K ↔ Harmless S (G := G) K := by
    constructor
    · intro h A n q
      simpa only [fullOwnerAcl_eq S H,fullRealAcl_eq S H] using h A n q
    · intro h A n q
      simpa only [fullOwnerAcl_eq S H,fullRealAcl_eq S H] using h A n q
  exact he.trans (harmless_iff_containsDirections S H cco K)

/-- The full-group mixed-sort conclusion retains arbitrary finite actual
owner collections and every finite real input base. -/
theorem full_mixed_harmless_owners (cco : SemanticCCO.{0,v,0,w} S)
    [Infinite M] {I : Type z} [Finite I] (K : I → ColourEq S ())
    (hK : ∀ i, ContainsDirections S (K i)) (q : ∀ i, Quotient (K i).val)
    (A : Finset M) : FullOwnerAcl S A K q = FullRealAcl S A := by
  rw [fullOwnerAcl_eq S H,fullRealAcl_eq S H]
  exact mixed_harmless_owners S H cco K hK q A

end CCO.AclOwners
