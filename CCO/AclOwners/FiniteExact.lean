import CCO.FinitePackets.Normalization.TerminalThin
import CCO.FinitePackets.Normalization.SquarePowers
import CCO.FinitePackets.Geometry.MinimalCutBasic
import CCO.RealClosure.Bounds.Singleton
import CCO.RawExact.ExactCalculusSource

/-! The normalized finite exact intersection argument.  The packet F is
the full finite-class invariant equivalence; it is never declared exact.
The stabilized equivalence is constructed from positive powers of the
actual nonempty exact relation. -/
universe v w t
namespace CCO.AclOwners
open ParityHasse.Original RealHull.Geometry RealHull.Canonical
open RealClosure.Bounds FinitePackets.Geometry FinitePackets.Normalization RawExact
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

def exactPower (D : NonemptyExact S () ()) : ℕ → NonemptyExact S () ()
  | 0 => exactIdentityAtom S ()
  | n+1 => convolutionExact S H D (exactPower D n)

theorem exactPower_relation (cco : SemanticCCO.{0,v,0,w} S)
    (D : NonemptyExact S () ()) (n : ℕ) :
    evaluate S (exactPower S H D n).words = relPow (evaluate S D.words) n := by
  induction n with
  | zero => exact exactIdentityAtom_relation S ()
  | succ n ih =>
    change evaluate S (convolutionExact S H D (exactPower S H D n)).words = _
    rw [convolutionExact_represents S H
      (heterogeneousExactBallHelly_of_CCO S H (semanticCCO_change_universe S cco)),ih]
    rfl

/-- A reflexive exact relation inside the finite packet collapses to
actual equality after finite-exact normalization. -/
theorem finite_reflexive_exact_eq_identity
    (cco : SemanticCCO.{0,v,0,w} S) (normalized : NoFiniteExactKernel S)
    (D : NonemptyExact S () ()) (hr : ∀ x, evaluate S D.words x x)
    (hF : ∀ x y, evaluate S D.words x y → finitePacket S H x y) :
    evaluate S D.words = Eq := by
  let R := evaluate S D.words
  have hc : ColourInvariant S () R := groupInvariant_colourInvariant S H
    (presentation_invariant_of_homogeneous S H D.words)
  let C := {R : M → M → Prop // ColourInvariant S () R}
  letI : Finite C := finite_colour_relations S
  let powers : ℕ →o C := {
    toFun := fun n => ⟨relPow R n,colourInvariant_relPow S H hc n⟩
    monotone' := relPow_mono_of_reflexive S H hr }
  obtain ⟨n₀,hn⟩ := WellFoundedGT.monotone_chain_condition powers
  let n := n₀+1
  have hstable (k : ℕ) (hk : n ≤ k) : relPow R n = relPow R k :=
    congrArg Subtype.val ((hn n (by omega)).symm.trans (hn k (by omega)))
  have hidem : RawSymmetric.compose (relPow R n) (relPow R n) = relPow R n :=
    (relPow_add R n n).symm.trans (hstable (n+n) (by omega)).symm
  let E : ColourEq S () := ⟨⟨relPow R n,⟨relPow_reflexive S H hr n,
    (fun {x y} h => colourInvariant_symmetric S (colourInvariant_relPow S H hc n) x y h),by
      intro x y z hxy hyz
      rw [← hidem]
      exact ⟨y,hxy,hyz⟩⟩⟩,colourInvariant_relPow S H hc n⟩
  have hEF : E ≤ finitePacket S H :=
    relPow_le_equivalence S H (finitePacket S H) hF n
  have he : E = ⊥ := normalized E
    ((finiteIndex_bottom_iff_finite_classes S E).mpr
      (finiteClasses_of_le S hEF (finitePacket_finite S H)))
    (exactPower S H D n) (exactPower_relation S H cco D n)
  funext x y
  apply propext
  constructor
  · intro hxy
    have hpow : E x y := relPow_mono_of_reflexive S H hr
      (show 1 ≤ n by omega) x y ⟨y,hxy,rfl⟩
    rwa [he] at hpow
  · rintro rfl
    exact hr x

def colourSquare (c : FullColour S) : M → M → Prop :=
  fun x z => ∃ y, col S x y = c ∧ col S y z = c

include H in
theorem colourSquare_reflexive (c : FullColour S) (x : M) : colourSquare S c x x := by
  obtain ⟨y,hy⟩ := colour_serial S H c x
  exact ⟨y,hy,(col_symm S y x).trans hy⟩

/-- C04, including the equality orbital as a harmless stronger boundary.
The E argument is an actual full exact EQUIVALENCE. -/
theorem finite_exact_intersection
    (cco : SemanticCCO.{0,v,0,w} S) (normalized : NoFiniteExactKernel S)
    (E : ColourEq S ()) (hE : ExactCRT.IsExactEq S (i := ()) E.val)
    (c : FullColour S)
    (hF : ∀ x y, E x y → colourSquare S c x y → finitePacket S H x y) :
    (fun x y => E x y ∧ colourSquare S c x y) = Eq := by
  obtain ⟨A,hA⟩ := optional_original_atom_exact S c
  let aa := convolutionExact S H A A
  have haa : evaluate S aa.words = colourSquare S c := by
    rw [convolutionExact_represents S H
      (heterogeneousExactBallHelly_of_CCO S H (semanticCCO_change_universe S cco)),hA]
    rfl
  obtain ⟨B,hB⟩ := hE
  obtain ⟨x⟩ := S.nonemptySort ()
  have hne : TRel.Nonempty (X := fun _ : Unit => M) (i := ()) (j := ())
      (fun (x y : M) => evaluate S B.words x y ∧ evaluate S aa.words x y) := by
    refine ⟨x,x,?_,?_⟩
    · simpa only [hB] using E.val.refl x
    · rw [haa]; exact colourSquare_reflexive S H c x
  let D := NonemptyExact.meet S B aa hne
  have hD : evaluate S D.words = (fun x y => E x y ∧ colourSquare S c x y) := by
    rw [NonemptyExact.meet_relation,hB,haa]
  rw [← hD]
  exact finite_reflexive_exact_eq_identity S H cco normalized D
    (by intro y; rw [hD]; exact ⟨E.val.refl y,colourSquare_reflexive S H c y⟩)
    (by intro y z h; rw [hD] at h; exact hF y z h.1 h.2)

end CCO.AclOwners
