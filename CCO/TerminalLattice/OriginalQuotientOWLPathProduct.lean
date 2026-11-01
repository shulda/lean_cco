import CCO.TerminalLattice.OriginalQuotientOWLPeriodicContradiction

/-!
# B050 source09 OWL: actual finite products of complete external old-G orbitals

The finite escape cycle's labels are literal COMPLETE orbitals for
the ORIGINAL ambient G-action on the true quotient M_a/J.
Their ordered nonempty quotient relation product is again invariant,
serial and contained in the original upper K/J equivalence. Outside
index two it ALWAYS contains an OFF-DIAGONAL quotient pair, even
when its intermediate products contain the true quotient diagonal.

These results discharge the real input to OWL-P without assuming that
a composite label-product is a complete orbital, positive OLD identity
letter, quotient reduct automorphism orbit, or diagonal-free state.
The next theorem must identify this product with the one occurring
in an actual periodic finite escape.
-/

universe u v w t z

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- Positive ordered product of the complete quotient orbitals
selected along a finite sequence of states. Index n means exactly
n+1 actual orbitals, so the quotient equality is NEVER inserted
as a synthetic positive factor. Invariance uses the original-G
quotient action proved internally. -/
noncomputable def original_OWL_external_path_state
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i)
    {E : Type z} (next : E → E)
    (label : E → OriginalExternalQuotientState S H J K) :
    E → Nat → OriginalInvariantQuotientState S H J
  | e, 0 => (label e).val
  | e, n+1 =>
      originalInvariantQuotientState_comp S H J (label e).val
        (original_OWL_external_path_state H J K next label (next e) n)

/-- Forgetting the invariance certificate leaves PRECISELY the
same actual quotient relation product as the generic labelled
finite-cycle lemma, with no order reversal or reindexing. -/
theorem original_OWL_external_path_state_val
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i)
    {E : Type z} (next : E → E)
    (label : E → OriginalExternalQuotientState S H J K)
    (e : E) (n : Nat) :
    (original_OWL_external_path_state
      S H J K next label e n).val =
      original_finite_labelled_product next
        (fun s => (label s).val.val) e n := by
  induction n generalizing e with
  | zero => rfl
  | succ n ih =>
      change RawSymmetric.compose (label e).val.val
          (original_OWL_external_path_state
            S H J K next label (next e) n).val =
        RawSymmetric.compose (label e).val.val
          (original_finite_labelled_product next
            (fun s => (label s).val.val) (next e) n)
      exact congrArg
        (RawSymmetric.compose (label e).val.val) (ih (next e))

/-- Every complete genuine original-G external quotient orbital
respects the TRUE upper equivalence K/J. -/
theorem original_OWL_external_state_inside_upper
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K)
    (C : OriginalExternalQuotientState S H J K) :
    ∀ q r : Quotient J.val, C.val.val q r →
      originalUpperSetoid S J K hJK q r := by
  obtain ⟨a,b,hKab,_,hEq⟩ := C.property
  intro q r hC
  rw [hEq] at hC
  exact originalQuotientOrbital_inside_originalUpper
    S H J K hJK a b hKab q r hC

/-- The path-product is SERIAL, including genuine quotient-diagonal
returns: it is a composition of nonempty COMPLETE old-G orbitals
and thus admits a successor at every actual J-class. -/
theorem original_OWL_external_path_state_serial
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i)
    {E : Type z} (next : E → E)
    (label : E → OriginalExternalQuotientState S H J K)
    (e : E) (n : Nat) :
    ∀ q : Quotient J.val, ∃ r : Quotient J.val,
      (original_OWL_external_path_state
        S H J K next label e n).val q r := by
  induction n generalizing e with
  | zero =>
      exact originalExternalQuotientState_serial
        S H J K (label e)
  | succ n ih =>
      change ∀ q : Quotient J.val, ∃ r : Quotient J.val,
        RawSymmetric.compose (label e).val.val
          (original_OWL_external_path_state
            S H J K next label (next e) n).val q r
      exact original_quotient_serial_comp
        (label e).val.val
        (original_OWL_external_path_state
          S H J K next label (next e) n).val
        (originalExternalQuotientState_serial S H J K (label e))
        (ih (next e))

/-- The whole ORIGINAL-G-invariant quotient path-product stays
inside K/J, by literal old K-transitivity and the true original
old-G orbital containment of each factor. -/
theorem original_OWL_external_path_state_inside_upper
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K)
    {E : Type z} (next : E → E)
    (label : E → OriginalExternalQuotientState S H J K)
    (e : E) (n : Nat) :
    ∀ q r : Quotient J.val,
      (original_OWL_external_path_state
        S H J K next label e n).val q r →
      originalUpperSetoid S J K hJK q r := by
  induction n generalizing e with
  | zero =>
      exact original_OWL_external_state_inside_upper
        S H J K hJK (label e)
  | succ n ih =>
      intro q r
      rintro ⟨mid,hC,hRest⟩
      exact (originalUpperSetoid S J K hJK).trans
        (original_OWL_external_state_inside_upper
          S H J K hJK (label e) q mid hC)
        (ih (next e) mid r hRest)

/-- SOURCE OWL no-return instantiated for one nonempty ACTUAL
product of original-G external quotient orbitals. In index!=2
every such finite product contains a genuinely OFF-DIAGONAL
quotient pair. The product MAY also contain quotient loops.

The one-factor base is the real external orbit root; for longer
paths the first complete external orbital cannot compose with
the SERIAL remainder into only the quotient diagonal, by the
already proved CCO-free original full-cover power theorem.
-/
theorem original_OWL_external_path_state_offdiagonal
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i) (hJK : J ⋖ K)
    (anchor : X i)
    (hNotTwo : relativeIndex J.val K.val anchor ≠ 2)
    {E : Type z} (next : E → E)
    (label : E → OriginalExternalQuotientState S H J K)
    (e : E) (n : Nat) :
    ∃ q r : Quotient J.val, q ≠ r ∧
      (original_OWL_external_path_state
        S H J K next label e n).val q r := by
  cases n with
  | zero =>
      obtain ⟨a,b,_,hNotJ,hEq⟩ := (label e).property
      refine ⟨Quotient.mk J.val a,Quotient.mk J.val b,?_,?_⟩
      · intro hEqual
        exact hNotJ (Quotient.exact hEqual)
      · change (label e).val.val
          (Quotient.mk J.val a) (Quotient.mk J.val b)
        rw [hEq]
        exact originalQuotientOrbital_root S (G := G) J a b
  | succ n =>
      obtain ⟨a,b,hKab,hNotJ,hEq⟩ := (label e).property
      have hRestSerial :=
        original_OWL_external_path_state_serial
          S H J K next label (next e) n
      obtain ⟨q,r,hNe,hComp⟩ :=
        original_external_orbital_serial_comp_has_offdiagonal
          S H J K hJK anchor hNotTwo a b hKab hNotJ
          (original_OWL_external_path_state
            S H J K next label (next e) n).val hRestSerial
      refine ⟨q,r,hNe,?_⟩
      change RawSymmetric.compose (label e).val.val
        (original_OWL_external_path_state
          S H J K next label (next e) n).val q r
      rw [hEq]
      exact hComp

end CCO.TerminalLattice
