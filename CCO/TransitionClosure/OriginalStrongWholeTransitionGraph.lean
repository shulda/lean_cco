import CCO.TransitionClosure.OriginalWholeTransitionCylinder

/-!
# B049 source07 C47: entire RAW transition graph as a STRONG old palette

The full equality-inclusive RAW J;R;K sandwich was already proved
to equal J;{a};K for ANY genuine original diversity atom a in R,
where K is the actual FULL transported target F=Rᵒᵖ;J;R.
Here original visible SAP and source J>Id, J<Top guarantee
that both old exterior kernels J,K are NONZERO. Old TSC for
each true fine atom then gives the COMPLETE source QT-Graph
strong palette identity

  (J;R;K)° = J° star (R° star K°).

R° is the literal old diversity atom menu of the full actual
invariant RAW relation R. Its real diagonal is NOT introduced
as an artificial STRONG identity factor. This theorem requires
a chosen actual diversity atom a⊆R (source QT-Graph assumes
identity-free nonempty R), and does NOT assert R={a} or
use quotient SAP, quotient CCO, terminal NR2 or word equality
between the many-atom R and a single old atomic word.

The complete graph's positive OLD presentation is handled
separately by the accepted source C48 consumer.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.QuotientTransport
open CCO.TerminalLattice

/-- Exact SOURCE07 C47, with REAL source typed original G-invariant
RAW relation R and its literal transported FULL target kernel K.

Any STRONG product witness chooses one genuine old diversity fine
atom b inside the WHOLE R palette. Source atom-to-whole transport
gives (J;{b};K)°=(J;R;K)°; original AgeSAP TSC gives the
corresponding J°*{b}*K°. The reverse direction uses one chosen
a∈R°. This covers all R diversity atoms without an invalid
claim that the union R is itself an atomic old typed word. -/
theorem original_full_transport_raw_guard_eq_strong_whole
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (J : ColourEq S i)
    (hJbot : (⊥ : ColourEq S i) < J)
    (hJtop : J < (⊤ : ColourEq S i))
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (a : S.Atom i j) (ha : a ∈ S.diversityGuard R) :
    S.diversityGuard (originalRawFullTypedSandwich S J
      (originalTransportTargetColourEq S H J T) R) =
      S.product (originalEquivDiversityPalette S J)
        (S.product (S.diversityGuard R)
          (originalEquivDiversityPalette S
            (originalTransportTargetColourEq S H J T))) := by
  let K : ColourEq S j := originalTransportTargetColourEq S H J T
  have hKbot : (⊥ : ColourEq S j) < K :=
    (originalTransportTargetColourEq_proper_nonzero
      S H sap J hJbot hJtop T).1
  apply Set.Subset.antisymm
  · intro c hc
    have hAtom : c ∈ S.product (originalEquivDiversityPalette S J)
        (S.product ({a} : S.Menu i j)
          (originalEquivDiversityPalette S K)) := by
      rw [← original_raw_typed_J_atom_K_guard_eq_strong
        S H sap J K hJbot hKbot a]
      rw [← original_raw_full_transport_guard_eq_atomic S H J T a ha]
      exact hc
    obtain ⟨p,hp,z,hz,htri⟩ := hAtom
    obtain ⟨b,hb,d,hd,htri'⟩ := hz
    have hbR : b ∈ S.diversityGuard R := by
      have hEq : b = a := Set.mem_singleton_iff.mp hb
      subst b
      exact ha
    exact ⟨p,hp,z,⟨b,hbR,d,hd,htri'⟩,htri⟩
  · intro c hc
    obtain ⟨p,hp,z,hz,htri⟩ := hc
    obtain ⟨b,hb,d,hd,htri'⟩ := hz
    have hAtom : c ∈ S.product (originalEquivDiversityPalette S J)
        (S.product ({b} : S.Menu i j)
          (originalEquivDiversityPalette S K)) :=
      ⟨p,hp,z,⟨b,by simp,d,hd,htri'⟩,htri⟩
    rw [← original_raw_typed_J_atom_K_guard_eq_strong
      S H sap J K hJbot hKbot b] at hAtom
    rw [← original_raw_full_transport_guard_eq_atomic S H J T b hb]
      at hAtom
    exact hAtom

/-- SOURCE07 QT-Graph at every MATCHED original quotient pair:
its complete old representative-cylinder spectrum is exactly
J° star (R° star K°) with the WHOLE literal old R palette.
A further terminal NR2 gate supplies ONE positive word for
this already proved full graph menu; no quotient SAP is used. -/
theorem original_matched_transport_cylinder_eq_strong_whole
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (J : ColourEq S i)
    (hJbot : (⊥ : ColourEq S i) < J)
    (hJtop : J < (⊤ : ColourEq S i))
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (a : S.Atom i j) (ha : a ∈ S.diversityGuard R)
    (q : Quotient J.val)
    (r : Quotient (originalTransportTargetColourEq S H J T).val)
    (hqr : T.quotientEquiv q = r) :
    originalTypedQuotientPairSpectrum S J
        (originalTransportTargetColourEq S H J T) q r =
      S.product (originalEquivDiversityPalette S J)
        (S.product (S.diversityGuard R)
          (originalEquivDiversityPalette S
            (originalTransportTargetColourEq S H J T))) := by
  calc
    originalTypedQuotientPairSpectrum S J
        (originalTransportTargetColourEq S H J T) q r =
      S.diversityGuard
        (originalRawTypedSandwich S J
          (originalTransportTargetColourEq S H J T) a) :=
      original_transport_matched_pair_spectrum_eq_raw
        S H J T a ha q r hqr
    _ = S.diversityGuard
        (originalRawFullTypedSandwich S J
          (originalTransportTargetColourEq S H J T) R) :=
      (original_raw_full_transport_guard_eq_atomic S H J T a ha).symm
    _ = _ := original_full_transport_raw_guard_eq_strong_whole
      S H sap J hJbot hJtop T a ha

end CCO.TransitionClosure
