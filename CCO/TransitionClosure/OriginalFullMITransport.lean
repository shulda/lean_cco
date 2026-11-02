import CCO.TransitionClosure.OriginalTransportTargetFull
import CCO.QuotientTransport.Irreducible

/-!
# B049 source07 C35-C37: FULL original meet-irreducibility pullback

The accepted B040 upper-interval isomorphism acts on ALL invariant
equivalences under the actual original homogeneous group. The proved
old full-ColourEq / invariant-InvEq order isomorphism transports
the upper-interval source pullback back to one TRUE original FULL
colour-invariant equivalence H0, with J<=H0.

This module transfers proper meet-irreducibility, not merely
meet-irreducibility in an artificially restricted represented or
exact sublattice. No terminal NR2 or quotient SAP/CCO is used.
The selected further unique FULL cover, terminal represented
membership and named hidden-coordinate consumer remain separate.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open CCO.ParityHasse.Original
open CCO.QuotientTransport

/-- The exact source-side FULL original ColourEq pulled back from
a genuine target FULL L above F = Rᵒᵖ;J;R by the B040 interval
isomorphism. No independent quotient chart or represented-equivalence
hypothesis is introduced. -/
noncomputable def originalFullTransportPullColourEq
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (L : ColourEq S j)
    (hFL : originalTransportTargetColourEq S H J T ≤ L) :
    ColourEq S i :=
  (originalFullColourEqInvEqOrderIso S H).symm
    (T.pull (originalColourEqAsInvEq S H L)
      (fun y z hyz => hFL hyz))

/-- The pulled source FULL equivalence really lies above the
actual ORIGINAL J, as an inequality in the WHOLE old ColourEq
lattice, not in a restricted lattice of represented objects. -/
theorem originalFullTransportPullColourEq_source_le
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (L : ColourEq S j)
    (hFL : originalTransportTargetColourEq S H J T ≤ L) :
    J ≤ originalFullTransportPullColourEq S H J T L hFL := by
  intro x z hxz
  change (T.pull (originalColourEqAsInvEq S H L)
    (fun y z hyz => hFL hyz)) x z
  exact T.source_le_pull
    (originalColourEqAsInvEq S H L)
    (fun y z hyz => hFL hyz) hxz

/-- SOURCE C36 original FULL proper MI transport.
The original target L is a proper meet-irreducible in the
WHOLE ORIGINAL invariant-equivalence lattice iff its exact
FULL original source-side pullback H0 is also proper MI
in the WHOLE original invariant-equivalence lattice.

This consumes the actual B040 generic push_meetIrreducible and
push_pull equivalence, together with the already proved
SAME original ambient-G full lattice identification; it
assumes neither restricted-exact MI nor quotient SAP/CCO. -/
theorem originalFullTransportPullColourEq_properMI_iff
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i)
    {R : QuotientTransport.Rel (X i) (X j)}
    (T : Transport (originalColourEqAsInvEq S H J) R)
    (L : ColourEq S j)
    (hFL : originalTransportTargetColourEq S H J T ≤ L) :
    ProperMeetIrreducible (originalColourEqAsInvEq S H L) ↔
      ProperMeetIrreducible
        (originalColourEqAsInvEq S H
          (originalFullTransportPullColourEq S H J T L hFL)) := by
  let LV : InvEq G (X j) := originalColourEqAsInvEq S H L
  have hTL : T.target ≤ LV := by
    intro y z hyz
    exact hFL hyz
  let H0 : ColourEq S i :=
    originalFullTransportPullColourEq S H J T L hFL
  have hIso : originalColourEqAsInvEq S H H0 = T.pull LV hTL :=
    (originalFullColourEqInvEqOrderIso S H).apply_symm_apply (T.pull LV hTL)
  have hMI :=
    T.push_meetIrreducible (T.pull LV hTL) (T.source_le_pull LV hTL)
  rw [T.push_pull LV hTL] at hMI
  change ProperMeetIrreducible LV ↔
    ProperMeetIrreducible (originalColourEqAsInvEq S H H0)
  rw [hIso]
  exact hMI

end CCO.TransitionClosure
