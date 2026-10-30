import CCO.RigidGroupoid.Phase.RootPhase
import CCO.RigidGroupoid.Geometry.Transport
import CCO.ParityHasse.Relative.Source
import CCO.ParityHasse.Original.SourceHasse

/-! The actual reached maximal-character data.  Dominance quantifies over
ORIGINAL exact equivalences, before any marked age is constructed. -/
universe u v w t
namespace CCO.APCharacter
open RigidGroupoid.Geometry RigidGroupoid.Phase
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (C : ExactCalculus S)
variable {r : ι} (A : Kernel S r)

abbrev RootKernel := Reached.kernel H C (Reached.root A)
abbrev Character := letI := Reached.groupoid H C (A := A)
  Abstract.Character (Reached S A)

structure SourcePhase where
  odd : Arrow S (RootKernel S H C A) (RootKernel S H C A)
  odd_nonidentity : odd ≠ Arrow.id _
  odd_dominant : Dominant (RootKernel S H C A) odd
  character : Character S H C A
  detects : letI := Reached.groupoid H C (A := A); character.value odd = 1

variable {S H C A}
namespace SourcePhase
variable (P : SourcePhase S H C A)

def atSort (b : Reached S A) : Arrow S (Reached.kernel H C b) (Reached.kernel H C b) :=
  transport C P.odd (Reached.connectingArrow H C (Reached.root A) b)

theorem atSort_nonidentity (b : Reached S A) : P.atSort b ≠ Arrow.id _ :=
  transport_nonidentity C P.odd_nonidentity _

theorem atSort_dominant (b : Reached S A) : Dominant (Reached.kernel H C b) (P.atSort b) :=
  transport_dominant C P.odd P.odd_dominant _

set_option backward.isDefEq.respectTransparency.types false in
theorem atSort_detects (b : Reached S A) :
    letI := Reached.groupoid H C (A := A)
    P.character.value (P.atSort b) = 1 := by
  letI := Reached.groupoid H C (A := A)
  let R := Reached.connectingArrow H C (Reached.root A) b
  change P.character.value (R.inv.comp C (P.odd.comp C R)) = 1
  have hi : P.character.value R.inv + P.character.value R = 0 := by
    rw [← P.character.map_comp]
    change P.character.value (R.inv.comp C R) = 0
    rw [Arrow.inv_comp]
    exact P.character.map_id b
  have hc : P.character.value (R.inv.comp C (P.odd.comp C R)) =
      P.character.value R.inv + (P.character.value P.odd + P.character.value R) := by
    exact (P.character.map_comp R.inv (P.odd.comp C R)).trans
      (congrArg (fun a => P.character.value R.inv + a) (P.character.map_comp P.odd R))
  rw [hc,P.detects]
  calc
    P.character.value R.inv + (1 + P.character.value R) =
        (P.character.value R.inv + P.character.value R) + 1 := by abel
    _ = 1 := by rw [hi,zero_add]


/-- The actual maximal old gate supplies the character, rather than a
hypothetical mask, marked CCO, or quotient homogeneity premise. -/
theorem exists_of_odd (odd : Arrow S (RootKernel S H C A) (RootKernel S H C A))
    (hne : odd ≠ Arrow.id _) (hd : Dominant (RootKernel S H C A) odd) :
    Nonempty (SourcePhase S H C A) := by
  obtain ⟨χ,hχ,_⟩ := actual_source_character S H C A (Reached.root A) odd hne
  exact ⟨⟨odd,hne,hd,χ,hχ⟩⟩

end SourcePhase
end
end CCO.APCharacter
