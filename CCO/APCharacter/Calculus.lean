import CCO.APCharacter.Primality
import CCO.APCharacter.Paths

/-! The actual maximal source gate discharges BOTH algebraic mask providers.
The independent path/completion lemmas receive no stronger source premise. -/
universe u v w t
namespace CCO.APCharacter
open RigidGroupoid.Geometry
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}
namespace SourcePhase

def calculus (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S) :
    P.masks.Calculus where
  totality := P.fork_totality cco
  primality := P.phase_primality cco

end SourcePhase
end CCO.APCharacter
