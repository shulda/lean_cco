import CCO.FinitePackets.Normalization.SquareKernel

/-! C25: absence of nonidentity finite-class FULL RAW exact kernels
forces every finite-packet atom to be thin. This implication has no
converse, and it needs no normalization history or quotient-source law. -/
universe v w t
namespace CCO.FinitePackets.Normalization
open CCO.RealHull.Geometry CCO.ParityHasse.Original CCO.FinitePackets.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

def NoFiniteExactKernel : Prop :=
  ∀ K : ColourEq S (), FiniteIndex S ⊥ K →
    ∀ B : RawExact.NonemptyExact S () (), RawExact.evaluate S B.words = K.val.r → K = ⊥

variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G)

include H

theorem terminal_finite_bottom_thin (hterm : NoFiniteExactKernel S)
    (F : ColourEq S ()) (hF : FiniteIndex S ⊥ F) : ThinBottom S F := by
  intro c hc
  cases c with
  | none => exact thin_none S
  | some a =>
    by_contra hnt
    have hn := squareKernel_nonidentity_of_nonthin S H F hc hnt
    have he := hterm (squareKernel S H F) (squareKernel_finite S H F hF)
      (squareKernelExact S H F) (squareKernelExact_represents S H F)
    exact (ne_of_gt hn) he

theorem terminal_greatest_finite_packet_thin (hterm : NoFiniteExactKernel S) :
    ThinBottom S (sigma S H ⊥) :=
  terminal_finite_bottom_thin S H hterm (sigma S H ⊥) (finiteIndex_sigma S H ⊥)

end CCO.FinitePackets.Normalization
