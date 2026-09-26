import Erdos1152.V4.FiniteExternalField

noncomputable section
open Real Set
namespace Erdos1152.V5
open V4

def microCoordinate (s : ℕ) (x h y z : ℝ) : ℝ := (s:ℝ)*((z-x)/h-y)/2

def countingNodes (Y : Finset ℝ) (x h y : ℝ) (ρ : ℕ) : Finset ℝ :=
  let s := (insideNodes Y x h).card
  (insideNodes Y x h).filter (fun z => microCoordinate s x h y z∈Ico (-(ρ:ℝ)) ρ)

end Erdos1152.V5
