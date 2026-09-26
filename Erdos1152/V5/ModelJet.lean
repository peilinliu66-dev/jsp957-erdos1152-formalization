import Erdos1152.ExternalField

namespace Erdos1152.V5

noncomputable def modelJet (j : Fin 3) (u : ℝ) : ℝ :=
  if j=0 then externalField u else if j=1 then Real.artanh u else 1/(1-u^2)

end Erdos1152.V5
