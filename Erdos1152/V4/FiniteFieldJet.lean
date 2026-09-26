import Erdos1152.V4.FiniteExternalField

namespace Erdos1152.V4

noncomputable def finiteFieldJet (j : Fin 3) (Y : Finset ℝ) (a h u : ℝ) : ℝ :=
  if j = 0 then finiteField Y a h u
  else if j = 1 then finiteFieldFirst Y a h u
  else finiteFieldSecond Y a h u

end Erdos1152.V4
