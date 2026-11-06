import WC.NormalizedFamily
import WC.AllParameterLower

/-! The full randomized oracle-complexity theorem of the manuscript.
Both concrete families, all parameter regimes, and the genuine Borel
upper algorithm have been proved in the imported modules. -/

namespace WC

theorem main : Model.MainTheorem :=
  BoundaryLower.mainTheorem_of_uniformFamilies normalizedChain_uniformFamilies

end WC
