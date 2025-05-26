namespace SpectralProof

/--
A static index of core definitions and theorems used in the DAG-based proof.
Useful for CLI inspection (`lake run spectralProof`).
-/
def dagIndex : List (String × String) :=
  [ ("def:tracePower", "tracePower")
  , ("def:zetaDet", "zetaDet")
  , ("def:spectralMap", "spectralMap")
  , ("def:inverseSpectralMap", "inverseSpectralMap")
  , ("thm:canonical_det_identity", "canonical_det_identity")
  , ("thm:zero_maps_to_spectrum", "zero_maps_to_spectrum")
  , ("thm:trace_class_Lsym_pi", "trace_class_Lsym_pi")
  , ("thm:self_adjoint_Lsym_pi", "self_adjoint_Lsym_pi")
  , ("thm:GRH_iff_spec_real", "GRH_iff_spec_real")
  , ("thm:GRH_spectral_closure", "GRH_spectral_closure")
  ]

end SpectralProof
