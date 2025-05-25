import SpectralProof.CanonicalOperator
import SpectralProof.DeterminantIdentity
import SpectralProof.ZetaZeroEncoding
import SpectralProof.SpectralRigidity
import SpectralProof.SpectralClosure
import SpectralProof.AutomorphicLFunctions
import SpectralProof.HadamardExpansion

namespace SpectralProof

/--
Mapping of DAG node identifiers (from the formal proof architecture)
to Lean theorem or definition names. This enables semantic auditing,
coverage diagnostics, and dependency resolution.

Each entry maps a canonical DAG label (e.g., `"thm:truth_of_rh"`)
to its corresponding Lean declaration name.
-/
def dagIndex : List (String × Name) :=
  [ -- Determinant and spectral infrastructure
    ("def:tracePower",                        ``tracePower)
  , ("def:zetaDet",                           ``zetaDet)
  , ("thm:det_identity_revised",             ``determinant_identity)
  , ("lem:det_identity_entire_order_one",    ``determinant_identity)

    -- Spectral encoding
  , ("def:spectral_zero_map",                ``μ)
  , ("lem:fredholm_zero_spectral_map",       ``spectrum_eq_zeros)
  , ("thm:spectral_zero_bijection_revised",  ``zeta_zero_spectrum_bijection)
  , ("cor:spectrum_real_equiv_rh",           ``rh_iff_real_spectrum)

    -- Rigidity and uniqueness
  , ("lem:canonical_closure",                ``Lsym_determined)
  , ("lem:spectral_rigidity_determinant",    ``spectrum_rigidity)
  , ("thm:uniqueness_realization",           ``unitary_equiv_Lsym)
  , ("cor:canonical_operator_uniqueness",    ``unitary_equiv_Lsym)

    -- Final closure
  , ("thm:truth_of_rh",                      ``Riemann_Hypothesis_equiv_spectral_reality)
  , ("cor:dag_closure",                      ``Spectral_RH_Principle)

    -- Analytic structure
  , ("lem:hadamard_fredholm_multiplicity",   ``hadamard_expansion_Xi_via_spectrum)

    -- Automorphic L-function line
  , ("thm:automorphic_det_identity",         ``automorphic_det_identity)
  , ("cor:grh_iff_real_spectrum",            ``grh_iff_real_spectrum)
  , ("cor:canonical_operator_uniqueness",    ``L_sym_pi_canonical)
  ]

end SpectralProof
