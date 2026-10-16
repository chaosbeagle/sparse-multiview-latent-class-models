# Formal coverage and limitations

[English home](../README.md) · [繁體中文首頁](../README.zh-TW.md)

All paths below are relative to `lean/`. Original module/declaration identifiers
are preserved to keep the PDF and historical source hashes aligned.

| Article result | Source and representative declaration | Boundary |
|---|---|---|
| Observational fibers and synchronization | `Gen/Graph.lean`: `Gen.fiber_eq_compatible_image`, `Gen.identifies_iff_compatible_mod_gauge` | Local rigidity, weight-sensitive stabilizers and component gauges are hypotheses/objects of the encoded model |
| Kruskal specialization | `Gen/Kruskal.lean`, `Gen/KruskalConsequences.lean`: `GEN_G_KRUSKAL` | Same fixed number of positive latent terms; component identification does not itself identify scientific truth |
| Semantic criterion and obstruction | `Gen/KruskalConsequences.lean`: `GEN_G_SEMANTIC`; `Gen/NoSemantic.lean`: `GEN_G_NOSEM` | Fixed coarsening, surviving permutations and exact strict anchor assumptions |
| Diagonal fibers and sharp images | `Gen/Diagonal.lean`: `full_diagonal_fiber`, `full_anchored_images`, `full_anchored_sharp`; `Ext/Hidden.lean`: `GEN_F_STAR` | Fixed state count; sharp finite images are specific to the diagonal family |
| Conditioning and inverse bounds | `Gen/Jacobian.lean`, `Gen/Hessian.lean`, `Gen/ConditionedRates.lean`: `literal_local_inverse`, `literal_global_inverse` | Explicit margins, quotient locality and valid positive far separation |
| Exact real encoding | `Cover/ConcreteCompiler.lean`, `Cover/FullRealBridge.lean`: `coverEncoding_iff`, `concrete_coverEncoding_iff_fullDistance` | Encoded algebraic inputs and full real far-pair semantics |
| Certificate soundness | `Cover/A06Certificate.lean`: `Cover.A06.verifyCoverCertificate_sound` | Soundness for an accepted finite certificate does not assume successful generation |
| Eventual certified search | `Cover/A06Program.lean`, `Cover/A06Executable.lean`: `coverStage_eventually_succeeds`, `runCover_success_fully_checked` | Admitted conditioned inputs and the stated schedule; no optimal bound or practical runtime claim |
| Finite-fuel interface | `Cover/A06Capped.lean`: `runCoverCapped_success_separates` and dependent modules | Exact abstract transitions and replay; physical CPU/RAM and OS supervision excluded |
| Statistical rate and sufficient sample prescription | `Gen/ConditionedRates.lean`: `literal_rate_stat`, `literal_baseline_informative`; `Cover/A06Statistics.lean`: `conditioned_rate_stat_of_cover` | Fixed sampling/metadata and fit comparison; a sufficient prescription is not a minimax lower bound |
| Gold-direction and conditional-dependence robustness | `Ext/GoldBounds.lean`, `Ext/CountLaw.lean`, `Ext/Confidence.lean`, `Ext/ObservationBounds.lean` | Exact encoded model and sampling assumptions; original functional API states a finite-family interface |
| Boundary example | `Gen/FiniteControl.lean`: `full_real_K_has_eight`, `prescribed_count_exact` | Existing finite-control statements; the paper's one-observation interpretation is a conventional argument |

The article's explicit product-box certificate leaf-count lower bound, volume
derivation, rational far-pair sample-budget example, splitting/stabilizer worked
examples and bounded-differences refinement have conventional paper proofs or
exact Python checks. They are not additional Lean-verified theorems. The
simultaneous, possibly data-selected functional-readout consequence is a
pointwise paper argument broader than the existing finite-family formal API.

The exact least-squares baseline is an existence/selection result; it does not
supply an executable globally certified estimator. No new successful full-model
separation run, general sharp-image solver, numerical estimation study, clinical
utility or real-data validation is established by this release. Mathematical
termination and finite-fuel totality do not imply feasible wall time or memory.

The dated [verification receipt](../verification/VERIFICATION_RECEIPT.json)
records the 2026-10-09 build/audit; publication checks preserve its Lean inputs
byte for byte. Compilation does not replace the model assumptions or the paper
to formal statement correspondence.
