# IUT actual public-type integration v3.0

This Lean 4.32 project imports the public `lana-agents/iut` Corollary 3.12 types.

## What is proved

- `ActualPilotWitness.lean`: an actual capsule-indexed admissible-region witness,
  with native q-volume and good-region monotonicity, proves the public
  `Iut.Corollary312Variant`.
- `GeneratedSource.lean`: builds the public `RHSData.thetaPilot` as the union of a
  concrete output type. Membership of every output, including a distinguished
  native output, is then definitional under a common finite-support theorem.
- `FullPolyGeneratedSource.lean`: Kummer conjugation removes a separate
  commuting-representative assumption, and the ordinary branch is a constructor
  of the generated output type. All regions, hulls, and volumes are the actual
  public IUT container types.

## What is not proved

The public repository explicitly does not define the full Hodge-theater,
Frobenioid, log-link, Kummer-correspondence, or multiradial-output types. It takes
`RHSData.thetaPilot`, `LogVolumeData`, and the hull system as input interfaces.
Consequently this project does not construct a closed `FullPolyGeneratedSource`
from the complete IUT I-III definitions.

There is no theorem `abc_conjecture : ABCConjecture` in this project. Adding one
would require:

1. a closed actual IUT III source instance;
2. a proved native q-pilot volume calibration in the public container;
3. a closed IUT IV height-theoretic reduction.

No `sorry`, `admit`, or user-declared `axiom` is intended in the source.
