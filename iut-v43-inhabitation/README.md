# Admissible-prime and orbicurve inhabitation v4.3

This Lean 4.32 project focuses only on the two requested IUT initial-theta
inhabitation problems.

## Formalized progress

### Admissible prime

- uses the actual public `Iut.AdmissiblePrimeData` type;
- separates the genuine mod-`ℓ` representation/large-image core;
- generates the local Tate parameter from the public uniqueness theorem;
- assembles all fields into `Iut.AdmissiblePrimeData`;
- proves finite prime avoidance converts an eventual large-image theorem into
  pointwise inhabitation.

### Orbicurve

- uses the actual public `Iut.OrbicurveData` type;
- separates the geometric core/cover/cartesian-square data;
- constructs the nonzero rank-one quotient element canonically as the inverse
  image of `1 ∈ ZMod ℓ`;
- constructs the distinguished cusp by `cuspOfQuotient`;
- proves nonemptiness of `OrbicurveData` is equivalent to nonemptiness of the
  reduced geometric core/cover record;
- lifts a pointwise core theorem to `OrbicurveFamilyExists`.

## Exact remaining deep theorems

The package does **not** prove:

1. the eventual large-image theorem that constructs the genuine mod-`ℓ`
   representation with image containing `SL₂` and all local coprimality
   conditions;
2. the anabelian theorem constructing the `(1,ℓ-tors)^±` orbicurve with the
   required core and cartesian covering square.

The public `orbicurve-cores` repository is presently a skeleton, and no public
Lean formalization of Serre's open image theorem for these curves was found.
Therefore this package is a rigorous reduction/assembly package, not a proof of
inhabitation or of the abc conjecture.

## Build

```bash
lake update
lake exe cache get
lake build --wfail
```
