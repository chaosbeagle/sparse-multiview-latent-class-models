# Exact separation and statistical examples

## Run

Requirements: Python 3.9 or later, using only the standard library.

```sh
python3 -I verify_examples.py
```

The program is independent of the working directory, needs no input archive or network connection, and writes no files. Run without `-O` or `-OO`; it explicitly rejects disabled assertions. Successful completion prints `All exact arithmetic checks passed.` and exits zero. `verified_output.txt` is the recorded output of the supplied script; `CHECK_RESULT.json` identifies that run and script.

## What is checked

1. Rational enclosures for square roots and pi, with pi obtained from Machin's identity and alternating-series bounds.
2. The six displayed binary-model volume and explicit-leaf lower scales, and the exact conservative conclusion of more than `2.9369e21` leaves at margins `(1/4, 1/sqrt(2))`.
3. A rational pair at margins `(1/5,1/5)`: normalization, positivity, all principal-minor tests for the binary Gram inequalities, and both common-label alignments beyond the prescribed local radius.
4. The exact identity `H = t^2/2048 + 5 t^4/256 + t^6/128`, with `t = 1/250000`, and `sqrt(H) < 9e-8`.
5. The resulting lower scale of the paper's prescribed per-edge sample count. A reciprocal-dyadic separation output implies a count of at least `5764607523034234880` for that prescription.
6. The boundary example's prescribed count `1812393`, eight parameters, four complementary-pair orbits, disjoint observation supports, and distance two between distinct orbits.

## Interpretation

All checks use `fractions.Fraction` or exact integers. Printed decimals are rounded displays of rational enclosures and must not be treated as outward-rounded decimal bounds unless an explicit rational assertion supports the displayed inequality. In particular, `2.9369e21` is checked exactly; `2.94e21` would only be a rounded scale.

The general volume theorem is a mathematical proof about the paper's explicit product-box tree format. The program checks its concrete numerical instantiations; it does not prove the general measure-theoretic statement. The theorem does not bound every compressed certificate, different coordinate system, quotient-domain checker, or search method.

The statistical numbers constrain the particular sufficient-sample prescription in the paper. They are not information-theoretic lower bounds on sample complexity. One observation already identifies the orbit in the noiseless boundary example, despite the much larger sufficient count given by the general prescription.

These calculations are outside the unchanged Lean formalization. They are not a Lean rebuild, numerical interval-cover search, certified global estimator, or empirical validation.

## Origin

`ORIGIN.json` identifies the original exact-arithmetic script and the limited adaptation used here. The formulas and original rational assertions are preserved; headings, variable naming, and the disabled-assertion guard make the script suitable for standalone mathematical reuse.
