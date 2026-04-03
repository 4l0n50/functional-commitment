# Function-Hiding Functional Commitment

This repository contains an experimental implementation of the function-hiding functional commitment construction described in the paper included as [`paper.pdf`](./paper.pdf).

The current code path uses:

- `ac_compiler` to compile arithmetic circuits into matrix form
- a modified `ark-marlin` to prove correct evaluation
- `pfr` to prove that the committed relation is functional

This repository contains experimental cryptographic code and should not be used in production.
