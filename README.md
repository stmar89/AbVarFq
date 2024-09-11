# AbVarFq

Description
--

A Magma package to work with Abelian Varieties over finite fields.
The main functionalities are:
- compute unpolarized isomorphism classes of abelian varieties in isogeny classes which are ordinary or over finite fields (using Deligne modules);
- compute polarized isomorphism classes of abelian varieties in isogeny classes which are ordinary and whose Weil polynomial is squarefree (using Deligne modules);
- compute base field extensions and detect twists for ordinary abelian varieteis.

For the theory on which this code is based, see the `References` section at the bottom.

This package requires the package [`AlgEt`](https://github.com/stmar89/AlgEt).

There are two expansions to:
- compute polarizations not just in the ordinary case, but also over a prime field, when the Weil polynomial is squarefree: see [`PolsAbVarFpCanLift`](https://github.com/stmar89/PolsAbVarFpCanLift);
- compute unpolarized isomorphism classes with squarefree Weil polynomial (i.e. commutative endomorphism algebra) with no further assuptions: see [`IsomClassesAbVarFqComEnd`](https://github.com/stmar89/IsomClassesAbVarFqComEnd).
We refer to the documention in there for more details.

Warning for old users: in September 2024, there was a major update. All functionalities moved from the type AlgAss to the type AlgEt (faster,better,stronger). The old code is still here in the old_AlgAss folder and can be used attaching the correspoding spec file. The interface is very similar, so updating your code should be very easy. We invite you to do so, since the old code will not be maintained.

Please send comments and bug reports to `stefano.marseglia89@gmail.com`.

Details
--

For complete descriptions and more details we refer to the [`List of commands`](https://github.com/stmar89/AlgEt/blob/main/doc/ListOfCommandsAbVarFq.md).
To use them, use the magma command `AttachSpec("spec")`, after opening magma in the folder where you have downloaded the repo.

In the folder [`examples`](https://github.com/stmar89/AbVarFq/blob/main/examples), you will find files containing the code to reproduce the examples from the papers in the references below, which should be of help to get a quick start on the functionalities.

References
--

Stefano Marseglia,<br>
*Computing square-free polarized abelian varieties over finite fields*,<br>
Mathematics of Computation 90 (2021), no. 328, 953–971. [`DOI`](https://doi.org/10.1090/mcom/3594)

Stefano Marseglia,<br>
*Computing abelian varieties over finite fields isogenous to a power*,<br>
Res. number theory 5 (2019), no. 4, paper no. 35 [`DOI`](https://doi.org/10.1007/s40993-019-0174-x)

Stefano Marseglia,<br>
*Computing base extensions of ordinary abelian varieties over a finite field*,<br>
Int. J. Number Theory, Vol. 18, No. 09, pp. 1957-1974 (2022) [`DOI`](https://doi.org/10.1142/S1793042122501007)

Stefano Marseglia,<br>
*Modules over orders, conjugacy classes of integral matrices, and abelian varieties over finite fields*,<br>
to appear in the proceedings of the Sixteenth Algorithmic Number Theory Symposium

