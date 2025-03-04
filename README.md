# Computing point-line minimal problems

This code is supplementary material for the article

> PLMP -- Point-Line Minimal Problems for Projective SfM

by Kim Lukas

## Prerequisites

We use [Julia](https://julialang.org/) for the computations.  If you intend to
read the source code, make sure that your editor is able to display UTF-8
characters as it will otherwise not be able to display all characters in the
file.

The required packages for running this software with Julia are:
- [AbstractAlgebra.jl](https://github.com/Nemocas/AbstractAlgebra.jl/),
- [Oscar.jl](https://github.com/oscar-system/Oscar.jl),
- [HomotopyContinuation.jl](https://github.com/JuliaHomotopyContinuation/HomotopyContinuation.jl)

## Running computations

All functions lie within `minimal_plps.jl`.  In Julia, run
```julia
include("minimal_plps.jl")
```
to get all functionalities.

### Classes of balanced point-line problems

To compute all classes of balanced point-line problems, that is, all tuples
$(m, p^f, p^d, l^f, l^a)$, run
```julia
calculate_balanced_classes()
```
The result is always computed during startup, and is stored in
`balanced_classes`.

### Candidates of point-line minimal problems

To compute all *candidates* of point-line minimal problems where
$p^f + p^d < 7$, run
```julia
calculate_candidate_problems()
```
The result is always computed during startup, and is stored in
`candidate_problems`.

All *candidates* of point-line minimal problems where $p^f + p^d = 7$ is stored
in `candidate_problems_7pts`, and is enumerated by hand.

### Point-line minimal problems

To check whether a problem `pb` is minimal, run
```julia
is_minimal(pb)
```
This runs a check of minimality by evaluating the generators of the polynomial
ring to random numbers, and then computing the determinant (as opposed to
symbolical, due to being computationally infeasible).  By default, this is done
1000 times.  To explicitly set the number of evaluations to `n` used in
`is_minimal`, run `is_minimal(pb, numevals=n)`.

All minimal problems for $p^f + p^d < 7$ and $p^f + p^d = 7$ are stored in
`minimal_problems` and `minimal_problems_7pts`, respectively.  To check that
these are correct, run
```julia
assert_minimal_problems_is_correct()
```
and
```julia
assert_minimal_problems_7pts_is_correct()
```
respectively.  These also accept an optional argument `numevals`, just like
`is_minimal`.

We also enumerate all candidates of minimal problems that turned out to be
non-minimal, and list the criteria that makes them non-minimal.  These are
listed in the variable `nonminimal_candidate_problems`, and the criteria are
listed in the comments in the code.

### Degrees of point-line minimal problems

#### Monodromy

All point-line minimal problems along with their degrees as given by monodromy
are given as tuples `(pb, deg)` in the variables `pb_degs` and `pb_degs_7pts`
for $p^f + p^d < 7$ and $p^f + p^d = 7$, respectively.  These are not
calculated during startup, so to assure that these are correct according to
monodromy, run
```julia
assert_degs_is_correct()
```
and
```julia
assert_degs_7pts_is_correct()
```

#### Gröbner basis

Recall that monodromy yields a lower bound for the degree.  To verify that this
lower bound is actually the degree, we calculate the degree using Gröbner basis
to get an upper bound of the degree, and verify that this is the same as the
lower bound.

To assert that the degrees for an array of problems `pbs` are correct, run
```julia
assert_degrees_are_correct_gb(pbs)
```
If no argument is given, `pbs` will default to all minimal point-line problems
with three views.

For modern mid-end computers, this is expected to terminate within an hour or
so for all problems with three to four views.  The most computationally heavy
problem in four views (the one in the class
$(m, p^f, p^d, l^f, l^a) = (4, 1, 0, 3, 6)$) is factorized into subproblems as
a special case in order to make it computationally feasible, and this code can
be found in the function `degree_m4_l9`, which corresponds to Example D.1 in
the article.

While it is expected to be able to verify some problems for higher views, the
memory consumption and run time grows very fast, in particular for higher line
counts.

## Running Example 4.12

To run Example 4.12 in the article, open Julia and run
```julia
include("example_4-12.jl")
```

## Running Example D.1

As mentioned under the section about Gröbner basis computations, Example D.1
corresponds to the function `degree_m4_l9`.  Hence, simply run
```julia
degree_m4_l9()
```
to get the degree of this problem.
