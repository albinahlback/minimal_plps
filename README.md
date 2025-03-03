# Computing point-line minimal problems

This code is supplementary material for the article

> PLMP -- Point-Line Minimal Problems for Projective SfM

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
`include("minimal_plps.jl")` to get all functionalities.

### Classes of balanced point-line problems

To compute all classes of balanced point-line problems, that is, all tuples
$(m, p^f, p^d, l^f, l^a)$

### Compute all candidate point-line minimal problems

TODO

### Compute all point-line minimal problems

TODO

### Compute degrees of all point-line minimal problems

TODO

## Running Example 4.12

To run Example 4.12 in the article, open Julia and run
```
include("example_4-12.jl")
```
