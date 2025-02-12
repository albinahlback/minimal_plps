#=  minimal_plps.jl:  Computions of point-line minimal problems
    Copyright (C) 2025  Albin Ahlbäck

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
=#

import Base:
    show, ==
import LinearAlgebra:
    norm
import AbstractAlgebra.Generic:
    FracField, FracFieldElem,
    MatSpace, MatSpaceElem
import AbstractAlgebra:
    matrix_space, polynomial_ring, fraction_field, residue_ring,
    elem_type, base_ring,
    one, zero,
    is_one, is_zero,
    derivative,
    ncols, nrows,
    number_of_variables,
    lcm, is_invertible,
    coefficients, exponent_vectors
import Oscar:
    Partition,
    ZZ,
    MPolyRingElem, RingElem,
    Ring
import Oscar:
    partitions, evaluate, det, denominator, numerator, is_prime
import HomotopyContinuation: @var, System, solve, solutions, monodromy_solve,
                             nsolutions, verify_solution_completeness
import HomotopyContinuation.ModelKit: Variable, Expression

###############################################################################
###############################################################################
# computing candidate problems where p < 7
###############################################################################
###############################################################################

###############################################################################
# computing classes of point-line balanced problems for less than seven points
###############################################################################

dim_camera_space(m::Int) = 11 * m - 15

dim_point_line_space(pf::Int, pd::Int, lf::Int, la::Int) =
    3 * pf + pd + 4 * lf + 2 * la

dim_image_space(pf::Int, pd::Int, lf::Int, la::Int) =
    2 * pf + pd + 2 * lf + la

function is_balanced(m::Int, pf::Int, pd::Int, lf::Int, la::Int)
    dim_camera_space(m) + dim_point_line_space(pf, pd, lf, la) ==
        m * dim_image_space(pf, pd, lf, la)
end

struct Class
    m::Int
    pf::Int
    pd::Int
    lf::Int
    la::Int

    function Class(m::Int, pf::Int, pd::Int, lf::Int, la::Int)
        @assert is_balanced(m, pf, pd, lf, la)
        return new(m, pf, pd, lf, la)
    end
end

_m(cl::Class) = cl.m
_pf(cl::Class) = cl.pf
_pd(cl::Class) = cl.pd
_lf(cl::Class) = cl.lf
_la(cl::Class) = cl.la

function show(io::IO, cl::Class)
    m = _m(cl)
    pf = _pf(cl)
    pd = _pd(cl)
    lf = _lf(cl)
    la = _la(cl)

    print(io, "Class (m, pf, pd, lf, la) = ($m, $pf, $pd, $lf, $la)")
end

finite_views = [m for m in 3:9]

# All possible point configuration on the form (pf, pd).  Taken from Albin's
# thesis.
possible_point_configurations =
    [(0, 0);
     (1, 0);
     (2, 0);
     (3, 0); (2, 1);
     (4, 0); (3, 1); (2, 2);
     (5, 0); (4, 1); (3, 2); (2, 3);
     (6, 0); (5, 1); (4, 2); (3, 3); (2, 4);
     (7, 0); (6, 1); (5, 2); (4, 3); (3, 4); (2, 5);
                                                     (2, 6)]

# Given (m, pf, pd), append all classes of balanced point-line problems to
# list.
function append_classes!(list::Vector{Class}, m::Int, pf::Int, pd::Int)
    # We rewrite the balancedness as g = h.
    g(m::Int, pf::Int, pd::Int) = (11 - 2 * pf - pd) * m - (15 - 3 * pf - pd)
    h(m::Int, lf::Int, la::Int) = (m - 2) * (2 * lf + la)

    val = g(m, pf, pd)

    # We have that any solution fulfills g(x) = h(x).  As h(x) ≥ 0, we must
    # have g(x) ≥ 0.
    if val < 0
        return
    end

    # As g(x) = (m - 2) (2 lf + la), g(x) must be divisible by (m - 2).
    if (val % (m - 2)) != 0
        return
    end

    # If (pf, pd) = (0, 0), then la = 0.  Treat this as a special case.
    if pf == 0 && pd == 0
        lf = val ÷ (2 * (m - 2))
        la = 0

        if h(m, lf, la) == val
            push!(list, Class(m, pf, pd, lf, la))
        end

        return
    end

    # Set lx to the largest value satifying h(m, 0, lx) ≤ g(m, pf, pd).
    lx = val ÷ (m - 2)

    lf = 0
    la = lx
    while la >= 0
        push!(list, Class(m, pf, pd, lf, la))
        la -= 2
        lf += 1
    end
end

# Returns a list of all classes of balanced point-line problems.
function calculate_balanced_classes()
    list = Class[]
    for m in finite_views
        for p in possible_point_configurations
            pf = p[1]
            pd = p[2]
            append_classes!(list, m, pf, pd)
        end
    end
    return list
end

balanced_classes = calculate_balanced_classes()

# Applying filter(x -> (_pf(x) + _pd(x) < 7), balanced_classes) results in the
# 123 classes of balanced problems as claimed at the end of the proof of
# Lemma 3.3; compare Table 2

# We know that problems containing four points on a line or six points on a
# plane cannot be minimal.  Hence, remove classes that only contain such
# problems.
feasible_balanced_classes = filter(
    x -> !((_pf(x) ≤ 2 && _pd(x) ≥ 2) || (_pf(x) ≤ 3 && _pd(x) ≥ 3)),
    balanced_classes)

# In this part we only care about problems with less than seven points.
interesting_balanced_classes = filter(
    x -> (_pf(x) + _pd(x) < 7), feasible_balanced_classes)

###############################################################################
# problem types typedef
###############################################################################

# TYPES
#
# We have a couple of different types of candidate problems. These are the
# following:
#
# 1. No dependent points, represented as type 1.
#
# 2. One dependent point, represented as type 1 via a dependent point between
#    the first and second free point.
#
# 3. Two dependent points, represented as either type 1 or type 2.
#
#    - Type 1 has one dependent point between the first and second free point,
#      and one between the first and third free point.
#
#    - Type 2 has one dependent point between the first and second free point,
#      and one between the third and fourth free point.

# GROUPING
#
# In order to distribute the adjacent lines into non-equivalent problems, we
# group the points together.  Within these groups, we partition the assigned
# adjacent lines.

# We will assume that pd ≤ 2
@assert maximum(x -> _pd(x), interesting_balanced_classes) ≤ 2

is_canonical_pd0(x1::Int) = true
is_canonical_pd1(x1::Int, x2::Int) = true
is_canonical_pd2_1(x1::Int, x2::Int, x3::Int, args...) = (x2 >= x3)
is_canonical_pd2_2(x1::Int, x2::Int, args...) = (x1 >= x2)

struct ProblemType
    cl::Class
    deps::Vector{Tuple{Int, Int}}
    numgrps::Int
    grps::Vector{Vector{Int}}
    is_canonical::Function

    function ProblemType(m::Int, pf::Int, pd::Int, lf::Int, la::Int, type::Int)
        if m < 2 || pf < 0 || pd < 0 || lf < 0 || la < 0 ||
            (pf < 2 && pd > 0) || (pf == 0 && la > 0)
            error()
        end

        cl = Class(m, pf, pd, lf, la)

        if type == 1 && pd == 0
            # No dependent points
            deps = Vector{Int}[]
            grps = [collect(1:pf)]
            numgrps = 1
            is_canonical = is_canonical_pd0
        elseif type == 1 && pd == 1
            # Line
            deps = [(1, 2)]
            grps = [[1, 2, pf + 1]]
            numgrps = 1
            if pf >= 3
                append!(grps, [collect(3:pf)])
                numgrps += 1
            end
            is_canonical = is_canonical_pd1
        elseif type == 1 && pd == 2
            # Half path
            deps = [(1, 2), (1, 3)]
            grps = [[1], [2, pf + 1], [3, pf + 2]]
            numgrps = 3
            if pf >= 4
                append!(grps, [collect(4:pf)])
                numgrps += 1
            end
            is_canonical = is_canonical_pd2_1
        elseif type == 2 && pd == 2
            # Two lines
            deps = [(1, 2), (3, 4)]
            grps = [[1, 2, pf + 1], [3, 4, pf + 2]]
            numgrps = 2
            if pf >= 5
                append!(grps, [collect(5:pf)])
                numgrps += 1
            end
            is_canonical = is_canonical_pd2_2
        else
            error()
        end

        return new(cl, deps, numgrps, grps, is_canonical)
    end

    function ProblemType(cl::Class, type::Int)
        return ProblemType(cl.m, cl.pf, cl.pd, cl.lf, cl.la, type)
    end
end

_m(pt::ProblemType) = _m(pt.cl)
_pf(pt::ProblemType) = _pf(pt.cl)
_pd(pt::ProblemType) = _pd(pt.cl)
_lf(pt::ProblemType) = _lf(pt.cl)
_la(pt::ProblemType) = _la(pt.cl)

function show(io::IO, px::ProblemType)
    m = _m(px)
    pf = _pf(px)
    pd = _pd(px)
    lf = _lf(px)
    la = _la(px)

    print(io, "Problem type of class (m, pf, pd, lf, la) = ($m, $pf, $pd, $lf, $la)\n")

    if pd == 1
        print(io, "with dependent point $(px.deps[1])")
    elseif pd == 2
        print(io, "with dependent points $(px.deps[1]) and $(px.deps[2])")
    end
end

###############################################################################
# problem typedefs
###############################################################################

# POINT ENUMERATION
#
# We enumerate points as
#
#   x_{1}, ..., x_{pf}, d_{1}, ..., d_{pd}.
#
# That is, in the list of points, the m-th free point will be at index m in the
# list of points, while the n-th dependent point will be at index pf + n.

# Get all problems from problem type
# Use partitions from Oscar to get all problems
struct Problem
    cl::Class
    deps::Vector{Tuple{Int, Int}}
    adjs::Vector{Int} # Number of adjacent points at each point index

    function Problem(pt::ProblemType, adjs::Vector{Int})
        return new(pt.cl, pt.deps, adjs)
    end

    function Problem(cl::Class, deps::Vector{Tuple{Int, Int}}, adjs::Vector{Int})
        return new(cl, deps, adjs)
    end
end

==(a::Problem, b::Problem) = (a.adjs == b.adjs && a.cl == b.cl && a.deps == b.deps)

_m(pb::Problem) = _m(pb.cl)
_pf(pb::Problem) = _pf(pb.cl)
_pd(pb::Problem) = _pd(pb.cl)
_lf(pb::Problem) = _lf(pb.cl)
_la(pb::Problem) = _la(pb.cl)

function show(io::IO, px::Problem)
    m = _m(px)
    pf = _pf(px)
    pd = _pd(px)
    lf = _lf(px)
    la = _la(px)

    print(io, "Problem of class (m, pf, pd, lf, la) = ($m, $pf, $pd, $lf, $la)")

    if pd == 1
        print(io, "\nwith dependent point $(px.deps[1])")
    elseif pd == 2
        print(io, "\nwith dependent points $(px.deps[1]) and $(px.deps[2])")
    end

    if la > 0
        print(io, ",\nand with adjacent lines on $(px.adjs)")
    end
end

###############################################################################
# compute all problems from problem types from classes
###############################################################################

# Partition `m` into at most `n` parts.
function collect_partitions(m::Int, n::Int)
    res = Partition{Int}[]

    if m == 0
        rx = collect(partitions(1, 1))
        rx[1][1] = 0
        append!(res, rx)
    else
        for ix in 1:n
            rx = collect(partitions(m, ix))
            append!(res, rx)
        end
    end

    return res
end

function problems(pt::ProblemType)
    numpts = _pf(pt) + _pd(pt)
    la = _la(pt)
    numgrps = pt.numgrps
    grps = pt.grps
    is_canonical = pt.is_canonical
    pbs = Problem[]

    # Trivial case. Also handles the case with no points.
    if la == 0
        push!(pbs, Problem(pt, zeros(Int, numpts)))
        return pbs
    end

    if numgrps == 1
        # Simple partition, i.e. partition `la` in at most `pf + pd` parts.
        # No need to check is_canonical function.
        parts = collect_partitions(la, numpts)
        for part in parts
            adjs = zeros(Int, numpts)
            for nx in 1:length(part)
                adjs[nx] = part[nx]
            end
            push!(pbs, Problem(pt, adjs))
        end
    elseif numgrps == 2
        # Assign ix adjacent lines to first group, and jx adjacent lines to
        # second group, with ix + jx = la.
        for ix in 0:la, jx in (la - ix):(la - ix)
            if !is_canonical(ix, jx)
                continue
            end

            p1 = collect_partitions(ix, length(grps[1]))
            p2 = collect_partitions(jx, length(grps[2]))

            for px1 in p1, px2 in p2
                adjs = zeros(Int, numpts)

                # Set adjacent lines for first group
                for nx in 1:length(px1)
                    adjs[grps[1][nx]] = px1[nx]
                end

                # Set adjacent lines for second group
                for nx in 1:length(px2)
                    adjs[grps[2][nx]] = px2[nx]
                end

                push!(pbs, Problem(pt, adjs))
            end
        end
    elseif numgrps == 3
        # ix + jx + kx = la
        # ix ≥ 0, jx ≥ 0, kx ≥ 0
        for ix in 0:la, jx in 0:(la - ix), kx in (la - ix - jx):(la - ix - jx)
            if !is_canonical(ix, jx, kx)
                continue
            end

            p1 = collect_partitions(ix, length(grps[1]))
            p2 = collect_partitions(jx, length(grps[2]))
            p3 = collect_partitions(kx, length(grps[3]))

            for px1 in p1, px2 in p2, px3 in p3
                adjs = zeros(Int, numpts)

                for nx in 1:length(px1)
                    adjs[grps[1][nx]] = px1[nx]
                end

                for nx in 1:length(px2)
                    adjs[grps[2][nx]] = px2[nx]
                end

                for nx in 1:length(px3)
                    adjs[grps[3][nx]] = px3[nx]
                end

                push!(pbs, Problem(pt, adjs))
            end
        end
    elseif numgrps == 4
        # ix + jx + kx + lx = la
        # ix ≥ 0, jx ≥ 0, kx ≥ 0, lx ≥ 0
        for ix in 0:la, jx in 0:(la - ix), kx in 0:(la - ix - jx), lx in (la - ix - jx - kx):(la - ix - jx - kx)
            if !is_canonical(ix, jx, kx, lx)
                continue
            end

            p1 = collect_partitions(ix, length(grps[1]))
            p2 = collect_partitions(jx, length(grps[2]))
            p3 = collect_partitions(kx, length(grps[3]))
            p4 = collect_partitions(lx, length(grps[4]))

            for px1 in p1, px2 in p2, px3 in p3, px4 in p4
                adjs = zeros(Int, numpts)

                for nx in 1:length(px1)
                    adjs[grps[1][nx]] = px1[nx]
                end

                for nx in 1:length(px2)
                    adjs[grps[2][nx]] = px2[nx]
                end

                for nx in 1:length(px3)
                    adjs[grps[3][nx]] = px3[nx]
                end

                for nx in 1:length(px4)
                    adjs[grps[4][nx]] = px4[nx]
                end

                push!(pbs, Problem(pt, adjs))
            end
        end
    else
        error()
    end

    return pbs
end

function number_of_types(pf::Int, pd::Int)
    if pf < 0 || pd < 0 || (pd > 0 && pf < 2)
        error()
    elseif pd < 2
        return 1
    elseif pf == 3 && pd == 2
        return 1
    elseif pf >= 4 && pd == 2
        return 2
    else
        error()
    end
end

function problems(cl::Class)
    numtypes = number_of_types(cl.pf, cl.pd)
    pts = [ProblemType(cl, tx) for tx in 1:numtypes]
    pbs = Problem[]
    for pt in pts
        append!(pbs, problems(pt))
    end
    return pbs
end

candidate_problems = Problem[]

for cl in interesting_balanced_classes
    append!(candidate_problems, problems(cl))
end

# FIXUP: For (pf, pd) = (3, 2), we have one symmetry more which we haven't
# accounted for in the V shaped problem, as noted by Kim, which appear when the
# ends has the same number of adjacent lines prescribed to them.
#
# Note, however, that this is the only case that this appears.  Similar things
# could happen for other shapes, but they "cannot afford" enough adjacent lines
# for this to become an issue.
function fixup_filter(pb::Problem)
    cl = pb.cl
    adjs = pb.adjs
    pf, pd = _pf(cl), _pd(cl)

    if (pf, pd) != (3, 2)
        return true
    end

    # Adjacent lines on the form (mid, l1, r1, l2, r2)
    l1, r1, l2, r2 = adjs[2:5]
    lnum = l1 + l2
    rnum = r1 + r2

    if lnum != rnum
        return true
    end

    return l1 >= r1
end

candidate_problems = filter(fixup_filter, candidate_problems)

# this turn the 124 classes from Table 2 into 434 balanced problems 
# that are candidates for being minimal, as claimed in the proof of the 
# main Theorem 2.3 c) 
# Note: these candidates do not contain problems violating homography Lemma 4.1

###############################################################################
###############################################################################
# computing minimality of candidate problems where p < 7
###############################################################################
###############################################################################

###############################################################################
# symbolic representation of camera configuration and point-line variety
###############################################################################

num_vars_cms(cl::Class) = 11 * _m(cl) - 15
num_vars_pfs(cl::Class) = 3 * _pf(cl)
num_vars_pds(cl::Class) = _pd(cl)
num_vars_lfs(cl::Class) = 4 * _lf(cl)
num_vars_las(cl::Class) = 2 * _la(cl)

num_vars(cl::Class) = num_vars_cms(cl) + num_vars_pfs(cl) + num_vars_pds(cl) +
                        num_vars_lfs(cl) + num_vars_las(cl)

function polynomial_ring(cl::Class, R::S) where {S <: Ring}
    syms = Symbol[]

    for ix in 1:num_vars_cms(cl)
        push!(syms, Symbol("c$ix"))
    end
    for ix in 1:num_vars_pfs(cl)
        push!(syms, Symbol("x$ix"))
    end
    for ix in 1:num_vars_pds(cl)
        push!(syms, Symbol("d$ix"))
    end
    for ix in 1:num_vars_lfs(cl)
        push!(syms, Symbol("l$ix"))
    end
    for ix in 1:num_vars_las(cl)
        push!(syms, Symbol("a$ix"))
    end

    return polynomial_ring(R, syms)
end

# C_{m} × X_{p, l, I}
struct CXElem{S <: RingElem, T <: MPolyRingElem{S}}
    pb::Problem
    cms::Vector{MatSpaceElem{T}}
    pfs::Vector{MatSpaceElem{T}}
    pds::Vector{MatSpaceElem{T}}
    lfs::Vector{MatSpaceElem{T}}
    las::Vector{MatSpaceElem{T}}

    # Here R is a base ring, such as integers or finite field
    function CXElem(pb::Problem, R::V) where {V <: Ring}
        m, pf, pd, lf, la = _m(pb), _pf(pb), _pd(pb), _lf(pb), _la(pb)
        deps = pb.deps
        adjs = pb.adjs

        U, gens = polynomial_ring(pb.cl, R)
        z0, o1 = zero(U), one(U)
        C = matrix_space(U, 3, 4) # camera space
        P = matrix_space(U, 4, 1) # point space
        L = matrix_space(U, 4, 2) # line space
        cms = Vector{MatSpaceElem{elem_type(U)}}(undef, m)
        pfs = Vector{MatSpaceElem{elem_type(U)}}(undef, pf)
        pds = Vector{MatSpaceElem{elem_type(U)}}(undef, pd)
        lfs = Vector{MatSpaceElem{elem_type(U)}}(undef, lf)
        las = Vector{MatSpaceElem{elem_type(U)}}(undef, la)

        # First camera on the form (1 0 0 0; 0 1 0 0; 0 0 1 0)
        c1 = zero(C)
        for ix in 1:3
            c1[ix, ix] = o1
        end
        cms[1] = c1

        # Second camera on the form (0 0 0 1; 1 * * *; * * * *)
        c2 = zero(C)
        c2[1, 4] = o1
        c2[2, 1] = o1
        c2[2, 2:4] = gens[1:3]
        c2[3, 1:4] = gens[4:7]
        cms[2] = c2

        new_gens = gens[8:end]

        # All other cameras on the form (1 * * *; * * * *; * * * *)
        for ix in 0:(m - 3)
            cx = zero(C)
            cx[1, 1] = o1
            cx[1, 2:4] = new_gens[(1 + 11 * ix):(3 + 11 * ix)]
            cx[2, 1:4] = new_gens[(4 + 11 * ix):(7 + 11 * ix)]
            cx[3, 1:4] = new_gens[(8 + 11 * ix):(11 + 11 * ix)]
            cms[ix + 3] = cx
        end

        new_gens = new_gens[(1 + 11 * (m - 2)):end]

        # Free points on the form (*; *; *; 1)
        for ix in 0:(pf - 1)
            px = zero(P)
            px[1:3, 1] = new_gens[(1 + 3 * ix):(3 + 3 * ix)]
            px[4, 1] = o1
            pfs[ix + 1] = px
        end

        new_gens = new_gens[(1 + 3 * pf):end]

        # Dependent points on the form t * p0 + (1 - t) * p1 where t is the
        # variable for the dependent point
        for ix in 1:pd
            t = new_gens[ix]
            px = t * pfs[deps[ix][1]] + (o1 - t) * pfs[deps[ix][2]]
            pds[ix] = px
        end

        new_gens = new_gens[(1 + pd):end]

        # Free lines on the form (* *; * *; 1 0; 0 1)
        for ix in 0:(lf - 1)
            lx = zero(L)
            lx[1, 1:2] = new_gens[(1 + 4 * ix):(2 + 4 * ix)]
            lx[2, 1:2] = new_gens[(3 + 4 * ix):(4 + 4 * ix)]
            lx[3, 1] = o1
            lx[4, 2] = o1
            lfs[ix + 1] = lx
        end

        new_gens = new_gens[(1 + 4 * lf):end]

        new_adjs = deepcopy(adjs)

        jx = 1
        # Adjacent lines on the form (* x1; * x2; 1 x3; 0 x4), where x is the
        # point that the line is adjacent to
        for ix in 0:(la - 1)
            lx = zero(L)
            lx[1:2, 1] = new_gens[(1 + 2 * ix):(2 + 2 * ix)]
            lx[3:4, 1] = [o1; z0]

            while new_adjs[jx] == 0
                jx += 1
            end
            new_adjs[jx] -= 1

            if jx <= pf
                lx[1:4, 2] = pfs[jx][1:4, 1]
            else
                lx[1:4, 2] = pds[jx - pf][1:4, 1]
            end
            las[ix + 1] = lx
        end
        @assert is_zero(new_adjs)

        return new{elem_type(R), elem_type(U)}(pb, cms, pfs, pds, lfs, las)
    end
end

###############################################################################
# naïve representation of image variety
###############################################################################

# Naïve representation of Y_{p, l, I, m}
#
# Stored in camera-major form.
struct NaiveImageVarietyElem{S <: RingElem, T <: MPolyRingElem{S}}
    pb::Problem
    pfs::Vector{MatSpaceElem{T}}
    pds::Vector{MatSpaceElem{T}}
    lfs::Vector{MatSpaceElem{T}}
    las::Vector{MatSpaceElem{T}}

    function NaiveImageVarietyElem(cx::CXElem)
        pb = cx.pb
        m, pf, pd, lf, la = _m(pb), _pf(pb), _pd(pb), _lf(pb), _la(pb)
        U = parent(cx.cms[1][1, 1])
        R = base_ring(U)

        pfs = Vector{MatSpaceElem{elem_type(U)}}(undef, m * pf)
        pds = Vector{MatSpaceElem{elem_type(U)}}(undef, m * pd)
        lfs = Vector{MatSpaceElem{elem_type(U)}}(undef, m * lf)
        las = Vector{MatSpaceElem{elem_type(U)}}(undef, m * la)

        for ix in 1:m
            # free points
            for jx in 1:pf
                pfs[jx + pf * (ix - 1)] = cx.cms[ix] * cx.pfs[jx]
            end

            # dep. points
            for jx in 1:pd
                pds[jx + pd * (ix - 1)] = cx.cms[ix] * cx.pds[jx]
            end

            # free lines
            for jx in 1:lf
                lfs[jx + lf * (ix - 1)] = cx.cms[ix] * cx.lfs[jx]
            end

            # adj. lines
            for jx in 1:la
                las[jx + la * (ix - 1)] = cx.cms[ix] * cx.las[jx]
            end
        end

        return new{elem_type(R), elem_type(U)}(pb, pfs, pds, lfs, las)
    end
end

_m(niv::NaiveImageVarietyElem) = _m(niv.pb)
_pf(niv::NaiveImageVarietyElem) = _pf(niv.pb)
_pd(niv::NaiveImageVarietyElem) = _pd(niv.pb)
_lf(niv::NaiveImageVarietyElem) = _lf(niv.pb)
_la(niv::NaiveImageVarietyElem) = _la(niv.pb)

###############################################################################
# efficient representation of image variety
###############################################################################

# Herein, we take the naïve representation, normalize it, and push the
# non-constant entries into a long vector `entries`.

struct ImageVarietyElem{S <: RingElem, T <: MPolyRingElem{S}, V <: FracFieldElem{T}}
    pb::Problem
    entries::Vector{V}

    function ImageVarietyElem(niv::NaiveImageVarietyElem)
        pb = niv.pb
        m, pf, pd, lf, la = _m(pb), _pf(pb), _pd(pb), _lf(pb), _la(pb)
        deps = pb.deps

        if pf != 0
            U = parent(niv.pfs[1][1, 1])
        else
            U = parent(niv.lfs[1][1, 1])
        end
        R = base_ring(U)
        K = fraction_field(U)

        entries = zeros(K, m * dim_image_space(pf, pd, lf, la))
        new_entries = view(entries, 1:length(entries))
        pfs = view(niv.pfs, 1:length(niv.pfs))
        pds = view(niv.pds, 1:length(niv.pds))
        lfs = view(niv.lfs, 1:length(niv.lfs))
        las = view(niv.las, 1:length(niv.las))

        #######################################################################
        # free points
        #######################################################################

        # Normalize via (y1; y2; y3) -> (y1 / y3; y2 / y3; 1)
        for ix in 1:m
            for jx in 1:pf
                new_entries[2 * (jx - 1) + 1] = pfs[jx][1, 1] // pfs[jx][3, 1]
                new_entries[2 * (jx - 1) + 2] = pfs[jx][2, 1] // pfs[jx][3, 1]
            end
            pfs = view(pfs, (pf + 1):length(pfs))
            new_entries = view(new_entries, (2 * pf + 1):length(new_entries))
        end

        #######################################################################
        # dependent points
        #######################################################################

        # A dependent point p = t x + (1 - t) y between two free points x and y
        # is completely determined by t = (p_i - b_i) / (a_i - b_i), where i is
        # arbitrary.

        # We have to reset pfs here since it is shifted from before
        pfs = view(niv.pfs, 1:length(niv.pfs))

        for ix in 1:m
            for jx in 1:pd
                ax, bx = deps[jx][1], deps[jx][2]
                a1 = pfs[ax][1, 1] // pfs[ax][3, 1]
                b1 = pfs[bx][1, 1] // pfs[bx][3, 1]
                v1 = pds[jx][1, 1] // pds[jx][3, 1]
                new_entries[jx] = (v1 - b1) // (a1 - b1)
            end
            pfs = view(pfs, (pf + 1):length(pfs))
            pds = view(pds, (pd + 1):length(pds))
            new_entries = view(new_entries, (pd + 1):length(new_entries))
        end

        #######################################################################
        # free lines
        #######################################################################

        # A free line written on the form (k1 k2; a b; c d) is equivalent to
        # (k1 / (a d - b c) k2 / (a d - b c); 1 0; 0 1), hence completely
        # determined by two variables.
        for ix in 1:m
            for jx in 1:lf
                k1 = lfs[jx][1, 1]
                k2 = lfs[jx][1, 2]
                ak = lfs[jx][2, 1]
                bk = lfs[jx][2, 2]
                ck = lfs[jx][3, 1]
                dk = lfs[jx][3, 2]
                # admbc = ak * dk - bk * ck
                # new_entries[2 * (jx - 1) + 1] = k1 // admbc
                # new_entries[2 * (jx - 1) + 2] = k2 // admbc
                v1 = ak * dk - bk * ck
                v2 = ck * k2 - k1 * dk
                v3 = k1 * bk - ak * k2
                new_entries[2 * (jx - 1) + 1] = v1 // v3
                new_entries[2 * (jx - 1) + 2] = v2 // v3
            end
            lfs = view(lfs, (lf + 1):length(lfs))
            new_entries = view(new_entries, (2 * lf + 1):length(new_entries))
        end

        #######################################################################
        # adjacent lines
        #######################################################################

        # An adjacent line can be written on the form (k1 y1; k2 y2; k3 1).  It
        # is then fully described by the variable (k2 - k3 y2) / (k1 - k3 y1).
        for ix in 1:m
            for jx in 1:la
                k1 = las[jx][1, 1]
                k2 = las[jx][2, 1]
                k3 = las[jx][3, 1]
                y3 = las[jx][3, 2]
                y1 = las[jx][1, 2] // y3
                y2 = las[jx][2, 2] // y3
                new_entries[jx] = (k2 - k3 * y2) // (k1 - k3 * y1)
            end
            las = view(las, (la + 1):length(las))
            new_entries = view(new_entries, (la + 1):length(new_entries))
        end

        return new{elem_type(R), elem_type(U), elem_type(K)}(pb, entries)
    end

    function ImageVarietyElem(pb::Problem, R::V) where {V <: Ring}
        # Get the symbolic representation C_{m} × X_{p, l, I} of problem
        cx = CXElem(pb, R)

        # Map naïvely to images
        niv = NaiveImageVarietyElem(cx)

        return ImageVarietyElem(niv)
    end
end

class(iv::ImageVarietyElem) = iv.pb.cl
field(iv::ImageVarietyElem) = parent(iv.entries[1])
number_of_variables(iv::ImageVarietyElem) = number_of_variables(base_ring(field(iv)))

###############################################################################
# jacobian
###############################################################################

function jacobian(iv::ImageVarietyElem)
    entries = iv.entries
    cl = class(iv)
    n = num_vars(cl)
    K = field(iv)

    # Ensure that Jacobian really is square
    @assert length(entries) == n

    M = matrix_space(K, n, n)
    jac = zero(M)

    for ix in 1:n, jx in 1:n
        jac[ix, jx] = derivative(entries[jx], ix)
    end

    return jac
end

function jacobian(pb::Problem, R::V) where {V <: Ring}
    jacobian(ImageVarietyElem(pb, R))
end

# NOTE: This will destroy input
function similar_matrix(mat::MatSpaceElem{V}) where {S <: RingElem, T <: MPolyRingElem{S}, V <: FracFieldElem{T}}
    n = ncols(mat)
    K = base_ring(mat)
    R = base_ring(K)

    for ix in 1:n, jx in 1:n
        if !is_one(denominator(mat[ix, jx]))
            den = denominator(mat[ix, jx])
            for ix2 in 1:n
                mat[ix2, jx] *= den
            end
        end
    end

    @assert all(x -> is_one(denominator(x)), mat)

    M = matrix_space(R, n, n)
    simmat = M()
    for ix in 1:n, jx in 1:n
        simmat[ix, jx] = numerator(mat[ix, jx])
    end

    return simmat
end

###############################################################################
# computing classes of point-line balanced problems
###############################################################################

# Some big prime that still allows arithmetic in double precision without
# losing too much precision.
big_prime = UInt64(281474976710677)
@assert is_prime(big_prime)
modring = residue_ring(ZZ, big_prime)[1]

###############################################################################
# numerical minimality check
###############################################################################

function is_minimal(pb::Problem; numevals::Int = 1000)
    # Get symbolical jacobian
    jac = jacobian(pb, modring)
    simjac = similar_matrix(jac)

    n = ncols(simjac)
    P = base_ring(simjac)
    nvars = number_of_variables(P)
    K = base_ring(P)
    M = matrix_space(K, n, n)
    jaceval = M()

    for nx in 1:numevals
        randpoint = rand(K, nvars)
        for ix in 1:n, jx in 1:n
            jaceval[ix, jx] = evaluate(simjac[ix, jx], randpoint)
        end

        if !is_zero(det(jaceval))
            return true
        end
    end

    return false
end

###############################################################################
# generate all minimal problems
###############################################################################

function generate_minimal_problems(numevals::Int = 1000)
    res = Problem[]

    for pb in candidate_problems
        if is_minimal(pb, numevals = numevals)
            push!(res, pb)
        end
    end

    return res
end

# This checks the 434 candidate problems for minimality and proves 
# that 285 are indeed minimal, as claimed in the proof of Main Theorem 2.3 c)
                
###############################################################################
# all minimal problems
###############################################################################

# The following problems were generated via `minimal_problems(numevals = 1000)'
# and its result was printed below using the following function:
function print_problem_array(pbs::Vector{Problem})
    str = "minimal_problems = [\n"
    for pb in pbs
        str *= "    Problem("
        str *= "Class($(_m(pb)), $(_pf(pb)), $(_pd(pb)), $(_lf(pb)), $(_la(pb))), "
        str *= "$(pb.deps), "
        str *= "$(pb.adjs)"
        if pb !== pbs[end]
            str *= "),\n"
        else
            str *= ")\n   ]"
        end
    end
    return str
end

minimal_problems = [
    Problem(Class(3, 0, 0, 9, 0), Tuple{Int, Int}[], Int[]),
    Problem(Class(3, 1, 0, 4, 7), Tuple{Int, Int}[], [7]),
    Problem(Class(3, 1, 0, 5, 5), Tuple{Int, Int}[], [5]),
    Problem(Class(3, 1, 0, 6, 3), Tuple{Int, Int}[], [3]),
    Problem(Class(3, 1, 0, 7, 1), Tuple{Int, Int}[], [1]),
    Problem(Class(3, 2, 0, 0, 12), Tuple{Int, Int}[], [6, 6]),
    Problem(Class(3, 2, 0, 1, 10), Tuple{Int, Int}[], [6, 4]),
    Problem(Class(3, 2, 0, 1, 10), Tuple{Int, Int}[], [5, 5]),
    Problem(Class(3, 2, 0, 2, 8), Tuple{Int, Int}[], [6, 2]),
    Problem(Class(3, 2, 0, 2, 8), Tuple{Int, Int}[], [5, 3]),
    Problem(Class(3, 2, 0, 2, 8), Tuple{Int, Int}[], [4, 4]),
    Problem(Class(3, 2, 0, 3, 6), Tuple{Int, Int}[], [6, 0]),
    Problem(Class(3, 2, 0, 3, 6), Tuple{Int, Int}[], [5, 1]),
    Problem(Class(3, 2, 0, 3, 6), Tuple{Int, Int}[], [4, 2]),
    Problem(Class(3, 2, 0, 3, 6), Tuple{Int, Int}[], [3, 3]),
    Problem(Class(3, 2, 0, 4, 4), Tuple{Int, Int}[], [4, 0]),
    Problem(Class(3, 2, 0, 4, 4), Tuple{Int, Int}[], [3, 1]),
    Problem(Class(3, 2, 0, 4, 4), Tuple{Int, Int}[], [2, 2]),
    Problem(Class(3, 2, 0, 5, 2), Tuple{Int, Int}[], [2, 0]),
    Problem(Class(3, 2, 0, 5, 2), Tuple{Int, Int}[], [1, 1]),
    Problem(Class(3, 2, 0, 6, 0), Tuple{Int, Int}[], [0, 0]),
    Problem(Class(3, 3, 0, 0, 9), Tuple{Int, Int}[], [5, 4, 0]),
    Problem(Class(3, 3, 0, 0, 9), Tuple{Int, Int}[], [5, 3, 1]),
    Problem(Class(3, 3, 0, 0, 9), Tuple{Int, Int}[], [5, 2, 2]),
    Problem(Class(3, 3, 0, 0, 9), Tuple{Int, Int}[], [4, 4, 1]),
    Problem(Class(3, 3, 0, 0, 9), Tuple{Int, Int}[], [4, 3, 2]),
    Problem(Class(3, 3, 0, 0, 9), Tuple{Int, Int}[], [3, 3, 3]),
    Problem(Class(3, 3, 0, 1, 7), Tuple{Int, Int}[], [5, 2, 0]),
    Problem(Class(3, 3, 0, 1, 7), Tuple{Int, Int}[], [4, 3, 0]),
    Problem(Class(3, 3, 0, 1, 7), Tuple{Int, Int}[], [5, 1, 1]),
    Problem(Class(3, 3, 0, 1, 7), Tuple{Int, Int}[], [4, 2, 1]),
    Problem(Class(3, 3, 0, 1, 7), Tuple{Int, Int}[], [3, 3, 1]),
    Problem(Class(3, 3, 0, 1, 7), Tuple{Int, Int}[], [3, 2, 2]),
    Problem(Class(3, 3, 0, 2, 5), Tuple{Int, Int}[], [5, 0, 0]),
    Problem(Class(3, 3, 0, 2, 5), Tuple{Int, Int}[], [4, 1, 0]),
    Problem(Class(3, 3, 0, 2, 5), Tuple{Int, Int}[], [3, 2, 0]),
    Problem(Class(3, 3, 0, 2, 5), Tuple{Int, Int}[], [3, 1, 1]),
    Problem(Class(3, 3, 0, 2, 5), Tuple{Int, Int}[], [2, 2, 1]),
    Problem(Class(3, 3, 0, 3, 3), Tuple{Int, Int}[], [3, 0, 0]),
    Problem(Class(3, 3, 0, 3, 3), Tuple{Int, Int}[], [2, 1, 0]),
    Problem(Class(3, 3, 0, 3, 3), Tuple{Int, Int}[], [1, 1, 1]),
    Problem(Class(3, 3, 0, 4, 1), Tuple{Int, Int}[], [1, 0, 0]),
    Problem(Class(3, 2, 1, 0, 10), [(1, 2)], [6, 4, 0]),
    Problem(Class(3, 2, 1, 0, 10), [(1, 2)], [5, 5, 0]),
    Problem(Class(3, 2, 1, 0, 10), [(1, 2)], [6, 3, 1]),
    Problem(Class(3, 2, 1, 0, 10), [(1, 2)], [6, 2, 2]),
    Problem(Class(3, 2, 1, 0, 10), [(1, 2)], [5, 4, 1]),
    Problem(Class(3, 2, 1, 0, 10), [(1, 2)], [5, 3, 2]),
    Problem(Class(3, 2, 1, 0, 10), [(1, 2)], [4, 4, 2]),
    Problem(Class(3, 2, 1, 0, 10), [(1, 2)], [4, 3, 3]),
    Problem(Class(3, 2, 1, 1, 8), [(1, 2)], [6, 2, 0]),
    Problem(Class(3, 2, 1, 1, 8), [(1, 2)], [5, 3, 0]),
    Problem(Class(3, 2, 1, 1, 8), [(1, 2)], [4, 4, 0]),
    Problem(Class(3, 2, 1, 1, 8), [(1, 2)], [6, 1, 1]),
    Problem(Class(3, 2, 1, 1, 8), [(1, 2)], [5, 2, 1]),
    Problem(Class(3, 2, 1, 1, 8), [(1, 2)], [4, 3, 1]),
    Problem(Class(3, 2, 1, 1, 8), [(1, 2)], [4, 2, 2]),
    Problem(Class(3, 2, 1, 1, 8), [(1, 2)], [3, 3, 2]),
    Problem(Class(3, 2, 1, 2, 6), [(1, 2)], [6, 0, 0]),
    Problem(Class(3, 2, 1, 2, 6), [(1, 2)], [5, 1, 0]),
    Problem(Class(3, 2, 1, 2, 6), [(1, 2)], [4, 2, 0]),
    Problem(Class(3, 2, 1, 2, 6), [(1, 2)], [3, 3, 0]),
    Problem(Class(3, 2, 1, 2, 6), [(1, 2)], [4, 1, 1]),
    Problem(Class(3, 2, 1, 2, 6), [(1, 2)], [3, 2, 1]),
    Problem(Class(3, 2, 1, 2, 6), [(1, 2)], [2, 2, 2]),
    Problem(Class(3, 2, 1, 3, 4), [(1, 2)], [4, 0, 0]),
    Problem(Class(3, 2, 1, 3, 4), [(1, 2)], [3, 1, 0]),
    Problem(Class(3, 2, 1, 3, 4), [(1, 2)], [2, 2, 0]),
    Problem(Class(3, 2, 1, 3, 4), [(1, 2)], [2, 1, 1]),
    Problem(Class(3, 2, 1, 4, 2), [(1, 2)], [2, 0, 0]),
    Problem(Class(3, 2, 1, 4, 2), [(1, 2)], [1, 1, 0]),
    Problem(Class(3, 2, 1, 5, 0), [(1, 2)], [0, 0, 0]),
    Problem(Class(3, 4, 0, 0, 6), Tuple{Int, Int}[], [4, 2, 0, 0]),
    Problem(Class(3, 4, 0, 0, 6), Tuple{Int, Int}[], [3, 3, 0, 0]),
    Problem(Class(3, 4, 0, 0, 6), Tuple{Int, Int}[], [4, 1, 1, 0]),
    Problem(Class(3, 4, 0, 0, 6), Tuple{Int, Int}[], [3, 2, 1, 0]),
    Problem(Class(3, 4, 0, 0, 6), Tuple{Int, Int}[], [2, 2, 2, 0]),
    Problem(Class(3, 4, 0, 0, 6), Tuple{Int, Int}[], [3, 1, 1, 1]),
    Problem(Class(3, 4, 0, 0, 6), Tuple{Int, Int}[], [2, 2, 1, 1]),
    Problem(Class(3, 4, 0, 1, 4), Tuple{Int, Int}[], [3, 1, 0, 0]),
    Problem(Class(3, 4, 0, 1, 4), Tuple{Int, Int}[], [2, 2, 0, 0]),
    Problem(Class(3, 4, 0, 1, 4), Tuple{Int, Int}[], [2, 1, 1, 0]),
    Problem(Class(3, 4, 0, 1, 4), Tuple{Int, Int}[], [1, 1, 1, 1]),
    Problem(Class(3, 4, 0, 2, 2), Tuple{Int, Int}[], [2, 0, 0, 0]),
    Problem(Class(3, 4, 0, 2, 2), Tuple{Int, Int}[], [1, 1, 0, 0]),
    Problem(Class(3, 4, 0, 3, 0), Tuple{Int, Int}[], [0, 0, 0, 0]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [4, 0, 3, 0]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [3, 1, 3, 0]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [2, 2, 3, 0]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [2, 1, 3, 1]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [5, 0, 2, 0]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [4, 1, 2, 0]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [3, 2, 2, 0]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [3, 1, 2, 1]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [2, 2, 2, 1]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [5, 1, 1, 0]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [4, 2, 1, 0]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [3, 3, 1, 0]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [4, 1, 1, 1]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [3, 2, 1, 1]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [2, 2, 1, 2]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [5, 2, 0, 0]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [4, 3, 0, 0]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [5, 1, 0, 1]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [4, 2, 0, 1]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [3, 3, 0, 1]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [3, 2, 0, 2]),
    Problem(Class(3, 3, 1, 1, 5), [(1, 2)], [2, 0, 3, 0]),
    Problem(Class(3, 3, 1, 1, 5), [(1, 2)], [1, 1, 3, 0]),
    Problem(Class(3, 3, 1, 1, 5), [(1, 2)], [3, 0, 2, 0]),
    Problem(Class(3, 3, 1, 1, 5), [(1, 2)], [2, 1, 2, 0]),
    Problem(Class(3, 3, 1, 1, 5), [(1, 2)], [1, 1, 2, 1]),
    Problem(Class(3, 3, 1, 1, 5), [(1, 2)], [4, 0, 1, 0]),
    Problem(Class(3, 3, 1, 1, 5), [(1, 2)], [3, 1, 1, 0]),
    Problem(Class(3, 3, 1, 1, 5), [(1, 2)], [2, 2, 1, 0]),
    Problem(Class(3, 3, 1, 1, 5), [(1, 2)], [2, 1, 1, 1]),
    Problem(Class(3, 3, 1, 1, 5), [(1, 2)], [4, 1, 0, 0]),
    Problem(Class(3, 3, 1, 1, 5), [(1, 2)], [3, 2, 0, 0]),
    Problem(Class(3, 3, 1, 1, 5), [(1, 2)], [3, 1, 0, 1]),
    Problem(Class(3, 3, 1, 1, 5), [(1, 2)], [2, 2, 0, 1]),
    Problem(Class(3, 3, 1, 2, 3), [(1, 2)], [0, 0, 3, 0]),
    Problem(Class(3, 3, 1, 2, 3), [(1, 2)], [1, 0, 2, 0]),
    Problem(Class(3, 3, 1, 2, 3), [(1, 2)], [2, 0, 1, 0]),
    Problem(Class(3, 3, 1, 2, 3), [(1, 2)], [1, 1, 1, 0]),
    Problem(Class(3, 3, 1, 2, 3), [(1, 2)], [3, 0, 0, 0]),
    Problem(Class(3, 3, 1, 2, 3), [(1, 2)], [2, 1, 0, 0]),
    Problem(Class(3, 3, 1, 2, 3), [(1, 2)], [1, 1, 0, 1]),
    Problem(Class(3, 5, 0, 0, 3), Tuple{Int, Int}[], [3, 0, 0, 0, 0]),
    Problem(Class(3, 5, 0, 0, 3), Tuple{Int, Int}[], [2, 1, 0, 0, 0]),
    Problem(Class(3, 5, 0, 0, 3), Tuple{Int, Int}[], [1, 1, 1, 0, 0]),
    Problem(Class(3, 5, 0, 1, 1), Tuple{Int, Int}[], [1, 0, 0, 0, 0]),
    Problem(Class(3, 4, 1, 0, 4), [(1, 2)], [0, 0, 2, 2, 0]),
    Problem(Class(3, 4, 1, 0, 4), [(1, 2)], [1, 0, 2, 1, 0]),
    Problem(Class(3, 4, 1, 0, 4), [(1, 2)], [2, 0, 2, 0, 0]),
    Problem(Class(3, 4, 1, 0, 4), [(1, 2)], [2, 0, 1, 1, 0]),
    Problem(Class(3, 4, 1, 0, 4), [(1, 2)], [1, 1, 2, 0, 0]),
    Problem(Class(3, 4, 1, 0, 4), [(1, 2)], [1, 1, 1, 1, 0]),
    Problem(Class(3, 4, 1, 0, 4), [(1, 2)], [3, 0, 1, 0, 0]),
    Problem(Class(3, 4, 1, 0, 4), [(1, 2)], [2, 1, 1, 0, 0]),
    Problem(Class(3, 4, 1, 0, 4), [(1, 2)], [1, 1, 1, 0, 1]),
    Problem(Class(3, 4, 1, 0, 4), [(1, 2)], [4, 0, 0, 0, 0]),
    Problem(Class(3, 4, 1, 0, 4), [(1, 2)], [3, 1, 0, 0, 0]),
    Problem(Class(3, 4, 1, 0, 4), [(1, 2)], [2, 2, 0, 0, 0]),
    Problem(Class(3, 4, 1, 0, 4), [(1, 2)], [2, 1, 0, 0, 1]),
    Problem(Class(3, 4, 1, 1, 2), [(1, 2)], [0, 0, 1, 1, 0]),
    Problem(Class(3, 4, 1, 1, 2), [(1, 2)], [1, 0, 1, 0, 0]),
    Problem(Class(3, 4, 1, 1, 2), [(1, 2)], [2, 0, 0, 0, 0]),
    Problem(Class(3, 4, 1, 1, 2), [(1, 2)], [1, 1, 0, 0, 0]),
    Problem(Class(3, 4, 1, 2, 0), [(1, 2)], [0, 0, 0, 0, 0]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [0, 3, 2, 0, 0]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [0, 3, 1, 0, 1]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [0, 2, 2, 1, 0]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [0, 2, 1, 1, 1]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [0, 3, 1, 1, 0]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [0, 2, 1, 2, 0]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [0, 3, 0, 2, 0]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [1, 2, 2, 0, 0]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [1, 2, 1, 0, 1]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [1, 1, 1, 1, 1]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [1, 3, 1, 0, 0]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [1, 2, 1, 1, 0]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [1, 3, 0, 1, 0]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [1, 2, 0, 2, 0]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [2, 2, 1, 0, 0]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [2, 1, 1, 1, 0]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [2, 3, 0, 0, 0]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [2, 2, 0, 1, 0]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [3, 1, 1, 0, 0]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [3, 2, 0, 0, 0]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [3, 1, 0, 1, 0]),
    Problem(Class(3, 6, 0, 0, 0), Tuple{Int, Int}[], [0, 0, 0, 0, 0, 0]),
    Problem(Class(3, 5, 1, 0, 1), [(1, 2)], [0, 0, 1, 0, 0, 0]),
    Problem(Class(3, 5, 1, 0, 1), [(1, 2)], [1, 0, 0, 0, 0, 0]),
    Problem(Class(3, 4, 2, 0, 2), [(1, 2), (1, 3)], [0, 1, 1, 0, 0, 0]),
    Problem(Class(3, 4, 2, 0, 2), [(1, 2), (1, 3)], [0, 2, 0, 0, 0, 0]),
    Problem(Class(3, 4, 2, 0, 2), [(1, 2), (1, 3)], [0, 1, 0, 0, 1, 0]),
    Problem(Class(3, 4, 2, 0, 2), [(1, 2), (1, 3)], [1, 1, 0, 0, 0, 0]),
    Problem(Class(3, 4, 2, 0, 2), [(1, 2), (1, 3)], [2, 0, 0, 0, 0, 0]),
    Problem(Class(3, 4, 2, 0, 2), [(1, 2), (3, 4)], [1, 0, 1, 0, 0, 0]),
    Problem(Class(3, 4, 2, 0, 2), [(1, 2), (3, 4)], [2, 0, 0, 0, 0, 0]),
    Problem(Class(3, 4, 2, 0, 2), [(1, 2), (3, 4)], [1, 1, 0, 0, 0, 0]),
    Problem(Class(3, 4, 2, 1, 0), [(1, 2), (3, 4)], [0, 0, 0, 0, 0, 0]),
    Problem(Class(4, 1, 0, 3, 6), Tuple{Int, Int}[], [6]),
    Problem(Class(4, 1, 0, 4, 4), Tuple{Int, Int}[], [4]),
    Problem(Class(4, 1, 0, 5, 2), Tuple{Int, Int}[], [2]),
    Problem(Class(4, 1, 0, 6, 0), Tuple{Int, Int}[], [0]),
    Problem(Class(4, 3, 0, 0, 7), Tuple{Int, Int}[], [4, 3, 0]),
    Problem(Class(4, 3, 0, 0, 7), Tuple{Int, Int}[], [4, 2, 1]),
    Problem(Class(4, 3, 0, 0, 7), Tuple{Int, Int}[], [3, 3, 1]),
    Problem(Class(4, 3, 0, 0, 7), Tuple{Int, Int}[], [3, 2, 2]),
    Problem(Class(4, 3, 0, 1, 5), Tuple{Int, Int}[], [3, 2, 0]),
    Problem(Class(4, 3, 0, 1, 5), Tuple{Int, Int}[], [3, 1, 1]),
    Problem(Class(4, 3, 0, 1, 5), Tuple{Int, Int}[], [2, 2, 1]),
    Problem(Class(4, 3, 0, 2, 3), Tuple{Int, Int}[], [3, 0, 0]),
    Problem(Class(4, 3, 0, 2, 3), Tuple{Int, Int}[], [2, 1, 0]),
    Problem(Class(4, 3, 0, 2, 3), Tuple{Int, Int}[], [1, 1, 1]),
    Problem(Class(4, 3, 0, 3, 1), Tuple{Int, Int}[], [1, 0, 0]),
    Problem(Class(4, 2, 1, 0, 8), [(1, 2)], [5, 3, 0]),
    Problem(Class(4, 2, 1, 0, 8), [(1, 2)], [4, 4, 0]),
    Problem(Class(4, 2, 1, 0, 8), [(1, 2)], [5, 2, 1]),
    Problem(Class(4, 2, 1, 0, 8), [(1, 2)], [4, 3, 1]),
    Problem(Class(4, 2, 1, 0, 8), [(1, 2)], [4, 2, 2]),
    Problem(Class(4, 2, 1, 0, 8), [(1, 2)], [3, 3, 2]),
    Problem(Class(4, 2, 1, 1, 6), [(1, 2)], [4, 2, 0]),
    Problem(Class(4, 2, 1, 1, 6), [(1, 2)], [3, 3, 0]),
    Problem(Class(4, 2, 1, 1, 6), [(1, 2)], [4, 1, 1]),
    Problem(Class(4, 2, 1, 1, 6), [(1, 2)], [3, 2, 1]),
    Problem(Class(4, 2, 1, 1, 6), [(1, 2)], [2, 2, 2]),
    Problem(Class(4, 2, 1, 2, 4), [(1, 2)], [4, 0, 0]),
    Problem(Class(4, 2, 1, 2, 4), [(1, 2)], [3, 1, 0]),
    Problem(Class(4, 2, 1, 2, 4), [(1, 2)], [2, 2, 0]),
    Problem(Class(4, 2, 1, 2, 4), [(1, 2)], [2, 1, 1]),
    Problem(Class(4, 2, 1, 3, 2), [(1, 2)], [2, 0, 0]),
    Problem(Class(4, 2, 1, 3, 2), [(1, 2)], [1, 1, 0]),
    Problem(Class(4, 2, 1, 4, 0), [(1, 2)], [0, 0, 0]),
    Problem(Class(4, 5, 0, 0, 2), Tuple{Int, Int}[], [2, 0, 0, 0, 0]),
    Problem(Class(4, 5, 0, 0, 2), Tuple{Int, Int}[], [1, 1, 0, 0, 0]),
    Problem(Class(4, 5, 0, 1, 0), Tuple{Int, Int}[], [0, 0, 0, 0, 0]),
    Problem(Class(4, 4, 1, 0, 3), [(1, 2)], [1, 0, 1, 1, 0]),
    Problem(Class(4, 4, 1, 0, 3), [(1, 2)], [2, 0, 1, 0, 0]),
    Problem(Class(4, 4, 1, 0, 3), [(1, 2)], [1, 1, 1, 0, 0]),
    Problem(Class(4, 4, 1, 0, 3), [(1, 2)], [3, 0, 0, 0, 0]),
    Problem(Class(4, 4, 1, 0, 3), [(1, 2)], [2, 1, 0, 0, 0]),
    Problem(Class(4, 4, 1, 0, 3), [(1, 2)], [1, 1, 0, 0, 1]),
    Problem(Class(4, 4, 1, 1, 1), [(1, 2)], [1, 0, 0, 0, 0]),
    Problem(Class(4, 3, 2, 0, 4), [(1, 2), (1, 3)], [0, 2, 2, 0, 0]),
    Problem(Class(4, 3, 2, 0, 4), [(1, 2), (1, 3)], [0, 2, 1, 0, 1]),
    Problem(Class(4, 3, 2, 0, 4), [(1, 2), (1, 3)], [0, 1, 1, 1, 1]),
    Problem(Class(4, 3, 2, 0, 4), [(1, 2), (1, 3)], [0, 2, 1, 1, 0]),
    Problem(Class(4, 3, 2, 0, 4), [(1, 2), (1, 3)], [0, 2, 0, 2, 0]),
    Problem(Class(4, 3, 2, 0, 4), [(1, 2), (1, 3)], [1, 2, 1, 0, 0]),
    Problem(Class(4, 3, 2, 0, 4), [(1, 2), (1, 3)], [1, 1, 1, 1, 0]),
    Problem(Class(4, 3, 2, 0, 4), [(1, 2), (1, 3)], [1, 2, 0, 1, 0]),
    Problem(Class(4, 3, 2, 0, 4), [(1, 2), (1, 3)], [2, 1, 1, 0, 0]),
    Problem(Class(4, 3, 2, 0, 4), [(1, 2), (1, 3)], [2, 2, 0, 0, 0]),
    Problem(Class(4, 3, 2, 0, 4), [(1, 2), (1, 3)], [2, 1, 0, 1, 0]),
    Problem(Class(5, 1, 0, 3, 5), Tuple{Int, Int}[], [5]),
    Problem(Class(5, 1, 0, 4, 3), Tuple{Int, Int}[], [3]),
    Problem(Class(5, 1, 0, 5, 1), Tuple{Int, Int}[], [1]),
    Problem(Class(5, 4, 0, 0, 4), Tuple{Int, Int}[], [2, 2, 0, 0]),
    Problem(Class(5, 4, 0, 0, 4), Tuple{Int, Int}[], [2, 1, 1, 0]),
    Problem(Class(5, 4, 0, 0, 4), Tuple{Int, Int}[], [1, 1, 1, 1]),
    Problem(Class(5, 4, 0, 1, 2), Tuple{Int, Int}[], [1, 1, 0, 0]),
    Problem(Class(5, 4, 0, 2, 0), Tuple{Int, Int}[], [0, 0, 0, 0]),
    Problem(Class(5, 3, 1, 0, 5), [(1, 2)], [3, 0, 2, 0]),
    Problem(Class(5, 3, 1, 0, 5), [(1, 2)], [2, 1, 2, 0]),
    Problem(Class(5, 3, 1, 0, 5), [(1, 2)], [1, 1, 2, 1]),
    Problem(Class(5, 3, 1, 0, 5), [(1, 2)], [3, 1, 1, 0]),
    Problem(Class(5, 3, 1, 0, 5), [(1, 2)], [2, 2, 1, 0]),
    Problem(Class(5, 3, 1, 0, 5), [(1, 2)], [2, 1, 1, 1]),
    Problem(Class(5, 3, 1, 0, 5), [(1, 2)], [3, 2, 0, 0]),
    Problem(Class(5, 3, 1, 0, 5), [(1, 2)], [3, 1, 0, 1]),
    Problem(Class(5, 3, 1, 0, 5), [(1, 2)], [2, 2, 0, 1]),
    Problem(Class(5, 3, 1, 1, 3), [(1, 2)], [2, 0, 1, 0]),
    Problem(Class(5, 3, 1, 1, 3), [(1, 2)], [1, 1, 1, 0]),
    Problem(Class(5, 3, 1, 1, 3), [(1, 2)], [2, 1, 0, 0]),
    Problem(Class(5, 3, 1, 1, 3), [(1, 2)], [1, 1, 0, 1]),
    Problem(Class(6, 3, 0, 0, 6), Tuple{Int, Int}[], [3, 3, 0]),
    Problem(Class(6, 3, 0, 0, 6), Tuple{Int, Int}[], [3, 2, 1]),
    Problem(Class(6, 3, 0, 0, 6), Tuple{Int, Int}[], [2, 2, 2]),
    Problem(Class(6, 3, 0, 1, 4), Tuple{Int, Int}[], [2, 2, 0]),
    Problem(Class(6, 3, 0, 1, 4), Tuple{Int, Int}[], [2, 1, 1]),
    Problem(Class(6, 3, 0, 2, 2), Tuple{Int, Int}[], [2, 0, 0]),
    Problem(Class(6, 3, 0, 2, 2), Tuple{Int, Int}[], [1, 1, 0]),
    Problem(Class(6, 2, 1, 0, 7), [(1, 2)], [4, 3, 0]),
    Problem(Class(6, 2, 1, 0, 7), [(1, 2)], [4, 2, 1]),
    Problem(Class(6, 2, 1, 0, 7), [(1, 2)], [3, 3, 1]),
    Problem(Class(6, 2, 1, 0, 7), [(1, 2)], [3, 2, 2]),
    Problem(Class(6, 2, 1, 1, 5), [(1, 2)], [3, 2, 0]),
    Problem(Class(6, 2, 1, 1, 5), [(1, 2)], [3, 1, 1]),
    Problem(Class(6, 2, 1, 1, 5), [(1, 2)], [2, 2, 1]),
    Problem(Class(6, 2, 1, 2, 3), [(1, 2)], [3, 0, 0]),
    Problem(Class(6, 2, 1, 2, 3), [(1, 2)], [2, 1, 0]),
    Problem(Class(6, 2, 1, 2, 3), [(1, 2)], [1, 1, 1]),
    Problem(Class(7, 2, 0, 0, 8), Tuple{Int, Int}[], [4, 4]),
    Problem(Class(7, 2, 0, 1, 6), Tuple{Int, Int}[], [3, 3]),
    Problem(Class(7, 2, 0, 2, 4), Tuple{Int, Int}[], [3, 1]),
    Problem(Class(7, 2, 0, 2, 4), Tuple{Int, Int}[], [2, 2]),
    Problem(Class(7, 2, 0, 3, 2), Tuple{Int, Int}[], [2, 0]),
    Problem(Class(7, 2, 0, 3, 2), Tuple{Int, Int}[], [1, 1]),
    Problem(Class(7, 2, 0, 4, 0), Tuple{Int, Int}[], [0, 0]),
    Problem(Class(8, 1, 0, 3, 4), Tuple{Int, Int}[], [4]),
    Problem(Class(8, 1, 0, 4, 2), Tuple{Int, Int}[], [2]),
    Problem(Class(8, 1, 0, 5, 0), Tuple{Int, Int}[], [0]),
    Problem(Class(9, 0, 0, 6, 0), Tuple{Int, Int}[], Int[])
   ]

###############################################################################
# all candidate problems that are non-minimal
###############################################################################

# NOTE: This list is missing some balanced point-line problems that failed to
# appear in `candidate_problems' due to containing four points on a line or six
# points on a plane.

# Generated via `filter(x -> !in(x, minimal_problems), candidate_problems)'
nonminimal_candidate_problems = [
    Problem(Class(3, 1, 0, 0, 15), Tuple{Int64, Int64}[], [15]),                 #Criterion 1
    Problem(Class(3, 1, 0, 1, 13), Tuple{Int64, Int64}[], [13]),                 #Criterion 1
    Problem(Class(3, 1, 0, 2, 11), Tuple{Int64, Int64}[], [11]),                 #Criterion 1
    Problem(Class(3, 1, 0, 3, 9), Tuple{Int64, Int64}[], [9]),                   #Criterion 1
    Problem(Class(3, 2, 0, 0, 12), Tuple{Int64, Int64}[], [12, 0]),              #Criterion 2
    Problem(Class(3, 2, 0, 0, 12), Tuple{Int64, Int64}[], [11, 1]),              #Criterion 2
    Problem(Class(3, 2, 0, 0, 12), Tuple{Int64, Int64}[], [10, 2]),              #Criterion 2
    Problem(Class(3, 2, 0, 0, 12), Tuple{Int64, Int64}[], [9, 3]),               #Criterion 2
    Problem(Class(3, 2, 0, 0, 12), Tuple{Int64, Int64}[], [8, 4]),               #Criterion 2
    Problem(Class(3, 2, 0, 0, 12), Tuple{Int64, Int64}[], [7, 5]),               #Criterion 2
    Problem(Class(3, 2, 0, 1, 10), Tuple{Int64, Int64}[], [10, 0]),              #Criterion 2
    Problem(Class(3, 2, 0, 1, 10), Tuple{Int64, Int64}[], [9, 1]),               #Criterion 2
    Problem(Class(3, 2, 0, 1, 10), Tuple{Int64, Int64}[], [8, 2]),               #Criterion 2
    Problem(Class(3, 2, 0, 1, 10), Tuple{Int64, Int64}[], [7, 3]),               #Criterion 2
    Problem(Class(3, 2, 0, 2, 8), Tuple{Int64, Int64}[], [8, 0]),                #Criterion 2
    Problem(Class(3, 2, 0, 2, 8), Tuple{Int64, Int64}[], [7, 1]),                #Criterion 2
    Problem(Class(3, 3, 0, 0, 9), Tuple{Int64, Int64}[], [9, 0, 0]),             #Criterion 3
    Problem(Class(3, 3, 0, 0, 9), Tuple{Int64, Int64}[], [8, 1, 0]),             #Criterion 3
    Problem(Class(3, 3, 0, 0, 9), Tuple{Int64, Int64}[], [7, 2, 0]),             #Criterion 3
    Problem(Class(3, 3, 0, 0, 9), Tuple{Int64, Int64}[], [6, 3, 0]),             #Criterion 3
    Problem(Class(3, 3, 0, 0, 9), Tuple{Int64, Int64}[], [7, 1, 1]),             #Criterion 3
    Problem(Class(3, 3, 0, 0, 9), Tuple{Int64, Int64}[], [6, 2, 1]),             #Criterion 3
    Problem(Class(3, 3, 0, 1, 7), Tuple{Int64, Int64}[], [7, 0, 0]),             #Criterion 3
    Problem(Class(3, 3, 0, 1, 7), Tuple{Int64, Int64}[], [6, 1, 0]),             #Criterion 3
    Problem(Class(3, 2, 1, 0, 10), [(1, 2)], [10, 0, 0]),                        #Criterion 2
    Problem(Class(3, 2, 1, 0, 10), [(1, 2)], [9, 1, 0]),                         #Criterion 2
    Problem(Class(3, 2, 1, 0, 10), [(1, 2)], [8, 2, 0]),                         #Criterion 2
    Problem(Class(3, 2, 1, 0, 10), [(1, 2)], [7, 3, 0]),                         #Criterion 2
    Problem(Class(3, 2, 1, 0, 10), [(1, 2)], [8, 1, 1]),                         #Criterion 2
    Problem(Class(3, 2, 1, 0, 10), [(1, 2)], [7, 2, 1]),                         #Criterion 2
    Problem(Class(3, 2, 1, 1, 8), [(1, 2)], [8, 0, 0]),                          #Criterion 2
    Problem(Class(3, 2, 1, 1, 8), [(1, 2)], [7, 1, 0]),                          #Criterion 2
    Problem(Class(3, 4, 0, 0, 6), Tuple{Int64, Int64}[], [6, 0, 0, 0]),          #Criterion 4
    Problem(Class(3, 4, 0, 0, 6), Tuple{Int64, Int64}[], [5, 1, 0, 0]),          #Criterion 4
    Problem(Class(3, 4, 0, 1, 4), Tuple{Int64, Int64}[], [4, 0, 0, 0]),
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [0, 0, 7, 0]),                       #Criterion 5
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [1, 0, 6, 0]),                       #Criterion 5
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [2, 0, 5, 0]),                       #Criterion 5
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [1, 1, 5, 0]),                       #Criterion 5
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [3, 0, 4, 0]),                       #Criterion 5
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [2, 1, 4, 0]),                       #Criterion 5
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [1, 1, 4, 1]),                       #Criterion 5
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [6, 0, 1, 0]),                       #Criterion 3
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [7, 0, 0, 0]),                       #Criterion 3
    Problem(Class(3, 3, 1, 0, 7), [(1, 2)], [6, 1, 0, 0]),                       #Criterion 3
    Problem(Class(3, 3, 1, 1, 5), [(1, 2)], [0, 0, 5, 0]),                       #Criterion 5
    Problem(Class(3, 3, 1, 1, 5), [(1, 2)], [1, 0, 4, 0]),                       #Criterion 5
    Problem(Class(3, 3, 1, 1, 5), [(1, 2)], [5, 0, 0, 0]),
    Problem(Class(3, 3, 1, 3, 1), [(1, 2)], [0, 0, 1, 0]),
    Problem(Class(3, 3, 1, 3, 1), [(1, 2)], [1, 0, 0, 0]),
    Problem(Class(3, 4, 1, 0, 4), [(1, 2)], [0, 0, 4, 0, 0]),                    #Criterion 6
    Problem(Class(3, 4, 1, 0, 4), [(1, 2)], [0, 0, 3, 1, 0]),                    #Criterion 6
    Problem(Class(3, 4, 1, 0, 4), [(1, 2)], [1, 0, 3, 0, 0]),                    #Criterion 6
    Problem(Class(3, 4, 1, 1, 2), [(1, 2)], [0, 0, 2, 0, 0]),
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [0, 4, 1, 0, 0]),            #Criterion 5
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [0, 5, 0, 0, 0]),            #Criterion 5
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [0, 4, 0, 1, 0]),            #Criterion 5
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [1, 4, 0, 0, 0]),            #Criterion 5
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [4, 1, 0, 0, 0]),            #Criterion 7
    Problem(Class(3, 3, 2, 0, 5), [(1, 2), (1, 3)], [5, 0, 0, 0, 0]),            #Criterion 7
    Problem(Class(3, 3, 2, 1, 3), [(1, 2), (1, 3)], [0, 2, 1, 0, 0]),            #Criterion 8
    Problem(Class(3, 3, 2, 1, 3), [(1, 2), (1, 3)], [0, 1, 1, 1, 0]),            #Criterion 8
    Problem(Class(3, 3, 2, 1, 3), [(1, 2), (1, 3)], [0, 3, 0, 0, 0]),            #Criterion 8
    Problem(Class(3, 3, 2, 1, 3), [(1, 2), (1, 3)], [0, 2, 0, 1, 0]),            #Criterion 8
    Problem(Class(3, 3, 2, 1, 3), [(1, 2), (1, 3)], [1, 1, 1, 0, 0]),            #Criterion 8
    Problem(Class(3, 3, 2, 1, 3), [(1, 2), (1, 3)], [1, 2, 0, 0, 0]),            #Criterion 8
    Problem(Class(3, 3, 2, 1, 3), [(1, 2), (1, 3)], [1, 1, 0, 1, 0]),            #Criterion 8
    Problem(Class(3, 3, 2, 1, 3), [(1, 2), (1, 3)], [2, 1, 0, 0, 0]),            #Criterion 8
    Problem(Class(3, 3, 2, 1, 3), [(1, 2), (1, 3)], [3, 0, 0, 0, 0]),            #Criterion 8
    Problem(Class(3, 3, 2, 2, 1), [(1, 2), (1, 3)], [0, 1, 0, 0, 0]),            #Criterion 8
    Problem(Class(3, 3, 2, 2, 1), [(1, 2), (1, 3)], [1, 0, 0, 0, 0]),            #Criterion 8
    Problem(Class(3, 4, 2, 0, 2), [(1, 2), (1, 3)], [0, 0, 0, 2, 0, 0]),         #Criterion 8
    Problem(Class(3, 4, 2, 0, 2), [(1, 2), (1, 3)], [0, 1, 0, 1, 0, 0]),         #Criterion 8
    Problem(Class(3, 4, 2, 0, 2), [(1, 2), (1, 3)], [1, 0, 0, 1, 0, 0]),         #Criterion 8
    Problem(Class(3, 4, 2, 1, 0), [(1, 2), (1, 3)], [0, 0, 0, 0, 0, 0]),         #Criterion 8
    Problem(Class(4, 1, 0, 0, 12), Tuple{Int64, Int64}[], [12]),                 #Criterion 1
    Problem(Class(4, 1, 0, 1, 10), Tuple{Int64, Int64}[], [10]),                 #Criterion 1
    Problem(Class(4, 1, 0, 2, 8), Tuple{Int64, Int64}[], [8]),                   #Criterion 1
    Problem(Class(4, 3, 0, 0, 7), Tuple{Int64, Int64}[], [7, 0, 0]),             #Criterion 3
    Problem(Class(4, 3, 0, 0, 7), Tuple{Int64, Int64}[], [6, 1, 0]),             #Criterion 3
    Problem(Class(4, 3, 0, 0, 7), Tuple{Int64, Int64}[], [5, 2, 0]),             #Criterion 3
    Problem(Class(4, 3, 0, 0, 7), Tuple{Int64, Int64}[], [5, 1, 1]),             #Criterion 3
    Problem(Class(4, 3, 0, 1, 5), Tuple{Int64, Int64}[], [5, 0, 0]),             #Criterion 3
    Problem(Class(4, 3, 0, 1, 5), Tuple{Int64, Int64}[], [4, 1, 0]),
    Problem(Class(4, 2, 1, 0, 8), [(1, 2)], [8, 0, 0]),                          #Criterion 2
    Problem(Class(4, 2, 1, 0, 8), [(1, 2)], [7, 1, 0]),                          #Criterion 2
    Problem(Class(4, 2, 1, 0, 8), [(1, 2)], [6, 2, 0]),                          #Criterion 2
    Problem(Class(4, 2, 1, 0, 8), [(1, 2)], [6, 1, 1]),                          #Criterion 2
    Problem(Class(4, 2, 1, 1, 6), [(1, 2)], [6, 0, 0]),                          #Criterion 2
    Problem(Class(4, 2, 1, 1, 6), [(1, 2)], [5, 1, 0]),
    Problem(Class(4, 4, 1, 0, 3), [(1, 2)], [0, 0, 3, 0, 0]),                    #Criterion 6
    Problem(Class(4, 4, 1, 0, 3), [(1, 2)], [0, 0, 2, 1, 0]),                    #Criterion 6
    Problem(Class(4, 4, 1, 0, 3), [(1, 2)], [1, 0, 2, 0, 0]),                    #Criterion 6
    Problem(Class(4, 4, 1, 1, 1), [(1, 2)], [0, 0, 1, 0, 0]),
    Problem(Class(4, 3, 2, 0, 4), [(1, 2), (1, 3)], [0, 3, 1, 0, 0]),            #Criterion 5
    Problem(Class(4, 3, 2, 0, 4), [(1, 2), (1, 3)], [0, 4, 0, 0, 0]),            #Criterion 5
    Problem(Class(4, 3, 2, 0, 4), [(1, 2), (1, 3)], [0, 3, 0, 1, 0]),            #Criterion 5
    Problem(Class(4, 3, 2, 0, 4), [(1, 2), (1, 3)], [1, 3, 0, 0, 0]),            #Criterion 5
    Problem(Class(4, 3, 2, 0, 4), [(1, 2), (1, 3)], [3, 1, 0, 0, 0]),            #Criterion 7
    Problem(Class(4, 3, 2, 0, 4), [(1, 2), (1, 3)], [4, 0, 0, 0, 0]),            #Criterion 7
    Problem(Class(4, 3, 2, 1, 2), [(1, 2), (1, 3)], [0, 1, 1, 0, 0]),            #Criterion 8
    Problem(Class(4, 3, 2, 1, 2), [(1, 2), (1, 3)], [0, 2, 0, 0, 0]),            #Criterion 8
    Problem(Class(4, 3, 2, 1, 2), [(1, 2), (1, 3)], [0, 1, 0, 1, 0]),            #Criterion 8
    Problem(Class(4, 3, 2, 1, 2), [(1, 2), (1, 3)], [1, 1, 0, 0, 0]),            #Criterion 8
    Problem(Class(4, 3, 2, 1, 2), [(1, 2), (1, 3)], [2, 0, 0, 0, 0]),            #Criterion 8
    Problem(Class(4, 3, 2, 2, 0), [(1, 2), (1, 3)], [0, 0, 0, 0, 0]),            #Criterion 8
    Problem(Class(5, 1, 0, 0, 11), Tuple{Int64, Int64}[], [11]),                 #Criterion 1
    Problem(Class(5, 1, 0, 1, 9), Tuple{Int64, Int64}[], [9]),                   #Criterion 1
    Problem(Class(5, 1, 0, 2, 7), Tuple{Int64, Int64}[], [7]),                   #Criterion 1
    Problem(Class(5, 4, 0, 0, 4), Tuple{Int64, Int64}[], [4, 0, 0, 0]),          #Criterion 4
    Problem(Class(5, 4, 0, 0, 4), Tuple{Int64, Int64}[], [3, 1, 0, 0]),          #Criterion 4
    Problem(Class(5, 4, 0, 1, 2), Tuple{Int64, Int64}[], [2, 0, 0, 0]),
    Problem(Class(5, 3, 1, 0, 5), [(1, 2)], [0, 0, 5, 0]),                       #Criterion 5
    Problem(Class(5, 3, 1, 0, 5), [(1, 2)], [1, 0, 4, 0]),                       #Criterion 5
    Problem(Class(5, 3, 1, 0, 5), [(1, 2)], [2, 0, 3, 0]),                       #Criterion 5
    Problem(Class(5, 3, 1, 0, 5), [(1, 2)], [1, 1, 3, 0]),                       #Criterion 5
    Problem(Class(5, 3, 1, 0, 5), [(1, 2)], [4, 0, 1, 0]),                       #Criterion 3
    Problem(Class(5, 3, 1, 0, 5), [(1, 2)], [5, 0, 0, 0]),                       #Criterion 3
    Problem(Class(5, 3, 1, 0, 5), [(1, 2)], [4, 1, 0, 0]),                       #Criterion 3
    Problem(Class(5, 3, 1, 1, 3), [(1, 2)], [0, 0, 3, 0]),                       #Criterion 5
    Problem(Class(5, 3, 1, 1, 3), [(1, 2)], [1, 0, 2, 0]),
    Problem(Class(5, 3, 1, 1, 3), [(1, 2)], [3, 0, 0, 0]),
    Problem(Class(5, 3, 1, 2, 1), [(1, 2)], [0, 0, 1, 0]),
    Problem(Class(5, 3, 1, 2, 1), [(1, 2)], [1, 0, 0, 0]), 
    Problem(Class(6, 3, 0, 0, 6), Tuple{Int64, Int64}[], [6, 0, 0]),             #Criterion 3
    Problem(Class(6, 3, 0, 0, 6), Tuple{Int64, Int64}[], [5, 1, 0]),             #Criterion 3
    Problem(Class(6, 3, 0, 0, 6), Tuple{Int64, Int64}[], [4, 2, 0]),             #Criterion 3
    Problem(Class(6, 3, 0, 0, 6), Tuple{Int64, Int64}[], [4, 1, 1]),             #Criterion 3
    Problem(Class(6, 3, 0, 1, 4), Tuple{Int64, Int64}[], [4, 0, 0]),             #Criterion 3
    Problem(Class(6, 3, 0, 1, 4), Tuple{Int64, Int64}[], [3, 1, 0]),
    Problem(Class(6, 3, 0, 3, 0), Tuple{Int64, Int64}[], [0, 0, 0]),
    Problem(Class(6, 2, 1, 0, 7), [(1, 2)], [7, 0, 0]),                          #Criterion 2
    Problem(Class(6, 2, 1, 0, 7), [(1, 2)], [6, 1, 0]),                          #Criterion 2
    Problem(Class(6, 2, 1, 0, 7), [(1, 2)], [5, 2, 0]),                          #Criterion 2
    Problem(Class(6, 2, 1, 0, 7), [(1, 2)], [5, 1, 1]),                          #Criterion 2
    Problem(Class(6, 2, 1, 1, 5), [(1, 2)], [5, 0, 0]),                          #Criterion 2
    Problem(Class(6, 2, 1, 1, 5), [(1, 2)], [4, 1, 0]),
    Problem(Class(6, 2, 1, 3, 1), [(1, 2)], [1, 0, 0]),
    Problem(Class(7, 2, 0, 0, 8), Tuple{Int64, Int64}[], [8, 0]),                #Criterion 2
    Problem(Class(7, 2, 0, 0, 8), Tuple{Int64, Int64}[], [7, 1]),                #Criterion 2
    Problem(Class(7, 2, 0, 0, 8), Tuple{Int64, Int64}[], [6, 2]),                #Criterion 2
    Problem(Class(7, 2, 0, 0, 8), Tuple{Int64, Int64}[], [5, 3]),                #Criterion 2
    Problem(Class(7, 2, 0, 1, 6), Tuple{Int64, Int64}[], [6, 0]),                #Criterion 2
    Problem(Class(7, 2, 0, 1, 6), Tuple{Int64, Int64}[], [5, 1]),                #Criterion 2
    Problem(Class(7, 2, 0, 1, 6), Tuple{Int64, Int64}[], [4, 2]),
    Problem(Class(7, 2, 0, 2, 4), Tuple{Int64, Int64}[], [4, 0]),
    Problem(Class(8, 1, 0, 0, 10), Tuple{Int64, Int64}[], [10]),                 #Criterion 1
    Problem(Class(8, 1, 0, 1, 8), Tuple{Int64, Int64}[], [8]),                   #Criterion 1
    Problem(Class(8, 1, 0, 2, 6), Tuple{Int64, Int64}[], [6])                    #Criterion 1
   ]

###############################################################################
###############################################################################
# degree computations for p < 7
###############################################################################
###############################################################################

# For degree computations, we must assume that a problem is minimal.  We will
# use the list of minimal problems `minimal_problems' to compute the degrees.

###############################################################################
# helper functions
###############################################################################

# HomotopyContinuation.jl does not provide a way to convert from Oscar
# polynomials to their polynomials.  Hence, we write our own.
function evaluate(poly::MPolyRingElem{T}, vals::Vector{Variable}) where {T <: RingElem}
    @assert length(vals) == number_of_variables(parent(poly))

    res = Expression(0)
    for (cf, exp) in zip(coefficients(poly), exponent_vectors(poly))
        term = Expression(Int(cf))
        for ix in 1:length(vals)
            if !iszero(exp[ix])
                term *= vals[ix]^exp[ix]
            end
        end
        res += term
    end

    return res
end

###############################################################################
# main functions
###############################################################################

# Go from Problem to system of polynomials in terms of HomotopyContinuation.
# Uses vars[1:n] for iv, and vars[n+1:2*n] for the additional variables.
function system_of_polynomials(
        iv::ImageVarietyElem,
        vars::Vector{Variable},
        n::Int
    )
    entries = iv.entries

    n = length(entries)
    res = zeros(Expression, n)

    @assert length(entries) == n
    @assert number_of_variables(iv) == n

    for ix in 1:n
        f = denominator(entries[ix])
        g = numerator(entries[ix])
        fe = evaluate(f, vars[1:n])
        ge = evaluate(g, vars[1:n])
        res[ix] = fe - vars[n + ix] * ge
    end

    return res
end

# Assumes that pb is a minimal problem
function degree(pb::Problem; verify_solution::Bool = false, ix::Int = -1)
    iv = ImageVarietyElem(pb, ZZ)
    n = length(iv.entries)
    vars = (@var x[1:2*n])[1]
    system = system_of_polynomials(iv, vars, n)

    U = vars[1:n]
    V = vars[n+1:2*n]

    F = System(system, variables = U, parameters = V)
    F0 = System(system, variables = V, parameters = U)

    U0 = randn(ComplexF64, n)
    S0 = solve(F0, start_system = :total_degree, target_parameters = U0)
    V0 = solutions(S0)[1]

    res = monodromy_solve(F, U0, V0, show_progress = false)
    num_solutions = nsolutions(res)

    if verify_solution
        print("Verifying solution for $ix...")
        @assert ix > 0
        @assert num_solutions == degs[ix]
        @assert verify_solution_completeness(F, res, show_progress = false)
        println("Done!")
    end

    return num_solutions
end

function degrees(
        pbs::Vector{Problem} = minimal_problems;
        verify_solution::Bool = false, # NOTE: Setting to true is *very* slow
        verbose::Bool = false
    )
    degs = Vector{Int}(undef, length(pbs))

    for (ix, pb) in enumerate(pbs)
        if verbose
            print("Doing $ix/$(length(pbs))...")
        end
        deg = degree(pb, verify_solution = verify_solution, ix = ix)
        degs[ix] = deg
        if verbose
            println(" Done!")
        end
    end

    return degs
end

###############################################################################
# degrees
###############################################################################

# result of running `degrees'
degs = [36, 6, 23, 23, 15, 4, 6, 16, 4, 12, 16, 2, 9, 15, 17, 9, 12, 13, 8, 9,
        7, 4, 4, 4, 10, 10, 12, 2, 7, 2, 7, 10, 11, 2, 5, 7, 8, 9, 6, 6, 6, 3,
        4, 4, 4, 4, 10, 10, 10, 10, 2, 7, 10, 2, 7, 10, 10, 11, 2, 5, 5, 5, 5,
        5, 5, 2, 2, 2, 2, 1, 1, 1, 2, 5, 2, 5, 6, 5, 7, 3, 5, 5, 6, 3, 4, 3, 2,
        2, 2, 2, 2, 5, 5, 5, 5, 2, 5, 6, 5, 6, 6, 2, 5, 2, 5, 5, 5, 1, 1, 2, 2,
        2, 3, 3, 3, 3, 3, 4, 4, 4, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 2,
        1, 2, 3, 3, 3, 2, 3, 3, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2,
        25, 30, 12, 2, 2, 8, 10, 5, 6, 10, 4, 6, 7, 3, 2, 9, 2, 9, 9, 10, 5,
        10, 5, 10, 11, 3, 3, 3, 3, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 3, 1, 1, 1,
        1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 35, 20, 3, 4, 7, 3, 2, 2, 2, 2, 4, 6, 6,
        4, 4, 5, 1, 1, 2, 2, 3, 5, 12, 5, 8, 3, 4, 5, 5, 10, 10, 7, 7, 10, 1,
        1, 1, 3, 10, 9, 20, 6, 9, 3, 10, 38, 8, 114]

@assert length(degs) == length(minimal_problems)
pb_degs = [(minimal_problems[ix], degs[ix]) for ix in 1:length(degs)]

###############################################################################
###############################################################################
# minimal problems for p = 7
###############################################################################
###############################################################################

###############################################################################
# candidate problems
###############################################################################

# Take mlim = 10, just so we have at least one more view than 9.
mlim = 10
candidate_problems_7pts = Problem[]

for m in 2:mlim
    # Recall that problems containing four points on a line or six points on a
    # plane are non-minimal.  Hence, the remaining problems are the following.
    if m == 2
        push!(candidate_problems_7pts, Problem(Class(m, 7, 0, 0, 0), Tuple{Int, Int}[], Int[]))
        push!(candidate_problems_7pts, Problem(Class(m, 6, 1, 0, 0), [(1, 2)], Int[]))
        push!(candidate_problems_7pts, Problem(Class(m, 5, 2, 0, 0), [(1, 2), (2, 3)], Int[])) # chain
        push!(candidate_problems_7pts, Problem(Class(m, 5, 2, 0, 0), [(1, 2), (3, 4)], Int[])) # two groups
    else
        @assert !is_balanced(m, 7, 0, 0, 0)
        @assert !is_balanced(m, 6, 1, 0, 0)
        @assert !is_balanced(m, 5, 2, 0, 0)
    end
    push!(candidate_problems_7pts, Problem(Class(m, 4, 3, 0, 0), [(1, 2), (2, 3), (3, 4)], Int[])) # path/chain
    push!(candidate_problems_7pts, Problem(Class(m, 4, 3, 0, 0), [(1, 2), (2, 3), (2, 4)], Int[])) # star
end

###############################################################################
# minimal problems
###############################################################################

# Run this function to assert that all these candidate problems are minimal.
function assert_candidate_problems_7pts_is_minimal()
    @assert filter(x -> is_minimal(x), candidate_problems_7pts) == candidate_problems_7pts
end

minimal_problems_7pts = candidate_problems_7pts

###############################################################################
# degrees
###############################################################################

degs_7pts = [3, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

@assert length(degs_7pts) == length(minimal_problems_7pts)
pb_degs_7pts = [(minimal_problems_7pts[ix], degs_7pts[ix]) for ix in 1:length(degs_7pts)]

# Run this function to assert that the degrees here are correct (according to
# theory presented in paper).
function assert_degs_7pts_is_correct()
    @assert degrees(minimal_problems_7pts) == degs_7pts

    # Minimal problem with pf = 7
    pb_degs_pf7 = filter(x -> _pf(x[1]) == 7, pb_degs_7pts)

    # Assert that this problem has degree 3
    @assert length(pb_degs_pf7) == 1
    @assert all(x -> x[2] == 3, pb_degs_pf7)

    # Minimal problem with pf = 6
    pb_degs_pf6 = filter(x -> _pf(x[1]) == 6, pb_degs_7pts)
    # Assert that this problem has degree 2
    @assert length(pb_degs_pf6) == 1
    @assert all(x -> x[2] == 2, pb_degs_pf6)

    # Minimal problem with pf = 5 and one group of dependent points
    pb_degs_pf5_1 = filter(x -> _pf(x[1]) == 5 && x[1].deps == [(1, 2), (2, 3)], pb_degs_7pts)
    # Assert that this problem has degree 1
    @assert length(pb_degs_pf5_1) == 1
    @assert all(x -> x[2] == 1, pb_degs_pf5_1)

    # Minimal problem with pf = 5 and two groups of dependent points
    pb_degs_pf5_2 = filter(x -> _pf(x[1]) == 5 && x[1].deps == [(1, 2), (3, 4)], pb_degs_7pts)
    # Assert that this problem has degree 2
    @assert length(pb_degs_pf5_2) == 1
    @assert all(x -> x[2] == 2, pb_degs_pf5_2)

    # Minimal problems with pf = 4
    pb_degs_pf4 = filter(x -> _pf(x[1]) == 4, pb_degs_7pts)
    # Assert that these problems complete all problems, and that all of them
    # have degree 1
    @assert length(pb_degs_pf4) == (length(minimal_problems_7pts)
                                    - length(pb_degs_pf7)
                                    - length(pb_degs_pf6)
                                    - length(pb_degs_pf5_1)
                                    - length(pb_degs_pf5_2))
    @assert all(x -> x[2] == 1, pb_degs_pf4)
end
