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
    show
import LinearAlgebra:
    norm
import AbstractAlgebra.Generic:
    FracField, FracFieldElem,
    MatSpace, MatSpaceElem
import AbstractAlgebra:
    matrix_space, polynomial_ring, fraction_field, residue_ring,
    base_ring,
    one, zero,
    is_one, is_zero,
    derivative,
    ncols, nrows,
    number_of_variables,
    lcm, is_invertible
import Oscar:
    Partition,
    ZZ,
    zzModMPolyRing, zzModMPolyRingElem,
    ZZMPolyRing, ZZMPolyRingElem
import Oscar:
    partitions, evaluate, det
import HomotopyContinuation: @var

###############################################################################
###############################################################################
# computing candidate problems
###############################################################################
###############################################################################

###############################################################################
# computing classes of point-line balanced problems for less than seven points
###############################################################################

# NOTE: Recall that (m, 4, 3, 0, 0) is always minimal, and that for m = 2 the
# line configuration is unrestricted.  Hence, we only compute the finite
# classes here, i.e. when 2 < m ≤ 9, and remove all case where
# (pf, pd) = (4, 3).

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

# Applying filter(x -> (_pf(x) + _pd(x) < 7), balanced_classes) results in the 123 classes of balanced problems 
# as claimed at the end of the proof of Lemma 3.3; compare Table 2

# We know that problems containing four points on a line or six points on a
# plane cannot be minimal.  Hence, remove classes that only contain such
# problems.
feasible_balanced_classes = filter(
    x -> !((_pf(x) ≤ 2 && _pd(x) ≥ 2) || (_pf(x) ≤ 3 && _pd(x) ≥ 3)),
    balanced_classes)

# We can settle all cases with pf + pd = 7 by hand, so we only care about the
# cases with less than seven points.
interesting_balanced_classes = filter(
    x -> (_pf(x) + _pd(x) < 7), feasible_balanced_classes)

###############################################################################
# computing classes of point-line balanced problems
###############################################################################

small_field = false
big_prime = UInt(0xffffffffffffffc5) # Biggest 64-bit prime

@static if small_field
    xMPolyRing = zzModMPolyRing
    xMPolyRingElem = zzModMPolyRingElem
else
    xMPolyRing = ZZMPolyRing
    xMPolyRingElem = ZZMPolyRingElem
end

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
# computing minimality of candidate problems
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

function polynomial_ring(cl::Class)
    syms = Symbol[]
    basering = (small_field) ? residue_ring(ZZ, big_prime)[1] : ZZ

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

    return polynomial_ring(basering, syms)
end

# C_{m} × X_{p, l, I}
struct CXElem
    pb::Problem
    R::xMPolyRing
    cms::Vector{MatSpaceElem{xMPolyRingElem}}
    pfs::Vector{MatSpaceElem{xMPolyRingElem}}
    pds::Vector{MatSpaceElem{xMPolyRingElem}}
    lfs::Vector{MatSpaceElem{xMPolyRingElem}}
    las::Vector{MatSpaceElem{xMPolyRingElem}}

    function CXElem(pb::Problem)
        m, pf, pd, lf, la = _m(pb), _pf(pb), _pd(pb), _lf(pb), _la(pb)
        deps = pb.deps
        adjs = pb.adjs

        R, gens = polynomial_ring(pb.cl)
        z0, o1 = zero(R), one(R)
        C = matrix_space(R, 3, 4) # camera space
        P = matrix_space(R, 4, 1) # point space
        L = matrix_space(R, 4, 2) # line space
        cms = MatSpaceElem{xMPolyRingElem}[]
        pfs = MatSpaceElem{xMPolyRingElem}[]
        pds = MatSpaceElem{xMPolyRingElem}[]
        lfs = MatSpaceElem{xMPolyRingElem}[]
        las = MatSpaceElem{xMPolyRingElem}[]

        # First camera on the form (1 0 0 0; 0 1 0 0; 0 0 1 0)
        c1 = zero(C)
        for ix in 1:3
            c1[ix, ix] = o1
        end
        push!(cms, c1)

        # Second camera on the form (0 0 0 1; 1 * * *; * * * *)
        c2 = zero(C)
        c2[1, 4] = o1
        c2[2, 1] = o1
        c2[2, 2:4] = gens[1:3]
        c2[3, 1:4] = gens[4:7]
        push!(cms, c2)

        new_gens = gens[8:end]

        # All other cameras on the form (1 * * *; * * * *; * * * *)
        for ix in 0:(m - 3)
            cx = zero(C)
            cx[1, 1] = o1
            cx[1, 2:4] = new_gens[(1 + 11 * ix):(3 + 11 * ix)]
            cx[2, 1:4] = new_gens[(4 + 11 * ix):(7 + 11 * ix)]
            cx[3, 1:4] = new_gens[(8 + 11 * ix):(11 + 11 * ix)]
            push!(cms, cx)
        end

        new_gens = new_gens[(1 + 11 * (m - 2)):end]

        # Free points on the form (*; *; *; 1)
        for ix in 0:(pf - 1)
            px = zero(P)
            px[1:3, 1] = new_gens[(1 + 3 * ix):(3 + 3 * ix)]
            px[4, 1] = o1
            push!(pfs, px)
        end

        new_gens = new_gens[(1 + 3 * pf):end]

        # Dependent points on the form t * p0 + (1 - t) * p1 where t is the
        # variable for the dependent point
        for ix in 1:pd
            t = new_gens[ix]
            px = t * pfs[deps[ix][1]] + (o1 - t) * pfs[deps[ix][2]]
            push!(pds, px)
        end

        new_gens = new_gens[(1 + pd):end]

        # Free lines on the form (* *; * *; 1 0; 0 1)
        for ix in 0:(lf - 1)
            lx = zero(L)
            lx[1, 1:2] = new_gens[(1 + 4 * ix):(2 + 4 * ix)]
            lx[2, 1:2] = new_gens[(3 + 4 * ix):(4 + 4 * ix)]
            lx[3, 1] = o1
            lx[4, 2] = o1
            push!(lfs, lx)
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
            push!(las, lx)
        end
        @assert is_zero(new_adjs)

        return new(pb, R, cms, pfs, pds, lfs, las)
    end
end

###############################################################################
# naïve representation of image variety
###############################################################################

# Naïve representation of Y_{p, l, I, m}
#
# Stored in camera-major form.
struct NaiveImageVarietyElem
    pb::Problem
    R::xMPolyRing
    pfs::Vector{MatSpaceElem{xMPolyRingElem}}
    pds::Vector{MatSpaceElem{xMPolyRingElem}}
    lfs::Vector{MatSpaceElem{xMPolyRingElem}}
    las::Vector{MatSpaceElem{xMPolyRingElem}}

    function NaiveImageVarietyElem(cx::CXElem)
        pb = cx.pb
        m, pf, pd, lf, la = _m(pb), _pf(pb), _pd(pb), _lf(pb), _la(pb)
        R = cx.R
        pfs = MatSpaceElem{xMPolyRingElem}[]
        pds = MatSpaceElem{xMPolyRingElem}[]
        lfs = MatSpaceElem{xMPolyRingElem}[]
        las = MatSpaceElem{xMPolyRingElem}[]

        for ix in 1:m
            # free points
            for jx in 1:pf
                push!(pfs, cx.cms[ix] * cx.pfs[jx])
            end

            # dep. points
            for jx in 1:pd
                push!(pds, cx.cms[ix] * cx.pds[jx])
            end

            # free lines
            for jx in 1:lf
                push!(lfs, cx.cms[ix] * cx.lfs[jx])
            end

            # adj. lines
            for jx in 1:la
                push!(las, cx.cms[ix] * cx.las[jx])
            end
        end

        return new(pb, R, pfs, pds, lfs, las)
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

struct ImageVarietyElem
    pb::Problem
    R::xMPolyRing
    K::FracField{xMPolyRingElem}
    entries::Vector{FracFieldElem{xMPolyRingElem}}

    function ImageVarietyElem(niv::NaiveImageVarietyElem)
        pb = niv.pb
        m, pf, pd, lf, la = _m(pb), _pf(pb), _pd(pb), _lf(pb), _la(pb)
        deps = pb.deps
        R = niv.R
        K = fraction_field(R)
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

        return new(pb, R, K, entries)
    end

    function ImageVarietyElem(pb::Problem)
        # Get the symbolic representation C_{m} × X_{p, l, I} of problem
        cx = CXElem(pb)

        # Map naïvely to images
        niv = NaiveImageVarietyElem(cx)

        return ImageVarietyElem(niv)
    end
end

class(iv::ImageVarietyElem) = iv.pb.cl
field(iv::ImageVarietyElem) = iv.K

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

jacobian(pb::Problem) = jacobian(ImageVarietyElem(pb))

# NOTE: This will destroy input
function similar_matrix(mat::MatSpaceElem{FracFieldElem{xMPolyRingElem}})
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
# numerical minimality check
###############################################################################

function is_minimal(pb::Problem; numevals::Int = 1000)
    # Get symbolical jacobian
    jac = jacobian(pb)
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
# minimality check for 2 cameras
###############################################################################   

# TODO

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
# and printed using the following function:
#=
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
=#

minimal_problems = [
    Problem(Class(3, 0, 0, 9, 0), Tuple{Int64, Int64}[], Int64[]),
    Problem(Class(3, 1, 0, 4, 7), Tuple{Int64, Int64}[], [7]),
    Problem(Class(3, 1, 0, 5, 5), Tuple{Int64, Int64}[], [5]),
    Problem(Class(3, 1, 0, 6, 3), Tuple{Int64, Int64}[], [3]),
    Problem(Class(3, 1, 0, 7, 1), Tuple{Int64, Int64}[], [1]),
    Problem(Class(3, 2, 0, 0, 12), Tuple{Int64, Int64}[], [6, 6]),
    Problem(Class(3, 2, 0, 1, 10), Tuple{Int64, Int64}[], [6, 4]),
    Problem(Class(3, 2, 0, 1, 10), Tuple{Int64, Int64}[], [5, 5]),
    Problem(Class(3, 2, 0, 2, 8), Tuple{Int64, Int64}[], [6, 2]),
    Problem(Class(3, 2, 0, 2, 8), Tuple{Int64, Int64}[], [5, 3]),
    Problem(Class(3, 2, 0, 2, 8), Tuple{Int64, Int64}[], [4, 4]),
    Problem(Class(3, 2, 0, 3, 6), Tuple{Int64, Int64}[], [6, 0]),
    Problem(Class(3, 2, 0, 3, 6), Tuple{Int64, Int64}[], [5, 1]),
    Problem(Class(3, 2, 0, 3, 6), Tuple{Int64, Int64}[], [4, 2]),
    Problem(Class(3, 2, 0, 3, 6), Tuple{Int64, Int64}[], [3, 3]),
    Problem(Class(3, 2, 0, 4, 4), Tuple{Int64, Int64}[], [4, 0]),
    Problem(Class(3, 2, 0, 4, 4), Tuple{Int64, Int64}[], [3, 1]),
    Problem(Class(3, 2, 0, 4, 4), Tuple{Int64, Int64}[], [2, 2]),
    Problem(Class(3, 2, 0, 5, 2), Tuple{Int64, Int64}[], [2, 0]),
    Problem(Class(3, 2, 0, 5, 2), Tuple{Int64, Int64}[], [1, 1]),
    Problem(Class(3, 2, 0, 6, 0), Tuple{Int64, Int64}[], [0, 0]),
    Problem(Class(3, 3, 0, 0, 9), Tuple{Int64, Int64}[], [5, 4, 0]),
    Problem(Class(3, 3, 0, 0, 9), Tuple{Int64, Int64}[], [5, 3, 1]),
    Problem(Class(3, 3, 0, 0, 9), Tuple{Int64, Int64}[], [5, 2, 2]),
    Problem(Class(3, 3, 0, 0, 9), Tuple{Int64, Int64}[], [4, 4, 1]),
    Problem(Class(3, 3, 0, 0, 9), Tuple{Int64, Int64}[], [4, 3, 2]),
    Problem(Class(3, 3, 0, 0, 9), Tuple{Int64, Int64}[], [3, 3, 3]),
    Problem(Class(3, 3, 0, 1, 7), Tuple{Int64, Int64}[], [5, 2, 0]),
    Problem(Class(3, 3, 0, 1, 7), Tuple{Int64, Int64}[], [4, 3, 0]),
    Problem(Class(3, 3, 0, 1, 7), Tuple{Int64, Int64}[], [5, 1, 1]),
    Problem(Class(3, 3, 0, 1, 7), Tuple{Int64, Int64}[], [4, 2, 1]),
    Problem(Class(3, 3, 0, 1, 7), Tuple{Int64, Int64}[], [3, 3, 1]),
    Problem(Class(3, 3, 0, 1, 7), Tuple{Int64, Int64}[], [3, 2, 2]),
    Problem(Class(3, 3, 0, 2, 5), Tuple{Int64, Int64}[], [5, 0, 0]),
    Problem(Class(3, 3, 0, 2, 5), Tuple{Int64, Int64}[], [4, 1, 0]),
    Problem(Class(3, 3, 0, 2, 5), Tuple{Int64, Int64}[], [3, 2, 0]),
    Problem(Class(3, 3, 0, 2, 5), Tuple{Int64, Int64}[], [3, 1, 1]),
    Problem(Class(3, 3, 0, 2, 5), Tuple{Int64, Int64}[], [2, 2, 1]),
    Problem(Class(3, 3, 0, 3, 3), Tuple{Int64, Int64}[], [3, 0, 0]),
    Problem(Class(3, 3, 0, 3, 3), Tuple{Int64, Int64}[], [2, 1, 0]),
    Problem(Class(3, 3, 0, 3, 3), Tuple{Int64, Int64}[], [1, 1, 1]),
    Problem(Class(3, 3, 0, 4, 1), Tuple{Int64, Int64}[], [1, 0, 0]),
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
    Problem(Class(3, 4, 0, 0, 6), Tuple{Int64, Int64}[], [4, 2, 0, 0]),
    Problem(Class(3, 4, 0, 0, 6), Tuple{Int64, Int64}[], [3, 3, 0, 0]),
    Problem(Class(3, 4, 0, 0, 6), Tuple{Int64, Int64}[], [4, 1, 1, 0]),
    Problem(Class(3, 4, 0, 0, 6), Tuple{Int64, Int64}[], [3, 2, 1, 0]),
    Problem(Class(3, 4, 0, 0, 6), Tuple{Int64, Int64}[], [2, 2, 2, 0]),
    Problem(Class(3, 4, 0, 0, 6), Tuple{Int64, Int64}[], [3, 1, 1, 1]),
    Problem(Class(3, 4, 0, 0, 6), Tuple{Int64, Int64}[], [2, 2, 1, 1]),
    Problem(Class(3, 4, 0, 1, 4), Tuple{Int64, Int64}[], [3, 1, 0, 0]),
    Problem(Class(3, 4, 0, 1, 4), Tuple{Int64, Int64}[], [2, 2, 0, 0]),
    Problem(Class(3, 4, 0, 1, 4), Tuple{Int64, Int64}[], [2, 1, 1, 0]),
    Problem(Class(3, 4, 0, 1, 4), Tuple{Int64, Int64}[], [1, 1, 1, 1]),
    Problem(Class(3, 4, 0, 2, 2), Tuple{Int64, Int64}[], [2, 0, 0, 0]),
    Problem(Class(3, 4, 0, 2, 2), Tuple{Int64, Int64}[], [1, 1, 0, 0]),
    Problem(Class(3, 4, 0, 3, 0), Tuple{Int64, Int64}[], [0, 0, 0, 0]),
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
    Problem(Class(3, 5, 0, 0, 3), Tuple{Int64, Int64}[], [3, 0, 0, 0, 0]),
    Problem(Class(3, 5, 0, 0, 3), Tuple{Int64, Int64}[], [2, 1, 0, 0, 0]),
    Problem(Class(3, 5, 0, 0, 3), Tuple{Int64, Int64}[], [1, 1, 1, 0, 0]),
    Problem(Class(3, 5, 0, 1, 1), Tuple{Int64, Int64}[], [1, 0, 0, 0, 0]),
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
    Problem(Class(3, 6, 0, 0, 0), Tuple{Int64, Int64}[], [0, 0, 0, 0, 0, 0]),
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
    Problem(Class(4, 1, 0, 3, 6), Tuple{Int64, Int64}[], [6]),
    Problem(Class(4, 1, 0, 4, 4), Tuple{Int64, Int64}[], [4]),
    Problem(Class(4, 1, 0, 5, 2), Tuple{Int64, Int64}[], [2]),
    Problem(Class(4, 1, 0, 6, 0), Tuple{Int64, Int64}[], [0]),
    Problem(Class(4, 3, 0, 0, 7), Tuple{Int64, Int64}[], [4, 3, 0]),
    Problem(Class(4, 3, 0, 0, 7), Tuple{Int64, Int64}[], [4, 2, 1]),
    Problem(Class(4, 3, 0, 0, 7), Tuple{Int64, Int64}[], [3, 3, 1]),
    Problem(Class(4, 3, 0, 0, 7), Tuple{Int64, Int64}[], [3, 2, 2]),
    Problem(Class(4, 3, 0, 1, 5), Tuple{Int64, Int64}[], [3, 2, 0]),
    Problem(Class(4, 3, 0, 1, 5), Tuple{Int64, Int64}[], [3, 1, 1]),
    Problem(Class(4, 3, 0, 1, 5), Tuple{Int64, Int64}[], [2, 2, 1]),
    Problem(Class(4, 3, 0, 2, 3), Tuple{Int64, Int64}[], [3, 0, 0]),
    Problem(Class(4, 3, 0, 2, 3), Tuple{Int64, Int64}[], [2, 1, 0]),
    Problem(Class(4, 3, 0, 2, 3), Tuple{Int64, Int64}[], [1, 1, 1]),
    Problem(Class(4, 3, 0, 3, 1), Tuple{Int64, Int64}[], [1, 0, 0]),
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
    Problem(Class(4, 5, 0, 0, 2), Tuple{Int64, Int64}[], [2, 0, 0, 0, 0]),
    Problem(Class(4, 5, 0, 0, 2), Tuple{Int64, Int64}[], [1, 1, 0, 0, 0]),
    Problem(Class(4, 5, 0, 1, 0), Tuple{Int64, Int64}[], [0, 0, 0, 0, 0]),
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
    Problem(Class(5, 1, 0, 3, 5), Tuple{Int64, Int64}[], [5]),
    Problem(Class(5, 1, 0, 4, 3), Tuple{Int64, Int64}[], [3]),
    Problem(Class(5, 1, 0, 5, 1), Tuple{Int64, Int64}[], [1]),
    Problem(Class(5, 4, 0, 0, 4), Tuple{Int64, Int64}[], [2, 2, 0, 0]),
    Problem(Class(5, 4, 0, 0, 4), Tuple{Int64, Int64}[], [2, 1, 1, 0]),
    Problem(Class(5, 4, 0, 0, 4), Tuple{Int64, Int64}[], [1, 1, 1, 1]),
    Problem(Class(5, 4, 0, 1, 2), Tuple{Int64, Int64}[], [1, 1, 0, 0]),
    Problem(Class(5, 4, 0, 2, 0), Tuple{Int64, Int64}[], [0, 0, 0, 0]),
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
    Problem(Class(6, 3, 0, 0, 6), Tuple{Int64, Int64}[], [3, 3, 0]),
    Problem(Class(6, 3, 0, 0, 6), Tuple{Int64, Int64}[], [3, 2, 1]),
    Problem(Class(6, 3, 0, 0, 6), Tuple{Int64, Int64}[], [2, 2, 2]),
    Problem(Class(6, 3, 0, 1, 4), Tuple{Int64, Int64}[], [2, 2, 0]),
    Problem(Class(6, 3, 0, 1, 4), Tuple{Int64, Int64}[], [2, 1, 1]),
    Problem(Class(6, 3, 0, 2, 2), Tuple{Int64, Int64}[], [2, 0, 0]),
    Problem(Class(6, 3, 0, 2, 2), Tuple{Int64, Int64}[], [1, 1, 0]),
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
    Problem(Class(7, 2, 0, 0, 8), Tuple{Int64, Int64}[], [4, 4]),
    Problem(Class(7, 2, 0, 1, 6), Tuple{Int64, Int64}[], [3, 3]),
    Problem(Class(7, 2, 0, 2, 4), Tuple{Int64, Int64}[], [3, 1]),
    Problem(Class(7, 2, 0, 2, 4), Tuple{Int64, Int64}[], [2, 2]),
    Problem(Class(7, 2, 0, 3, 2), Tuple{Int64, Int64}[], [2, 0]),
    Problem(Class(7, 2, 0, 3, 2), Tuple{Int64, Int64}[], [1, 1]),
    Problem(Class(7, 2, 0, 4, 0), Tuple{Int64, Int64}[], [0, 0]),
    Problem(Class(8, 1, 0, 3, 4), Tuple{Int64, Int64}[], [4]),
    Problem(Class(8, 1, 0, 4, 2), Tuple{Int64, Int64}[], [2]),
    Problem(Class(8, 1, 0, 5, 0), Tuple{Int64, Int64}[], [0]),
    Problem(Class(9, 0, 0, 6, 0), Tuple{Int64, Int64}[], Int64[])
   ]

###############################################################################
###############################################################################
# degree computations
###############################################################################
###############################################################################

# For degree computations, we must assume that a problem is minimal.  We will
# use the list of minimal problems `minimal_problems' to compute the degrees.

###############################################################################
###############################################################################
# generate nice TikZed 2D-pictures of problems
###############################################################################
###############################################################################

# NOTE: This section is very much non-optimized and can be tweaked further!
# Use at your own risk!

struct ProblemInstance
    pfs::Matrix{Float64}
    pds::Vector{Float64}
    lfs::Vector{Tuple{Vector{Float64}, Vector{Float64}}}
    las::Vector{Float64}
end

function distance_line_to_point(
        lf::Tuple{Vector{Float64}, Vector{Float64}},
        x0::Float64,
        y0::Float64
    )
    x1, y1 = lf[1]
    x2, y2 = lf[2]

    num = abs((y2 - y1) * x0 - (x2 - x1) * y0 + x2 * y1 - y2 * x1)
    den = sqrt((y2 - y1)^2 + (x2 - x1)^2)

    return num / den
end

function distance_line_to_point(
        lf::Tuple{Vector{Float64}, Vector{Float64}},
        p0::Vector{Float64}
    )
    return distance_line_to_point(lf, p0[1], p0[2])
end

function okay_distance_line_to_points(
        lf::Tuple{Vector{Float64}, Vector{Float64}},
        pfs::Matrix{Float64},
        pds::Vector{Float64},
        deps::Vector{Tuple{Int, Int}},
        threshold::Float64 = 0.07
    )
    pf = size(pfs, 2)
    pd = length(pds)

    for ix in 1:pf
        x0, y0 = pfs[:, ix]

        if distance_line_to_point(lf, x0, y0) < threshold
            return false
        end
    end

    for ix in 1:pd
        p0 = pfs[:, deps[ix][1]]
        p1 = pfs[:, deps[ix][2]]
        α = pds[ix]

        # NOTE: Be careful about the order here
        px = α * p0 + (1.0 - α) * p1

        if distance_line_to_point(lf, px) < threshold
            return false
        end
    end

    return true
end

function generate_instance_2d(pb::Problem)
    pf = _pf(pb)
    pd = _pd(pb)
    lf = _lf(pb)
    la = _la(pb)
    deps = pb.deps
    adjs = pb.adjs

    # free points distributed nicely
    γ = 0.45
    ϕ = 1 / 4
    pfs = Matrix{Float64}(undef, 2, pf)
    if pf == 0
    elseif pf == 1
        pfs[:, 1] = [0.5, 0.5]
    elseif pf == 2
        pfs = [0.2 0.8;
               0.2 0.8]
    elseif pf == 3
        pfs = [0.19 0.82 0.45;
               0.19 0.16 0.87]
    elseif pf == 4
        pfs = [0.275434 0.886218 0.608196 0.114101;
               0.814813 0.588540 0.162511 0.340228]
    elseif pf == 5
        pfs = [0.392723 0.207106 0.804027 0.131138 0.801207;
               0.910171 0.155910 0.750257 0.577976 0.252140]
    elseif pf == 6
        pfs = [0.739454  0.905580  0.103712  0.390290  0.534961  0.748622;
               0.162856  0.445577  0.406706  0.109134  0.568298  0.876420]
    elseif pf == 7
        pfs = [0.739454  0.905580  0.103712  0.390290  0.534961  0.748622  0.26;
               0.162856  0.445577  0.406706  0.109134  0.568298  0.876420  0.82]
    else
        error()
    end

    # dependent points in the middle
    pds = [0.5 for _ in 1:pd]

    # free lines
    lfs = [(Vector{Float64}(undef, 2), Vector{Float64}(undef, 2)) for _ in 1:lf]
    ix = 1
    while ix <= lf
        # We go from one side to another side
        rn = rand(1:4)
        if rn == 1
            # bottom
            copy!(lfs[ix][1], [0.1 + 0.8 * rand(), 0.0])
        elseif rn == 2
            # right
            copy!(lfs[ix][1], [1.0, 0.1 + 0.8 * rand()])
        elseif rn == 3
            # top
            copy!(lfs[ix][1], [0.1 + 0.8 * rand(), 1.0])
        else
            # left
            copy!(lfs[ix][1], [0.0, 0.1 + 0.8 * rand()])
        end

        sn = rn
        while sn == rn
            sn = rand(1:4)
        end

        while true
            if sn == 1
                # bottom
                copy!(lfs[ix][2], [0.1 + 0.8 * rand(), 0.0])
            elseif sn == 2
                # right
                copy!(lfs[ix][2], [1.0, 0.1 + 0.8 * rand()])
            elseif sn == 3
                # top
                copy!(lfs[ix][2], [0.1 + 0.8 * rand(), 1.0])
            else
                # left
                copy!(lfs[ix][2], [0.0, 0.1 + 0.8 * rand()])
            end

            # Ensure line is long enough
            if norm(lfs[ix][2] - lfs[ix][1]) > 0.8
                break
            end
        end

        # Ensure proper distance between this line and all points
        if okay_distance_line_to_points(lfs[ix], pfs, pds, deps)
            ix += 1
        end
    end

    # adjacent lines
    las = Vector{Float64}(undef, la)
    twiddle_factor = 1 / 14
    rand_factor = 1 / 32
    kx = 1
    for ix in 1:(pf + pd)
        if adjs[ix] == 0
            continue
        end

        n = adjs[ix]
        for jx in 1:n
            las[kx] = jx / n + twiddle_factor + rand_factor * rand()
            kx += 1
        end
    end

    return ProblemInstance(pfs, pds, lfs, las)
end

function tikz_init(scale::Float64 = 1.0)
    return "\\begin{tikzpicture}[scale=$scale]\n"
end

function tikz_fin()
    return "\\end{tikzpicture}\n"
end

function tikz_define_coordinate(name::String, ip::Vector{Float64})
    if length(ip) != 2
        error()
    end
    return raw"\coordinate (" * name * ") at (" * string(ip)[2:end-1] * ");\n"
end

function tikz_define_coordinate(name::String, p0::String, p1::String, sc::Float64; convex::Bool=true)
    if convex
        return raw"\coordinate (" * name * ") at (\${$sc}*($p0) + {$(1.0 - sc)}*($p1)\$);\n"
    else
        return raw"\coordinate (" * name * ") at (\$($p0) + {$sc}*($p1)\$);\n"
    end
end

# Given two points p0 and p1, return the endpoints of the set A such that
#
#       p0 + α * (p1 - p0)
#     = α * p1 + (1 - α) * p0
#     ∈ [0, 1]^2
#
# for all α ∈ A.
function boundary_points(p0::Vector{Float64}, p1::Vector{Float64}; p1_is_dir::Bool = false)
    if length(p0) != 2 || length(p1) != 2
        error("Dimension wrong")
    elseif !(0.0 ≤ p0[1] ≤ 1.0 && 0.0 ≤ p0[2] ≤ 1.0)
        error("p0 not in box, p0 = $p0")
    elseif !p1_is_dir && !(0.0 ≤ p1[1] ≤ 1.0 && 0.0 ≤ p1[2] ≤ 1.0)
        error("p1 not in box, p1 = $p1")
    elseif p1_is_dir && !(0.999 < norm(p1) < 1.001)
        error("size of pdir was unexpected")
    end

    # c defines the plane it is able to hit
    c = Vector{Float64}(undef, 2)
    alpha = Vector{Float64}(undef, 2)

    # Do upper bound of α first
    if p1_is_dir
        pdir = p1
    else
        pdir = p1 - p0
    end

    if 0.0 in pdir
        # Check for anomalies
        error("Anomaly")
    end

    for ix in 1:2
        c[ix] = (pdir[ix] > 0.0) ? 1.0 : 0.0
        alpha[ix] = (c[ix] - p0[ix]) / pdir[ix]
        if alpha[ix] < 0.0
            error("alpha[ix] < 0")
        end
    end

    alphamax = minimum(alpha)
    if alphamax < 0.0
        error("alphamax < 0")
    end

    # Now do lower bound of α
    pdir = -pdir

    for ix in 1:2
        c[ix] = (pdir[ix] > 0.0) ? 1.0 : 0.0
        alpha[ix] = (c[ix] - p0[ix]) / pdir[ix]
        if alpha[ix] < 0.0
            error("alpha[ix] < 0")
        end
    end

    alphamin = minimum(alpha)
    if alphamin < 0.0
        error("alphamin < 0")
    end

    return (-alphamin, alphamax)
end

function tikz_define_coordinates(pb::Problem, ip::ProblemInstance)
    pf = _pf(pb)
    pd = _pd(pb)
    lf = _lf(pb)
    la = _la(pb)
    deps = pb.deps
    adjs = pb.adjs
    pfs = ip.pfs
    pds = ip.pds
    lfs = ip.lfs
    las = ip.las

    str = ""

    # Define free points
    for ix in 1:pf
        str = str * tikz_define_coordinate("p_$(ix)", pfs[:, ix])
    end

    # Define dependent points
    for ix in 1:pd
        dp = deps[ix]
        # NOTE: Be careful about the order here
        str = str * tikz_define_coordinate("d_$(dp[1])_$(dp[2])",
                                           "p_$(dp[1])", "p_$(dp[2])",
                                           pds[ix])
    end

    # Define free lines
    for ix in 1:lf
        p0, p1 = lfs[ix]
        str = str * tikz_define_coordinate("lf_$(ix)_1", p0)
        str = str * tikz_define_coordinate("lf_$(ix)_2", p1)
    end

    # Define adjacent lines
    adjs = deepcopy(adjs)
    for ix in 1:la
        jx = 1
        while adjs[jx] == 0
            jx += 1
        end
        adjs[jx] -= 1

        if jx <= pf
            # free point
            p0 = pfs[:, jx]
            p0str = "p_$(jx)"
        else
            # dependent point
            dp = deps[jx - pf]
            sc = pds[jx - pf]
            p0 = sc * pfs[:, dp[1]] + (1.0 - sc) * pfs[:, dp[2]]
            p0str = "d_$(dp[1])_$(dp[2])"
        end

        θ = las[ix]
        p1 = [cospi(θ), sinpi(θ)]
        p1str = "_la_$(ix)"

        (α0, α1) = boundary_points(p0, p1, p1_is_dir = true)

        str = str * tikz_define_coordinate(p1str, p1)
        str = str * tikz_define_coordinate("la_$(ix)_1", p0str, p1str, α0, convex = false)
        str = str * tikz_define_coordinate("la_$(ix)_2", p0str, p1str, α1, convex = false)
    end
    if !iszero(adjs)
        error()
    end

    return str
end

function tikz_draw(pb::Problem;
        free_point_color::String = "red",
        dep_point_color::String = "cyan",
        dep_line_color::String = "gray",
        free_line_color::String = "violet",
        adj_line_color::String = "yellow"
    )

    pf = _pf(pb)
    pd = _pd(pb)
    lf = _lf(pb)
    la = _la(pb)
    deps = pb.deps
    adjs = pb.adjs

    str = ""

    # Draw dotted lines for dependent points
    for ix in 1:pd
        str = str * "\\draw[dotted, $dep_line_color] (p_$(deps[ix][1])) -- (p_$(deps[ix][2]));\n"
    end

    # Draw full lines for adjacent lines
    for ix in 1:la
        str = str * "\\draw[$adj_line_color] (la_$(ix)_1) -- (la_$(ix)_2);\n"
    end

    # Draw full lines for free lines
    for ix in 1:lf
        str = str * "\\draw[$free_line_color] (lf_$(ix)_1) -- (lf_$(ix)_2);\n"
    end

    # Draw dependent points
    for ix in 1:pd
        str = str * "\\filldraw[fill=$dep_point_color] (d_$(deps[ix][1])_$(deps[ix][2])) circle[radius=1pt];\n"
    end

    # Draw free points
    for ix in 1:pf
        str = str * "\\filldraw[fill=$free_point_color] (p_$(ix)) circle[radius=1pt];\n"
    end

    # Draw box
    str = str * "\\draw (0, 0) -- (1, 0) -- (1, 1) -- (0, 1) -- cycle;\n"

    return str
end

function do_tikz(pb::Problem; scale::Float64 = 1.0)
    ip = generate_instance_2d(pb)

    str = tikz_init(scale)

    str = str * tikz_define_coordinates(pb, ip)
    str = str * tikz_draw(pb)

    str = str * tikz_fin()

    return str
end

function _print_all_tikz(scale::Float64 = 1.0)
    str = ""
    for (ix, pb) in enumerate(candidate_problems)
        str *= do_tikz(pb, scale = scale)
    end
    print(str)
end
