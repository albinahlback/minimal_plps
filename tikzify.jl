#=  tikzify.jl:  Draw point-line problems in TikZ
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

# NOTE: This file requires `minimal_plps.jl' to be loaded first.

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
    rand_factor = 0.5
    kx = 1
    for ix in 1:(pf + pd)
        if adjs[ix] == 0
            continue
        end

        n = adjs[ix]
        for jx in 1:n
            las[kx] = (jx + rand_factor * rand() + 0.10) / n
            kx += 1
        end
    end

    return ProblemInstance(pfs, pds, lfs, las)
end

function tikz_init(scale::Float64 = 1.0)
    return "\\begin{tikzpicture}[scale=$scale]\n"
end

function tikz_fin()
    return "\\end{tikzpicture}%\n"
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

function tikz_caption(pb::Problem, deg::Int)
    return "\\node[below] at (.5, 0) {\\scriptsize\$($(_pf(pb)){,}$(_pd(pb)){,}$(_lf(pb)){,}$(_la(pb)))\$, \$\\pmb{$deg}\$};\n"
end

function do_tikz(pb::Problem, deg::Int; scale::Float64 = 1.4)
    ip = generate_instance_2d(pb)

    str = tikz_init(scale)

    str = str * tikz_define_coordinates(pb, ip)
    str = str * tikz_draw(pb)
    str = str * tikz_caption(pb, deg)

    str = str * tikz_fin()

    return str
end

function ascii_deps(deps::Vector{Tuple{Int, Int}})
    str = ""
    for ix in 1:length(deps)
        str *= "-$(deps[ix][1]).$(deps[ix][2])"
    end
    return str
end

function ascii_adjs(adjs::Vector{Int})
    str = ""
    for ix in 1:length(adjs)
        str *= "-$(adjs[ix])"
    end
    return str
end

function _filename(pb::Problem)
    m, pf, pd, lf, la = _m(pb), _pf(pb), _pd(pb), _lf(pb), _la(pb)
    str = "fig"
    str *= "_m$(m)_pf$(pf)"
    str *= "_pd$(pd)" * ascii_deps(pb.deps)
    str *= "_lf$(lf)"
    str *= "_la$(la)" * ascii_adjs(pb.adjs)
    str *= ".tex"
    return str
end

function write_tikz(pb_deg::Tuple{Problem, Int}; scale::Float64 = 1.4, prefix::String = "./")
    pb, deg = pb_deg
    filename = prefix * "/" * _filename(pb)
    str = do_tikz(pb, deg, scale = scale)

    open(filename, "w") do file
        write(file, str)
    end
end

function write_all_tikz(; scale::Float64 = 1.4, prefix::String = "./")
    for pb_deg in pb_degs
        write_tikz(pb_deg, scale = scale, prefix = prefix)
    end
end

_table_top = raw"\begin{table*}[h!]
\setlength\tabcolsep{0pt}%
\centering
\renewcommand\arraystretch{0.0}%
\begin{tabular}{|@{\hspace{5pt}}c@{\hspace{5pt}}|*{9}{>{\centering\arraybackslash}p{5.10em}}|}
\hline
  $m$ & \multicolumn{9}{c|}{$(p^f,p^d,l^f,l^a)$, algebraic degree\vphantom{\raisebox{-4pt}{a}\rule{0pt}{10pt}}}
\\\hline
"

_table_bottom = raw"\\\hline
\end{tabular}%
\caption{Minimal problems with their associated degree.}%
\end{table*}
"

_table_firstline_fixup = raw"\rule{0pt}{5.6em}"
_table_m(m::Int, line::Int) = "\\raisebox{$(((m == 3 && line < 12) || m == 5) ? "3" : (m >= 7) ? "2.7" : "0")em}{\$$m\$}\n"
_table_hline = "\\hline\n"

function _table_line(m::Int, line::Int)
    if m == 3
        if line == 1
            return _table_top
        elseif line == 6
            return _table_m(m, line)
        elseif line == 12
            return _table_bottom * "\n" * _table_top
        elseif line == 16
            return _table_m(m, line)
        else
            return ""
        end
    elseif m == 4
        if line == 1
            return _table_top
        elseif line == 3
            return _table_m(m, line)
        else
            return ""
        end
    elseif m == 5
        if line == 1
            return _table_top
        elseif line == 2
            return _table_m(m, line)
        else
            return ""
        end
    elseif m == 6
        if line == 1
            return "\\\\\n" * _table_hline * _table_m(m, line)
        else
            return ""
        end
    elseif m == 7
        if line == 1
            return "\\\\\n" * _table_hline * _table_m(m, line)
        else
            return ""
        end
    elseif m == 8
        if line == 1
            return "\\\\\n" * _table_hline * _table_m(m, line)
        else
            return ""
        end
    elseif m == 9
        if line == 1
            return "\\\\\n" * _table_hline * _table_m(m, line)
        else
            return ""
        end
    else
        error()
    end
end

function _table_line_is_fin(m::Int, line::Int)
    if m == 0
        return false # for first entry into write_tables
    elseif m == 3
        return line == 21
    elseif m == 4
        return line == 6
    elseif m == 5
        return false
    elseif m == 6
        return false
    elseif m == 7
        return false
    elseif m == 8
        return false
    elseif m == 9
        return true
    else
        error()
    end
end

line_width = 9

# NOTE: Semi-hardcoded, but nice to have for re-rendering pictures
function write_tables(filename::String)
    open(filename, "w") do file
        line = 0
        old_m = 0
        mx = 0
        for pb_deg in pb_degs
            pb, _ = pb_deg
            m = _m(pb)
            if old_m != m
                while mx % line_width != 0
                    mx += 1
                    write(file, "&\n")
                end
                if _table_line_is_fin(old_m, line)
                    write(file, _table_bottom * "\n")
                end
                old_m = m
                line = 0
            end
            
            figfilename = _filename(pb)
            str = ""

            if mx % line_width == 0
                line += 1
                if line != 1 && line != 12
                    str *= "\\\\\n"
                end
                str *= _table_line(m, line)
            end

            str *= "& \\input{$figfilename}"
            if (line == 1 || (m == 3 && line == 12)) && mx % line_width == 0
                str *= _table_firstline_fixup
            end
            str *= "\n"

            write(file, str)
            mx += 1
        end
        write(file, _table_bottom)
    end
end
