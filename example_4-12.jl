#=  example_4-12.jl:  Code for running Example 4.12
    Copyright (C) 2025  REDACTED

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
import AbstractAlgebra: rational_function_field, QQ, coefficients, exponent_vectors
import Oscar: next_prime
using HomotopyContinuation

p = next_prime(100000)

#dependent points can be described by the pair (p1,p2) of free points spanning the line it lies on

#adjacent lines are described by the point they touch as a number in 1:pf+pd
m=3
pf=0
pd=[]
lf=4
la=[]

function random_rational_vector(n::Int)
    return [QQ(rand(-1000:1000), rand(1:1000)) for _ in 1:n]
end

numvars=(m-1)*4+lf*4
#numvars=3*pf+ size(pd)[1]+ 2* size(la)[1]+ 4* lf+ 7*m-11
numvarias=27
#Fp=GF(p)
#second set of variables only for monodromy
#P, vars= polynomial_ring(QQ,numvars)
#K= fraction_field(P)
#K, vars=rational_function_field(QQ, 2*numvars)
K, varias=rational_function_field(QQ, 2*numvars)
vars=random_rational_vector(numvarias)

fps=Vector{Vector{typeof(K(vars[1]))}}()
for i in 1:pf
    push!(fps, [K(1),K(0),K(0), K(0)])
end
#pd:= pf_1+ t^d pf_2
dps=Vector{Vector{typeof(K(vars[1]))}}()
for i in 1:size(pd)[1]
    push!(dps, [(K(1)- K(vars[(3*pf+i)]))*fps[(pd[i][1])][1] + K(vars[(3*pf+i)])*fps[(pd[i][2])][1],(K(1)- K(vars[(3*pf+i)]))*fps[(pd[i][1])][2] + K(vars[(3*pf+i)])*fps[(pd[i][2])][2], (K(1)- K(vars[(3*pf+i)]))*fps[(pd[i][1])][3] + K(vars[(3*pf+i)])*fps[(pd[i][2])][3], K(1) ])
end
fls=Vector{Vector{Vector{typeof(K(1))}}}()  #  store line by two points (0,x,y,1) and (u,0,w,1)
for i in 1:lf
    push!(fls, [[K(0), K(varias[(4*i-3)]), K(varias[( 4*i-2)]), K(1)],[K(varias[(4*i-1)]), K(0), K(varias[(4*i)]), K(1)]])
end
als=Vector{Vector{typeof(K(1))}}() # store one additional point (0,x,y,1)
push!(als,[K(0),K(1),K(0),K(0)])
push!(als,[K(0),K(0),K(1),K(0)])
push!(als,[K(0),K(0),K(0),K(1)])
push!(als,[K(0),K(1),K(1),K(1)])
for i in 1: (size(la)[1]-4)
    push!(als, [K(0), K(vars[(2*i-1)]), K(vars[(2*i)]), K(1)  ])
end 
C=[]
for i in 1: m
    push!(C, K[1 1 1 1; K(vars[7*i]) K(vars[7*i+1]) K(vars[7*i+2]) K(vars[7*i+3]); K(vars[7*i+4]) K(vars[7*i+5]) 1 K(vars[7*i+6])])
end
for i in 2:m
    C[i]=C[i]*K[K(varias[4*lf+(i-1)*4-3]) K(varias[4*lf+(i-1)*4-2]) K(varias[4*lf+(i-1)*4-1]) K(varias[4*lf+(i-1)*4]); 0 1 0 0; 0 0 1 0; 0 0 0 1]
end

proj=Vector{typeof(varias[1])}() 
for j in 1:m
    for i in 1:pf
        im= C[j]* fps[i]
        push!(proj, im[1]/im[3])
        push!(proj, im[2]/im[3])
    end 
end
for j in 1:m
    for i in 1:size(pd)[1]
        # map to the paramter t s.t. image is affine t combination of two points
        imdp= C[j]* dps[i]
        imfirst= C[j]* fps[(pd[i][1])]
        imsecond=C[j]*fps[(pd[i][2])]
        push!(proj, ((imdp[2]/imdp[3]) -(imfirst[2]/imfirst[3]))/((imsecond[2]/imsecond[3])-(imfirst[2]/imfirst[3])))
    end
end
for j in 1:m #map free line to cross product of images of points
    for i in 1:lf
        im1= C[j]*fls[i][1]
        im2=C[j]*fls[i][2]
        imcross=[im1[2]*im2[3]-im1[3]*im2[2], im1[3]*im2[1]-im1[1]*im2[3], im1[1]*im2[2]-im1[2]*im2[1]]
        push!(proj, imcross[1]/imcross[3])
        push!(proj, imcross[2]/imcross[3])
    end
end 
for j in 1:m
    for i in 1:size(la)[1]
        if la[i]<= pf
            im2=C[j]*fps[la[i]]
        else
            im2=C[j]*dps[la[i]-pf]
        end
        im1=C[j]*als[i] 
        t=im1[1]/(im1[1]-im1[3]*im2[1]/im2[3])
        push!(proj, (K(1)-t)*im1[2]/im1[3]+ t* im2[2]/im2[3])
    end 
end 



Y=random_rational_vector(numvars)

equations=Vector{typeof(numerator(proj[1]))}() 
for i in 1:numvars 
    #push!(equations, numerator(proj[i])-Y[i]*denominator(proj[i]))
    push!(equations, numerator(proj[i])-numerator(varias[numvars+i])*denominator(proj[i]))
end

#I=ideal(equations)
#degree(I)



@var x[1:(2*numvars)]
#eq1 = sum(c * prod(x[i]^e[i] for i in 1:numvars) for (c, e) in zip(AbstractAlgebra.coefficients(equations[1]), exponent_vectors(equations[1])));


system = []
for j in 1:numvars
    push!(system,sum(c * prod(x[i]^e[i] for i in 1:2*numvars) for (c, e) in zip(coefficients(equations[j]), exponent_vectors(equations[j])));)
end

#F=System(system)
#HomotopyContinuation.solve(F)


V=x[1:numvars]
U=x[numvars+1:2*numvars]

 

    #randpoint=rand(Fp, numvars)

F = System(system; variables = V, parameters = U)
V0 = randn(ComplexF64, numvars)
F0 = System(system; variables = U, parameters = V)
S0 = solve(F0, start_system = :total_degree, target_parameters = V0)
U0 = solutions(S0)[1]

SM = monodromy_solve(F, V0, U0)






#=
Jacp=Vector{Vector{typeof(Fp(1))}}() 
for i in 1:size(proj)[1]
    Jacrow=Vector{typeof(Fp(1))}() 
    for j in 1:numvars
        num=numerator(proj[i])
        denom=denominator(proj[i])
        numder= derivative(num, j)
        denomder= derivative(denom, j)
        nv=num(randpoint...)
        dv=denom(randpoint...)
        nvd=numder(randpoint...)
        dvd=denomder(randpoint...)
        if (dv==Fp(0))
            println("New point needs to be chosen")
            push!(Jacrow, Fp(0))
        else
            push!(Jacrow, (nvd*dv- dvd*nv)/(dv*dv) )
        end
    end
    push!(Jacp, Jacrow)
end
S=matrix_space(Fp, size(proj)[1], numvars)
Jacatrandpoint= S(vcat(Jacp...))
r=rank(Jacatrandpoint)
if  numvars==r
    println("Minimal")
else
    println("TryAgain")
end
=#
#=
function JacRational(Proj)
    JacRat=Vector{Vector{typeof(K(1))}}() 
    for i in 1:size(proj)[1]
        Jacrow=Vector{typeof(K(1))}() 
        for j in 1:numvars
            num=numerator(proj[i])
            denom=denominator(proj[i])
            numder= derivative(num, j)
            denomder= derivative(denom, j)
            push!(Jacrow, (K(numder)*K(denom)- K(denomder)*K(num))/(K(denom)*K(denom)) )
        end
        push!(JacRat, Jacrow)
    end
    return JacRat
end=#
