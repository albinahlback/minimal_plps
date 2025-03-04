#=  example_4-12.jl:  Code for running Example 4.12
    Copyright (C) 2025  Kim Kiehn

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

using Oscar

p=next_prime(100000)
Fp=GF(p)



m=3
pf=1
pd=[]
lf=4
la=[7] # for each point there is a number of lines attached to it

# C' in 4.12 has 7 variables and the subproblem does not contain the free
# lines, the point and the first 4 adjacent lines are normalised
numvars1=7*m+3*(pf-1)+2*(la[1]-4)

K, vars=polynomial_ring(Fp, numvars1)

fps=[[K(1),K(0),K(0), K(0)]] # We have only one point which is normalised.

als=Vector{Vector{typeof(K(1))}}() 
# The first four lines are normalised.
push!(als,[K(0),K(1),K(0),K(0)])
push!(als,[K(0),K(0),K(1),K(0)])
push!(als,[K(0),K(0),K(0),K(1)])
push!(als,[K(0),K(1),K(1),K(1)])

for i in 1: 3
    push!(als, [K(0), K(vars[(2*i-1)]), K(vars[(2*i)]), K(1)  ])  # the remaining three lines are stored by one additional point (0,x,y,1) on it.
end 
C=[]
for i in 1: m
    push!(C, K[1 1 1 1; K(vars[7*i]) K(vars[7*i+1]) K(vars[7*i+2]) K(vars[7*i+3]); K(vars[7*i+4]) K(vars[7*i+5]) 1 K(vars[7*i+6])]) # Set up cameras in C'
end


equations=Vector{typeof(vars[1])}() 
denominators=Vector{typeof(vars[1])}() 
for j in 1:m
    for i in 1:pf
        image= C[j]* fps[i]
        push!(equations, image[1]-rand(Fp,1)[1]*image[3])
        push!(equations, image[2]-rand(Fp,1)[1]*image[3])
        push!(denominators, image[3])
    end 
end

# The main code uses here minors to eliminate the variables as it is also done
# for free lines below.
for j in 1:m
    for i in 1:la[1]
        im2=C[j]*fps[1] # line is attached to p1
        im1=C[j]*als[i] # lines has a second point stored in als
        t=im1[1]//(im1[1]-im1[3]*im2[1]//im2[3])

        point= (K(1)-t)*im1[2]//im1[3]+ t* im2[2]//im2[3]
        push!(equations, numerator(point)-rand(Fp,1)[1]*denominator(point))
        push!(denominators, denominator(point))
    end 
end 

I=ideal(equations)
J=ideal(denominators[16])
# Since the equations come from rational functions we have to ensure that the
# denominators are non-zero, taking one of them suffices in this case.
I=saturation(I,J)
deg1=degree(I)
println("The first part of the problem has degree ", degree(I))


# we reintroduce the stabilisers and normally one would need variables for the
# free lines but we eliminate those variables by using minors.
numvars2=(m-1)*4

# we create a new polynomial ring for the second problem
K, varias=polynomial_ring(Fp, numvars2)

# the variables of the first subproblem became now fixed values.
vars=rand(Fp, numvars1)


C=[]
for i in 1: m
    # initialise the cameras now with fixed values instead of variables
    push!(C, K[1 1 1 1; K(vars[7*i]) K(vars[7*i+1]) K(vars[7*i+2]) K(vars[7*i+3]); K(vars[7*i+4]) K(vars[7*i+5]) 1 K(vars[7*i+6])])
end
for i in 2:m
    # reintroduce the variables from the stabilisers to the cameras except for
    # the fiirst one to fix PGL4 action
    C[i]=C[i]*K[K(varias[(i-1)*4-3]) K(varias[(i-1)*4-2]) K(varias[(i-1)*4-1]) K(varias[(i-1)*4]); 0 1 0 0; 0 0 1 0; 0 0 0 1]
end

equations=Vector{typeof(varias[1])}() 



for i in 1:lf
    lM=K[0 0 0; 0 0 0; 0 0 0; 0 0 0]
    for j in 1:m
        lj=K[rand(Fp,1)[1]; rand(Fp,1)[1]; 1]
        preim=transpose(C[j])*lj
        for k in 1:4
            lM[k,j]=preim[k]
        end
    end
    threemino=minors(lM, 3)
    for j in 1: size(threemino)[1]
        push!(equations, threemino[j])
    end
end 

I=ideal(equations)
println("The second part of the problem has degree ", degree(I))

print("So in total the degree is deg1*deg2=", deg1*degree(I))
