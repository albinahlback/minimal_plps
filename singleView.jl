using Oscar
using Primes 

p=nextprime(100000)



#dependent points can be described by the pair (p1,p2) of free points spanning the line it lies on

#adjacent lines are described by the point they touch as a number in 1:pf+pd e.g. one line at p1 and one at p2 are denoted by [1,2]

#To use the code write specify the problem here and comment out all blocks below that do not belong to your problem.
m=1
pf=0
pd=[]
lf=2
la=[]



numvars=3*pf+ size(pd)[1]+ (m)*11 + 2* size(la)[1]+ 4* lf-15
Fp=GF(p)
K, vars=rational_function_field(Fp, numvars+m*(pf+size(pd)[1]+size(la)[1]+lf))



#case 1: (pf=4)
#fps=[K[1;0;0;0], K[0;1;0;0], K[0;0;1;0], K[0;0;0;1]]
#C=[K[vars[1] vars[2] vars[3] vars[4]; vars[5] vars[6] vars[7] vars[8]; 1 1 1 1]]
#als=[]
#fls=[]

#case 2:(pf=3)
#fps=[K[1;0;0;0], K[0;1;0;0], K[0;0;1;0]]
#als=[K[0;0;0;1]]
#C=[K[vars[1] vars[2] vars[3] vars[4]; vars[5] vars[6] vars[7] 1; 1 1 1 1]]
#fls=[]

#case 3: (pf=2) lf=0
#fps=[K[1;0;0;0], K[0;1;0;0]]
#als=[K[0;0;1;0], K[0;0;0;1]]
#C=[K[vars[1] vars[2] vars[3] vars[4]; vars[5] vars[6] 1 -1; 1 1 1 1]]
#fls=[]

#case 4: (pf=2) lf=1
#fps=[K[1;0;0;0], K[0;1;0;0]]
#als=[]
#fls=[[K[0;0;1;0], K[0;0;0;1]]]
#C=[K[vars[1] vars[2] vars[3] vars[4]; vars[5] vars[6] 1 -1; 1 1 1 1]]

#case 5: (pf=1) lf=0
#fps=[K[1;0;0;0]]
#als=[K[0;1;0;0], K[0;0;1;0], K[0;0;0;1]]
#C=[K[vars[1] vars[2] vars[3] vars[4]; vars[5] 1 -1 1; 1 1 1 1]]
#fls=[]

#case 6: (pf=1) lf=1
#fps=[K[1;0;0;0]]
#als=[K[0;1;0;0]]
#fls=[[K[0;0;1;0], K[0;0;0;1]]]
#C=[K[vars[1] vars[2] vars[3] vars[4]; vars[5] 1 -1 1; 1 1 1 1]]

#case 7: (pf=0)
fps=[]
als=[]
fls=[[K[1;0;0;0], K[0;1;0;0]],[K[0;0;1;0], K[0;0;0;1]]]
C=[K[vars[1] vars[2] vars[3] vars[4]; -1 1 -1 1; 1 1 1 1]]

proj=Vector{typeof(K(1))}()
for j in 1:pf
    for i in 1:m
        im= C[i]* fps[j]
        push!(proj, im[1]/im[3])
        push!(proj, (im[2])/im[3])
    end 
end



for j in 1:size(pd)[1]
    for i in 1:m
        imdp= C[i]* dps[j]
        imfirst= C[i]* fps[(pd[j][1])]
        imsecond=C[i]*fps[(pd[j][2])]
        param= ((imdp[2]/imdp[3]) -(imfirst[2]/imfirst[3]))/((imsecond[2]/imsecond[3])-(imfirst[2]/imfirst[3]))
        push!(proj, param)
    end
end

function crossProd( im1, im2)
    return   [im1[2,1]*im2[3,1]-im2[2,1]*im1[3,1], im1[3,1]*im2[1,1]-im2[3,1]*im1[1,1], im1[1,1]*im2[2,1]-im2[1,1]*im1[2,1]]
end

for i in 1:size(la)[1] #The main code uses here minors to eliminate the variables as it is also done for free lines below.
    for j in 1:m
        im2=C[j]*fps[la[i]] #line is attached to p1
        im1=C[j]*als[i] #lines has a second point stored in als
        t=im1[1]//(im1[1]-im1[3]*im2[1]//im2[3])
        println(im1)
        point= (K(1)-t)*im1[2]//im1[3]+ t* im2[2]//im2[3]
        push!(proj, point)
    end 
end 
for i in 1:lf
    for j in 1:m
        im1=C[j]*fls[i][1]
        im2=C[j]*fls[i][2]
        cp=crossProd(im1, im2)
        push!(proj, cp[1]/cp[3])
        push!(proj, cp[2]/cp[3])
    end 
end

randpoint=rand(Fp, numvars+m*(pf+size(pd)[1]+size(la)[1]+lf))



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
if r==numvars
    println("minimal")
else
    println("non-minimal")
end

rpo=Vector{typeof(Fp(1))}()

for i in 1:size(proj)[1]
    num=numerator(proj[i])
    denom=denominator(proj[i])
    nv=num(randpoint...)
    dv=denom(randpoint...)
    push!(rpo, nv/dv)
end



function random_rational_vector(n::Int)
    return [QQ(rand(-1000:1000), rand(1:1000)) for _ in 1:n]
end



Y=random_rational_vector(numvars)



equations2=Vector{typeof(numerator(vars[1]))}() 

points=[]
for i in 1:pf
    pointi=[]    
    for j in 1:m
    
        im= C[j]* fps[i]
        #rp=[QQ(rand(-1000:1000), rand(1:1000)); QQ(rand(-1000:1000), rand(1:1000)); 1]
        rp=[rpo[2*(i-1)*m+2*j-1];rpo[(i-1)*m+2*j]; 1]
        push!(pointi, rp)
        push!(equations2,numerator( im[1])-rp[1]*numerator(im[3]))
        push!(equations2, numerator(im[2])-rp[2]*numerator(im[3]))
        push!(equations2, numerator(im[3]*vars[numvars+(i-1)*m+j]- K(1)))
    end 
    push!(points, pointi)
end
for i in 1:size(la)[1] #The main code uses here minors to eliminate the variables as it is also done for free lines below.
    for j in 1:m
        im2=C[j]*fps[la[i]] #line is attached to p1
        im1=C[j]*als[i] #lines has a second point stored in als
        t=im1[1]//(im1[1]-im1[3]*im2[1]//im2[3])

        point= (K(1)-t)*im1[2]//im1[3]+ t* im2[2]//im2[3]
        push!(equations2, numerator(point)-rand(Fp,1)[1]*denominator(point))
        push!(equations2, numerator(vars[numvars+m*(pf)+(i-1)*m+j])*denominator(point))
    end 
end 
for i in 1:lf
    for j in 1:m
        im1=C[j]*fls[i][1]
        im2=C[j]*fls[i][2]
        cp=[im1[2,1]*im2[3,1]-im2[2,1]*im1[3,1], im1[3,1]*im2[1,1]-im2[3,1]*im1[1,1], im1[1,1]*im2[2,1]-im2[1,1]*im1[2,1]]
        push!(equations2, numerator(cp[1]/cp[3])-rand(Fp,1)[1]*denominator(cp[1]/cp[3]))
        push!(equations2, numerator(cp[2]/cp[3])-rand(Fp,1)[1]*denominator(cp[2]/cp[3]))
        push!(equations2, numerator(vars[numvars+m*(pf+size(la)[1])+(i-1)*m+j])*denominator(cp[1]/cp[3]))
    end 
end

I=ideal(equations2)
di=dim(I)
deg=degree(I)
println("The dimension of the ideal is ", di)
println("The degree of the ideal is ", deg)
