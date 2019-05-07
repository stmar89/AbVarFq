/*
by Taylor Dupuy
   
THIS CODE COMPUTES THE SLOPE FILTRATION IN AN EXAMPLE. 
IT IS DONE FOR THE PURPOSES OF COMPUTING THE FROBENIUS BASE CHANGE/VERSHIEBUNG CHANGE OF AN ABELIAN VARIETY.

*/


P<x>:=PolynomialRing(Integers());
f:=x^6 - 4*x^5 + 16*x^4 - 53*x^3 + 128*x^2 - 256*x + 512;
A:=AssociativeAlgebra(f);
R:=Order([13*A.1+0*A.2+0*A.3+0*A.4+0*A.5+0*A.6,0*A.1+13*A.2+0*A.3+0*A.4+0*A.5+0*A.6,1*A.1+0*A.2+1*A.3+0*A.4+0*A.5+0*A.6,0*A.1+1*A.2+0*A.3+1*A.4+0*A.5+0*A.6,5*A.1+1*A.2+0*A.3+0*A.4+1*A.5+0*A.6,2*A.1+0*A.2+0*A.3+-3/8*A.4+-3/8*A.5+1/8*A.6]);
S:=Order([1*A.1+0*A.2+0*A.3+0*A.4+0*A.5+0*A.6,0*A.1+1*A.2+0*A.3+0*A.4+0*A.5+0*A.6,0*A.1+0*A.2+1*A.3+0*A.4+0*A.5+0*A.6,0*A.1+0*A.2+0*A.3+1*A.4+0*A.5+0*A.6,0*A.1+0*A.2+0*A.3+0*A.4+1*A.5+0*A.6,0*A.1+0*A.2+0*A.3+-3/8*A.4+-3/8*A.5+1/8*A.6]);
//phi_pos_elt:=7*A.1+-14*A.2+-68*A.3+5/8*A.4+53/8*A.5+41/8*A.6;
I1:=<ideal<R|[13*A.1+0*A.2+0*A.3+0*A.4+0*A.5+0*A.6,0*A.1+13*A.2+0*A.3+0*A.4+0*A.5+0*A.6,1*A.1+0*A.2+1*A.3+0*A.4+0*A.5+0*A.6,0*A.1+1*A.2+0*A.3+1*A.4+0*A.5+0*A.6,5*A.1+1*A.2+0*A.3+0*A.4+1*A.5+0*A.6,2*A.1+0*A.2+0*A.3+-3/8*A.4+-3/8*A.5+1/8*A.6]>,[1/403*A.1+-2/403*A.2+32009/35139*A.3+-106259/140556*A.4+2417/10812*A.5+-2999/140556*A.6],2>;
//I2:=<ideal<R|[291200*A.1+0*A.2+0*A.3+0*A.4+0*A.5+0*A.6,-43082/5*A.1+26/5*A.2+0*A.3+0*A.4+0*A.5+0*A.6,-89600*A.1+0*A.2+1452*A.3+0*A.4+0*A.5+0*A.6,-42284*A.1+12*A.2+720*A.3+12*A.4+0*A.5+0*A.6,-77142*A.1+6*A.2+-93*A.3+3*A.4+3*A.5+0*A.6,-70514*A.1+2*A.2+35646846/496229*A.3+9981351/3969832*A.4+4502703/3969832*A.5+3/3969832*A.6]>,[1/3610880*A.1+-1/1805440*A.2+10770059/5669092*A.3+-965324333/612261936*A.4+7319173/15699024*A.5+-2476843/55660176*A.6],2>;
F:=PrimitiveElement(A);
I := I1[1];


/*
THE FOLLOWING TAKES A FRACTIONAL IDEAL I (VIEWED AS A DELIGNE MODULE)
AND COMPUTES THE SUBSPACE WHERE THE FROBENIUS ACTS BY MULTIPLICATION BY q 
TIMES AN INVERTIBLE MATRIX.

-COMPUTES THE MATRIX OF FROBENIUS IS THE STORED BASIS
-REDUCES MODULO p (IT SAYS q CURRENTLY, BUT THIS DOESN'T MATTER)
-COMPUTES THE RATIONAL CANONICAL FORM (FINDS THE KERNEL MODULO p)
-THEN LIFTS THE KERNEL OF THIS MATRIX OF COLUME VECTORS TO THE INTEGERS

*/

beta := ZBasis(I);
FM := Matrix(Coordinates([F*z : z in beta],beta))
Fq := GF(q);
FMq := ChangeRing(FM,Fq);
R, T, D := RationalForm(FM2);
//T*FMq*T^-1 eq R 
NM := NullspaceMatrix(Transpose(R)); 
R*Transpose(NullspaceMatrix(Transpose(R)));
NMlift := T^-1*NM; // FM2*NM1
NMlift := ChangeRing(NM1,Integers()); 

/*
THE FOLLOWING FUNCTION TAKES THE COLUMN VECTORS REPRESENTING THE NULL SPACE OF 
THE FROBENIUS MATRIX MODULO P AND STORES THEM BACK AS ELEMENT OF I
*/

function IElements(entries_in_column_vectors, I);
//A FUNCTION THAT CONVERTS FROM FREE MODULE COORDINATES BACK INTO
//THE PRESENATION WE ARE USING
//I THINK THIS WORKS BUT IT NEEDS TO BE TESTED
//    coeffs := entries_in_column_vectors;
/c is the length of the column vector
	beta := ZBasis(I);
	elements := [ &+[coeffs[j][i]*beta[i] i in [1..6]] : j in [1..c]];
	return elements;
end function;

/*
THE FOLLOWING TAKES PERFORMS THE ABOVE FUNCTION BY HAND THEN COMPUTES 1/p TIMES THE RESULT. 

*/

coeffs := Transpose(NMlift);
elements := [ &+[coeffs[1][i]*beta[j] i in]] : j in [1..g]]
divided_elements := [(Algebra(I) ! x)/p : x in elements];
ideal<Order(I)|Generators(I) cat divided_elements >;

J:=ideal<Order(I)|Generators(I) cat divided_elements >;
// will return true I subset J;
// The quotient of this is the Kernel of Frobenius. 
