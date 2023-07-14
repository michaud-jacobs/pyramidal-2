////////////////////////////////////////////////////////////////////////////////////////

// This code carries defines various functions for the paper
// "On power values of pyramidal numbers, II"

////////////////////////////////////////////////////////////////////////////////////////

// See end of this document for some further explanatory notes

////////////////////////////////////////////////////////////////////////////////////////

// +++ Local1 +++

// Tests to see if Ax^p-By^p = 1 has a solution using elementary congruences
// Tests using primes 1 mod p

// Input:   non-zero coprime integers A and B, and a prime p
// Output:  0 or 1

// 0 if contradiction achieved. 1 if inconclusive.

Local1:=function(A,B,p);
       for k in [1..150] do
           l:= 2*k*p+1;
           if ( A mod l ne 0 ) and ( B mod l ne 0 ) and IsPrime(l) then
              Fl := GF(l);
              g:= Fl ! PrimitiveRoot(l);
              h:=g^p;
              S:=[ h^r : r in [0..2*k-1] ] cat [0];
              A0 := Fl ! A;
              B0 := Fl ! B;
              AS := {A0*s : s in S};
              BSp1 := {B0*s+1 : s in S};
              if AS meet BSp1 eq {} then
                 return 0;
              end if;
           end if;
        end for;
        return 1;
end function;

///////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////

// +++ SysThue +++

// Input: A sequence of two triples: [[A1,B1,C1],[A2,B2,C2]] and p = 3 or p = 5
// Output: 0 (if no solution) or 1 if there is a positive solution

// Tests whether the system of equations
// A1 y1^p - B1 y2^p = C1,  A2 y1^p - B2 y3^p = C2
// has solution with y1 > 0 and y2 > 0
// Tests by solving (system of) Thue equations

SysThue:=function(Trips,p);
         T<x>:=PolynomialRing(Integers());
         A1:=Trips[1][1];  B1:=Trips[1][2]; C1:=Trips[1][3];
         A2:=Trips[2][1];  B2:=Trips[2][2]; C2:=Trips[2][3];

         Sols1 := Solutions(Thue(A1*x^p-B1),C1);
         // non-zero pairs (y2,y1) that solve first equation with y1 > 0
         PosSols1 := [S : S in Sols1 | S[1] gt 0 and S[2] gt 0];

         if PosSols1 eq [] then
            return 0;
         end if;

         y1s := [P[2] : P in PosSols1];

         for y1 in y1s do
             y3p := (A2*y1^p-C2)/B2;
             if IsIntegral(y3p) then
                y3p := Integers() ! y3p;
                vals := [p[2] : p in Factorisation(y3p)];
                if vals eq [] or GCD(vals) mod p eq 0 then
                   return 1;
                end if;
             end if;
         end for;
         return 0;
end function;


/////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////

// +++ SysLocal +++

// Input: A sequence of two triples: [[A1,B1,C1],[A2,B2,C2]] and a prime p
// Output: 0 or 1

// Tests whether the system of equations
// A1 y1^p - B1 y2^p = C1,  A2 y1^p - B2 y3^p = C2
// has a solution.
// Tests using prime 1 mod p

// 0 if contradiction achieved. 1 if inconclusive.

SysLocal:=function(Trips,p);
       A1:=Trips[1][1];  B1:=Trips[1][2]; C1:=Trips[1][3];
       A2:=Trips[2][1];  B2:=Trips[2][2]; C2:=Trips[2][3];

       for k in [1..150] do
           l:= 2*k*p+1;
           if IsPrime(l) and A1 mod l ne 0 and B1 mod l ne 0 and C1 mod l ne 0 and A2 mod l ne 0 and B2 mod l ne 0 and C2 mod l ne 0 then
              Fl := GF(l);
              g:= Fl ! PrimitiveRoot(l);
              h:=g^p;
              S:=[ h^r : r in [0..2*k-1] ] cat [0];
              A1l := Fl ! A1;     B1l := Fl ! B1;     C1l := Fl ! C1;
              AS := {A1l*s : s in S};
              BSp1 := {B1l*s+C1l : s in S};
              Int := AS meet BSp1;
              if Int eq {} then
                 return 0;
              end if;

              y1ps := [(I-C1l)/B1l : I in Int ]; // possibilities for y_1^p mod l

              A2l := Fl ! A2;      B2l := Fl ! B2;     C2l := Fl ! C2;

              for y1p in y1ps do
                  ct := 0;
                  if ((A2l*y1p-C2l)/B2l) in S then
                     ct := 1;
                     break;
                  end if;
              end for;

              if ct eq 0 then
                 return 0;
              end if;
           end if;
        end for;
        return 1;
end function;

////////////////////////////////////////////////////
////////////////////////////////////////////////////

// +++ Rec2 +++ (also in ModularFunctions.m)

// Input: Integer A, prime p, sequence SA, prime factors of A (in increasing order)
// Output: Reconstruction of A

// Reconstructs A from its sequence SA and the prime p.
// The prime factors of A are included an input
// as they can be obtained separately and this speeds things up

Rec2:=function(A,p,S,PrimeFacs)
      if A eq 1 then
         return 1;
      end if;
      Facs:=[];
      for i in [1..#S] do
          q := PrimeFacs[i];
          if S[i] eq 0 then
             Facs := Facs cat [q^(Valuation(A,q))];
          else Facs := Facs cat [q^(p-S[i])];
          end if;
      end for;
      return &*Facs;
end function;


////////////////////////////////////////////////////
////////////////////////////////////////////////////

// +++ ambmcm +++ (also in ModularFunctions.m)

// Input: Integer m > 5
// Output: am, bm, cm

ambmcm:=function(m);
     am:=m-2;
     bm:=m-5;
     cm:=6;
     if am mod 3 eq 0 and bm mod 3 eq 0 then
        am:=Integers() ! (am/3);
        bm:=Integers() ! (bm/3);
        cm:=2;
     end if;
     return am, bm, cm;
end function;

////////////////////////////////////////////////////
////////////////////////////////////////////////////

// +++ MPrimeBound +++

// Input: Integer m>5
// Output: Prime Bound for pyramidal equation

MPrimeBound:=function(m);
             am,bm,cm:= ambmcm(m);
             bd := 10676*Log(cm^2*(am+bm)*bm);
             return Floor(bd);
end function;

/////////////////////////////////////////////////////
/////////////////////////////////////////////////////

// +++ Triples +++

// Input: Integers A,B,C, m
// Output: Sequence of two triples of coefficients

// A,B,C are the denominators of x, x+1, and am x - b
// once they have been made coprime
// The output gives the coefficients for the corresponding system of Thue equations

Triples := function(A,B,C,m);
           am,bm,cm := ambmcm(m);
           Trip1 := [B,A,1];
           g2 := GCD([am*A,C,bm]);
           Trip2 := [Integers() ! (am*A/g2), Integers() ! (C/g2), Integers() ! (bm/g2)];
           return [Trip1,Trip2];
end function;

/////////////////////////////////////////////////////
/////////////////////////////////////////////////////

// +++ Sequ +++ (also in ModularFunctions.m)

// Input: An integer A
// Output: Sequence SA

// Recovers the sequence SA from A using p0=11 as the dummy prime

Sequ:=function(A);
      p0:=11;
      if A eq 1 then
         SeqA:=0;
      end if;;
      Vals:=[F[2] : F in Factorisation(A)];
      SA:=[];
      for v in Vals do
          if v lt 6 and v ne 0 then
             SA := SA cat [0];
          elif v gt 5 then
             SA := SA cat [p0-v];
          else SA := SA cat [0];
          end if;
       end for;
       return SA;
end function;

/////////////////////////////////////////////////////
/////////////////////////////////////////////////////

// +++ Pyramidal +++

// Input: Ainfo, Binfo, integer m, function Denom, case number cs
// Output: sequence of bad primes

Pyramidal:=function(Ainfo,Binfo,m,Denom,cs);
    badp:=[];
    for As in Ainfo do
        for Bs in Binfo do
            A:=As[1];
            SA:=As[2];
            B:=Bs[1];
            SB:=Bs[2];
            badpAB:=[];
            if (GCD(A,B) eq 1) and (cs in [2,21] or IsEven(A*B)) then
               // print "Considering <A,B> =", <Factorisation(A),Factorisation(B)>;
               PrimeFacsA:=PrimeFactors(A);
               PrimeFacsB:=PrimeFactors(B);
               for p in PrimesInInterval(3,MPrimeBound(m)) do   // up to MPrimeBound(m)
                   if cs ne 6 or p ne 3 then   // p = 3 is done separatly for case 6
                      RAp:= Rec2(A,p,SA,PrimeFacsA);
                      RBp := Rec2(B,p,SB,PrimeFacsB);
                      if (A ne 1 and B ne 1 and Local1(RBp,RAp,p) ne 0) or (A eq 1 or B eq 1) then
                         CC := Denom(RAp,RBp,p,m);
                         Trips := Triples(RAp,RBp,CC,m);
                         if SysLocal(Trips,p) ne 0 then
                            if (p notin [3,5]) or (p in [3,5] and SysThue(Trips,p) ne 0) then
                               badpAB := badpAB cat [p];
                               badp:=badp cat [p];
                            end if;
                         end if;
                      end if;
                   end if;
               end for;
            end if;
            if badpAB ne [] then
               print "For <A,B> =", <Factorisation(A),Factorisation(B)>;
               if #badpAB gt 20 then
                  print "Many bad primes";
               else print "Bad primes are", badpAB;
               end if;
               print ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>";
            end if;
        end for;
    end for;
    return badp;
end function;

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////

// +++ Sturm +++

// For a newform f and a prime p, checks whether ~_p f can be eliminated
// Checks necessary conditions up to the Sturm bound

// Input: Newform f; prime p
// Output: 0 if (f,p) passes Sturm check, non-zero integer otherwise

Sturm:=function(f,p);
        N:=Level(f);
        M:=LCM(4,N);
        mu := M* (&*[1-1/p : p in PrimeFactors(M)]);
        Bd:= Ceiling(mu/6);          // The Sturm bound
        ls1:={l : l in PrimesInInterval(2,Bd) | 2*N mod l ne 0};
        ct := 0; // start ct at 0

        K:=CoefficientField(f);
        OK:=Integers(K);
        Fact:=Factorisation(p*OK);
        PPs:=[Fac[1] : Fac in Fact];

        if Degree(f) eq 1
           then F:=EllipticCurve(f);  // faster to work with elliptic curve
        end if;

        for PP in PPs do
            Quo,pi := quo<OK | PP>;
            ct := 0;
            for l in ls1 do

                if Degree(f) eq 1 then
                   clf := TraceOfFrobenius(F,l);
                else clf := Coefficient(f,l);
                end if;
                if pi(l+1-clf) ne 0 then
                   ct := ct + 1;
                   break;
                end if;
             end for;
             if ct eq 0 then // this should work, so test second condition.
                ls2:={l : l in PrimesInInterval(2,Bd) | (2*N mod l eq 0) and (Valuation(4*N,l) lt 2) };
                for l in ls2 do
                    clf := Coefficient(f,l);
                    if pi( (l+1)*(clf-1) ) ne 0 then
                       ct := ct+1;
                       break;
                    end if;
                end for;
             end if;
             if ct eq 0 then
                break;
             end if;
        end for;

        return ct;
end function;

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////

// +++ Rad +++

// Determines Rad(M) or Rad_p(M) for and integer M

// Input:  integer M and a prime r, or r is 1 for normal Rad.
// Ouptut: Rad_r(M), the product of all primes not equal to r dividing M.
// If M = 0 then output is 0.

Rad:=function(M,r);
     if M eq 0 then
        return 0;
     else  seq := [i : i in PrimeFactors(M) | i ne r];
           if #seq eq 0 then
              return 1;
           else return &*seq;
           end if;
     end if;
end function;


/////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////

// +++ Modular +++

// Tests to see if By_2^p - Ay_1^p = 1 has a solution when A = 1 or B = 1
// AND we have a global solution to our system of two equations with y_1*y_2 = 0

// Input:   A,SA,B,SB,C, and m.
// Output:  List of bad primes > 3 that have not been eliminated

// It is also possible to run this code using (p,p,2) newforms by changing a few lines
// (Or using (p,p,3) newforms with some more work)

Modular:= function(A,SA,B,SB,C,m);
     am,bm,cm := ambmcm(m);
     // Start by obtaining a list of inital bad primes
     PrimeFacsA := PrimeFactors(A);
     PrimeFacsB := PrimeFactors(B);

     if B ne 1 then
        D := B; SD := SB; PrimeFacsD := PrimeFacsB;  // Choose D as A or B, depending on which is not 1
     else D := A; SD := SA; PrimeFacsD := PrimeFacsA;
     end if;

     RadD := Rad(D,1);
     p0 := 11; // dummy prime
     Rd := Rec2(D, p0, SD, PrimeFacsD); // reconstruct D using dummy prime (enough to get the prime factors of phi(D))
     Badp := Set(PrimeFactors(EulerPhi(Rd)));
     Badp := {p : p in Badp | p ne 2};

     print "Initial bad primes are", Badp;

     if Badp ne {} and Max(Badp) gt 7 then
        Nps:={2*Rad(D,2), 2^5*Rad(D,2)};

        print "Computing newforms at levels", Nps;

        Nfs := [* *];
        for Np in Nps do
            Newfs:=Newforms(CuspForms(Np));
            Nfs := Nfs cat [* Newfs[i][1] : i in [1..#Newfs] *];
        end for;
     end if;

     Badp2 := {};

     for p in Badp do
         print "Trying to eliminate p =", p;
         if #PrimeFacsD le 2 and Max(PrimeFacsD) lt 30 then
             print "eliminated using known results";
             continue;
         end if;

         RAp := Rec2(A,p,SA,PrimeFacsA);
         RBp := Rec2(B,p,SB,PrimeFacsB);

         A1 := RBp;    B1 := RAp; C1 := 1;
         A2 := am*RAp; B2 := C;   C2 := bm;

         if p lt 11 or (m eq 49 and p eq 11) then
            if p eq 11 then
                print "Takes a bit under an hour to solve this Thue equation";
            end if;
            if SysThue([[A1,B1,C1],[A2,B2,C2]], p ) eq 0 then
               print p, "eliminated by directly solving Thue equations";
            else print "There is a solution when p = ", p;
                 Badp2 := Badp2 join {p};
            end if;
            continue;
         end if;

         assert Valuation(D,2) eq 1; // sanity check for application of modular method
         lsp := []; // list of primes l at which Frey curve at p will have mult. red.

         for k in [1..50] do
             l:= 2*k*p+1;
             if A*B*C*am*bm mod l ne 0 and IsPrime(l) then
                Fl := GF(l);
                g:= Fl ! PrimitiveRoot(l);
                h:=g^p;
                S:=[ h^r : r in [0..2*k-1] ] cat [0];
                A1l := Fl ! A1;     B1l := Fl ! B1;     C1l := Fl ! C1;
                A2l := Fl ! A2;     B2l := Fl ! B2;     C2l := Fl ! C2;

                AS := {A1l*s : s in S};
                BSp1 := {B1l*s+C1l : s in S};
                Int := AS meet BSp1;
                y1ps := [(I-C1l)/B1l : I in Int ];  // possibilities for y_1^p
                goody1ps := {y1p : y1p in y1ps | ((A2l*y1p-C2l)/B2l) in S}; // ones that work with 2nd eq too

                if #goody1ps eq 1 then // y1 or y2 is 0 mod l so Frey curve will have mult. red. at l
                   lsp := lsp cat [l]; // know this as global solution will always survive
                end if;
             end if;
         end for;

         print #lsp, "auxiliary primes found";

         for f in Nfs do
             MM := 0; // Build up a GCD
             for l in lsp do
                 clf := Coefficient(f,l);
                 MM := GCD(MM, Integers() ! (Norm((l+1)^2 - clf^2)) );
                if (MM mod p) ne 0 then // prime is eliminated for this newform
                    break;
                end if;
             end for;

             Strm := Sturm(f,p);
             if Strm eq 0 then
                print "Using Sturm bound argument for the newform", f, "at level", Level(f);
             end if;
             if (MM mod p eq 0) and Sturm(f,p) ne 0 then
                 print "Cannot eliminate", p, f;  // If we reach here, then prime has not been eliminated
                 Badp2 := Badp2 join {p};
                 break;
             end if;
          end for;
     end for;

     if Badp2 eq {} then
        print "All primes eliminated";
     end if;

     return Badp2;
end function;


/////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////


// Explanatory notes on A,SA, and p0.

// SA is a sequence that determine the exponents of the prime factors of A
// The size of SA is the number of prime factors of A.
// Each element of SA corresponds to a prime factor of A
// and the prime factors should be in ascending order.
// If A does not depend on p, then SA = [0,0,...,0].
// A non-negative integer 'r' in the sequence means the corresponding exponent is p-r

// e.g. if A = 2 x 11 then SA = [0,0]
// e.g. if A = 3^4 x 13^2 then SA = [0,0]
// e.g. if A = 1 then SA = []
// e.g. if A = 2 x 3^5 x 7^(p-1) then SA = [0,0,1]
// e.g. if A = 2^(p-3) x 11^(p-4) then SA = [3,4]
// e.g. if A = 2^(p-1) x 3 x 7 x 11 x 23 then SA = [1,0,0,0,0]

// To input A when A depends on p, we always use the dummy variable p0 = 11.
// e.g. if A = 2^(p-1) x 11^(p-2) then enter A = 2^(p0-1) x 11^(p0-2)   ( = 2^10 x 11^9)
// e.g. if A = 2 x 3^5 x 7^(p-1) then enter 2 x 3^5 x 7^(p0-1)

// Given A (entered using p0=11), SA, and p
// the function 'Rec2' reconstructs the true value of A

// Given A (entered using p0 = 11)
// the function 'Sequ' finds SA
// This works assuming the exponents are fairly close to 1 or p0 which will always be the case
// Would not work for 2^8 x 3^(p-7)
// But using p0 = 41 say would remedy this if it were necessary
