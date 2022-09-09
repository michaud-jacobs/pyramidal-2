////////////////////////////////////////////////////////////////////////////////////////

// This code carries out all of the checks for the paper 
// "On power values of pyramidal numbers, II"

////////////////////////////////////////////////////////////////////////////////////////

// Please see the file PyramidalFunctions.m for all the necessary functions
// Please see the end of the file PyramidalFunctions.m for further explanatory notes

// We split into cases as in the paper
// We also have the Cases 11, 12, 21, 31 which are part of Cases 1,1,2,3 respectively in the paper
// Here we have separated out these as separate cases for clarity in the code.

// At the end of the document, we treat the extra cases for Cases 4,5,6.

// The whole file can be run and the output is available in the file PyramidalOutput.txt

////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////


load "PyramidalFunctions.m";

// Case 1

// EITHER

// cm = 6. 
// bm = p1^r1, for r1 = 0,1,2 and p1 > 3
// am+bm = p2^r2 for r2 = 0,1,2,3 and p2 > 3

// m = 6, 10, 12, 16, 18, 22, 24, 28, 30, 34, 48

// OR

// cm = 2. 
// bm = p1^r1, for r1 = 0,1,2 and p1 > 2
// am+bm = p2^r2 for r2 = 0,1,2,3 and p2 > 2

// m = 8, 14, 20, 32, 38, 44

for m in [6, 10, 12, 16, 18, 22, 24, 28, 30, 34, 48, 8, 14, 20, 32, 38, 44] do
print "Considering m =", m;

cs:=1;  // case number

print "Case",cs;

// computes possibilities for <A,SA> and <B,SB>

ABcase1:=function(m);       
         am,bm,cm:= ambmcm(m);

         if bm eq 1 then
            p1 := 1;
            r1:= 0;
         else p1 := PrimeFactors(bm)[1];
              r1 := Valuation(bm,p1);
         end if; 
 
         if am+bm eq 1 then
            p2 := 1;
            r2:= 0;
         else p2 := PrimeFactors(am+bm)[1];
              r2 := Valuation(am+bm,p2);
         end if;

         p0:=11;
         al1s:=[0,1];
         al2s:=[0,1];
         if cm eq 2 then 
            be1s:=[0];
            be2s:=[0];
         else be1s:=[0,1];
              be2s:=[0,1];
         end if;
         gam1s:=[0,r1,p0-r1];
         gam2s:=[0,r2,p0-r2];
         
         Ainfo:= {};
         for al1 in al1s do
             for be1 in be1s do
                 for gam1 in gam1s do
                     A:=2^al1*3^be1*p1^gam1;
                     SA:=Sequ(A);   // find SA from A
                     Ainfo := Ainfo join { <A,SA> };
                 end for;
             end for;
         end for;
            
         Binfo:= {};
         for al2 in al2s do
             for be2 in be2s do
                 for gam2 in gam2s do
                     B:=2^al2*3^be2*p2^gam2;
                     SB:=Sequ(B);
                     Binfo := Binfo join { <B,SB> };
                 end for;
             end for;
         end for;
           
         return Ainfo,Binfo;
end function;

Ainfo,Binfo:=ABcase1(m);

Denom1:=function(A,B,p,m);     // computes denominator of (amx-bm) from A,B, and p.
         am,bm,cm:= ambmcm(m);

         if bm eq 1 then
            p1 := 1;
            gam1 := 0;
         else p1 := PrimeFactors(bm)[1];
            gam1 := Valuation(A,p1);
         end if;
         
         if am+bm eq 1 then
            p2 := 1;
            gam2 := 0;
         else p2 := PrimeFactors(am+bm)[1];
              gam2 := Valuation(B,p2);
         end if;
         
         if cm eq 6 and A mod 3 ne 0 and B mod 3 ne 0 then 
            be3:=1;
         else be3:=0;
         end if;

         CC:=3^be3;               // Build up denominator 
         if gam1 ne 0 then 
            CC := CC*p1^(p-gam1);
         end if;
         if gam2 ne 0 then 
            CC := CC*p2^(p-gam2);
         end if;
         return CC;
end function;

 Bp:=Pyramidal(Ainfo,Binfo,m,Denom1,cs);  // run main function

////////////////////////////////////////////
// Bad Triples (A,B,C) in each case are 
// 1, cm*p2^(p-r2), p2^r2  and   cm*p1^(p-r1), 1, p1^r1


cs := 1;
am,bm,cm := ambmcm(m);
if bm eq 1 then
   p1 := 1;
   r1:= 0;
else p1 := PrimeFactors(bm)[1];
     r1 := Valuation(bm,p1);
end if; 
 
if am+bm eq 1 then
   p2 := 1;
   r2:= 0;
else p2 := PrimeFactors(am+bm)[1];
     r2 := Valuation(am+bm,p2);
end if;

p0 := 11;

A := 1; B := cm*p2^(p0-r2); C := p2^r2;
print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);

if m ne 8 then           // (When m = 8, we get A =2, B = 1)
   A := cm*p1^(p0-r1); B := 1; C := p1^r1;
   print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
   Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);   
end if;

print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
end for;

///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

// Case 2

// EITHER

// cm = 6. 
// bm = 2*p1^r1 for r1 = 0,1 and p1 > 3
// am+bm = p2 and p2 > 3

// m = 7, 15, 19, 27, 39, 43

// OR

// cm = 2. 
// bm = 2*p1^r1 for r1 = 0,1 and p1 > 2
// am+bm = p2 and p2 > 2

// m = 11, 23, 47

for m in [7, 15, 19, 27, 39, 43, 11, 23, 47] do
print "Considering m =", m;

cs:=2;  // case number

print "Case",cs;

// computes possibilities for <A,SA> and <B,SB>

ABcase2:=function(m);       
         am,bm,cm:= ambmcm(m);

         if bm eq 2 then
            p1 := 1;
         else p1 := PrimeFactors(bm)[2];
         end if;
 
         p2 := PrimeFactors(am+bm)[1];

         p0:=11;
         al1s:=[0,1];
         al2s:=[0,1];
         if cm eq 2 then 
            be1s:=[0];
            be2s:=[0];
         else be1s:=[0,1];
              be2s:=[0,1];
         end if;
         gam1s:=[0,1,p0-1];
         gam2s:=[0,1,p0-1];
         
         Ainfo:= {};
         for al1 in al1s do
             for be1 in be1s do
                 for gam1 in gam1s do
                     A:=2^al1*3^be1*p1^gam1;
                     SA:=Sequ(A);    
                     Ainfo := Ainfo join { <A,SA> };
                 end for;
             end for;
         end for;
            
         Binfo:= {};
         for al2 in al2s do
             for be2 in be2s do
                 for gam2 in gam2s do
                     B:=2^al2*3^be2*p2^gam2;
                     SB:=Sequ(B);
                     Binfo := Binfo join { <B,SB> };
                 end for;
             end for;
         end for;
           
         return Ainfo,Binfo;
end function;

Ainfo,Binfo:=ABcase2(m);

Denom2:=function(A,B,p,m);    
         am,bm,cm:= ambmcm(m);

         if bm eq 2 then
            gam1 := 0;
         else p1 := PrimeFactors(bm)[2];
              gam1 := Valuation(A,p1);
         end if;
         
         p2 := PrimeFactors(am+bm)[1];
         gam2 := Valuation(B,p2);

         if A mod 2 ne 0 and B mod 2 ne 0 then 
            al3:=1;
         else al3:=0;
         end if;

         if cm eq 6 and A mod 3 ne 0 and B mod 3 ne 0 then 
            be3:=1;
         else be3:=0;
         end if;
        
         CC:=2^al3*3^be3;               
         if gam1 ne 0 then 
            CC := CC*p1^(p-gam1);
         end if;
         if gam2 ne 0 then 
            CC := CC*p2^(p-gam2);
         end if;
         return CC;
end function;

Bp:=Pyramidal(Ainfo,Binfo,m,Denom2,cs);  

////////////////////////////////////////////
// Bad Triples (A,B,C) in each case are 
// 1, cm*p2^(p-1), p2  and   (cm/2)*p1^(p-r1), 1, p1^r1

cs:=2;
am,bm,cm := ambmcm(m);
if bm eq 2 then
   p1 := 1;
   r1:= 0;
else p1 := PrimeFactors(bm)[2];
     r1 := Valuation(bm,p1);
end if; 
p2 := am+bm;

p0 := 11;

A := 1; B := cm*p2^(p0-1); C := p2;
print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);

A := (Integers() ! (cm/2))*p1^(p0-r1); B := 1; C := p1^r1;
print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);

print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
end for;

///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

// Case 3

// EITHER

// cm = 6. 
// bm = 4*p1^r1 for r1 = 0,1  and p1 > 3
// am+bm = p2^r2 for r2 = 1,2 and p2 > 3

// m = 9, 25, 33

// OR

// cm = 2. 
// bm = 4*p1^r1 for r1 = 0,1 and p1 > 2
// am+bm = p2^r2 for r2 = 2 and p2 > 2

// m = 17, 41

for m in [9, 25, 33, 17, 41] do
print "Considering m =", m;

cs:=3;  

print "Case",cs;

ABcase3:=function(m);       
         am,bm,cm:= ambmcm(m);

         if bm eq 4 then
            p1 := 1;
         else p1 := PrimeFactors(bm)[2];
         end if;
 
         p2 := PrimeFactors(am+bm)[1];
         r2 := Valuation(am+bm,p2);

         p0:=11;
         al1s:=[0,2,p0-1];
         al2s:=[0,1];
         if cm eq 2 then 
            be1s:=[0];
            be2s:=[0];
         else be1s:=[0,1];
              be2s:=[0,1];
         end if;
         gam1s:=[0,1,p0-1];
         gam2s:=[0,r2,p0-r2];
         
         Ainfo:= {};
         for al1 in al1s do
             for be1 in be1s do
                 for gam1 in gam1s do
                     A:=2^al1*3^be1*p1^gam1;
                     SA:=Sequ(A);    
                     Ainfo := Ainfo join { <A,SA> };
                 end for;
             end for;
         end for;
            
         Binfo:= {};
         for al2 in al2s do
             for be2 in be2s do
                 for gam2 in gam2s do
                     B:=2^al2*3^be2*p2^gam2;
                     SB:=Sequ(B);
                     Binfo := Binfo join { <B,SB> };
                 end for;
             end for;
         end for;
           
         return Ainfo,Binfo;
end function;

Ainfo,Binfo:=ABcase3(m);

Denom3:=function(A,B,p,m);    
         am,bm,cm:= ambmcm(m);

         if bm eq 4 then
            gam1 := 0;
         else p1 := PrimeFactors(bm)[2];
              gam1 := Valuation(A,p1);
         end if;
         
         p2 := PrimeFactors(am+bm)[1];
         gam2 := Valuation(B,p2);
         al1:=Valuation(A,2);

         if  al1 eq p-1 then 
             al3:=2;
         elif al1 eq 2 then
             al3:=p-1;
         else al3:=0;
         end if;

         if cm eq 6 and A mod 3 ne 0 and B mod 3 ne 0 then 
            be3:=1;
         else be3:=0;
         end if;
        
         CC:=2^al3*3^be3;               
         if gam1 ne 0 then 
            CC := CC*p1^(p-gam1);
         end if;
         if gam2 ne 0 then 
            CC := CC*p2^(p-gam2);
         end if;
         return CC;
end function;

Bp:=Pyramidal(Ainfo,Binfo,m,Denom3,cs); 

////////////////////////////////////////////
// Bad Triples (A,B,C) in each case are 
// 1, cm*p2^(p-r2), p2^r2  and   2^(p-1)*(cm/2)*p1^(p-r1), 1, 2^2*p1^r1

cs:=3; 
am,bm,cm := ambmcm(m);
if bm eq 4 then
   p1 := 1;
   r1:= 0;
else p1 := PrimeFactors(bm)[2];
     r1 := Valuation(bm,p1);
end if; 

p2 := PrimeFactors(am+bm)[1];
r2 := Valuation(am+bm,p2);

p0 := 11;

A := 1; B := cm*p2^(p0-r2); C := p2^r2;
print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);

A := 2^(p0-1)* (Integers() ! (cm/2)) *p1^(p0-r1); B := 1; C := 2^2*p1^r1;
print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);
 
print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
end for;

///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

// Case 11 (like case 1)

// EITHER

// cm = 6. 
// bm = p1, and p1 > 3
// am+bm = p2*q2, and p2, q2 > 3

//  m =  36, 42, 46  

// OR

// cm = 2. 
// bm = p1, and p1 > 2
// am+bm = p2*q2, and p2, q2 > 2

// m = 26

for m in [36, 42, 46, 26] do
print "Considering m =", m;

cs:=11;  // case number

print "Case",cs; 
print "This is part of Case 1 in the paper";

// computes possibilities for <A,SA> and <B,SB>

ABcase11:=function(m);       
         am,bm,cm:= ambmcm(m);

         p1 := bm;           
         p2 := PrimeFactors(am+bm)[1];
         q2 := PrimeFactors(am+bm)[2];

         p0:=11;
         al1s:=[0,1];
         al2s:=[0,1];
         if cm eq 2 then 
            be1s:=[0];
            be2s:=[0];
         else be1s:=[0,1];
              be2s:=[0,1];
         end if;
         gam1s:=[0,1,p0-1];
         gam2s:=[0,1,p0-1];
         del2s:=[0,1,p0-1];
         
         Ainfo:= {};
         for al1 in al1s do
             for be1 in be1s do
                 for gam1 in gam1s do
                     A:=2^al1*3^be1*p1^gam1;
                     SA:=Sequ(A);   
                     Ainfo := Ainfo join { <A,SA> };
                 end for;
             end for;
         end for;
            
         Binfo:= {};
         for al2 in al2s do
             for be2 in be2s do
                 for gam2 in gam2s do
                     for del2 in del2s do
                         B:=2^al2*3^be2*p2^gam2*q2^del2;
                         SB:=Sequ(B);
                         Binfo := Binfo join { <B,SB> };
                     end for;
                 end for;
             end for;
         end for;
           
         return Ainfo,Binfo;
end function;

Ainfo,Binfo:=ABcase11(m);

Denom11:=function(A,B,p,m);     
         am,bm,cm:= ambmcm(m);

         p1 := bm;           
         p2 := PrimeFactors(am+bm)[1];
         q2 := PrimeFactors(am+bm)[2];
         
         gam1 := Valuation(A,p1);
         gam2 := Valuation(B,p2);
         del2 := Valuation(B,q2);

         if cm eq 6 and A mod 3 ne 0 and B mod 3 ne 0 then 
            be3:=1;
         else be3:=0;
         end if;

         CC:=3^be3;              
         if gam1 ne 0 then 
            CC := CC*p1^(p-gam1);
         end if;
         if gam2 ne 0 then 
            CC := CC*p2^(p-gam2);
         end if;
         if del2 ne 0 then
            CC := CC*q2^(p-del2);
         end if;
         return CC;
end function;

Bp:=Pyramidal(Ainfo,Binfo,m,Denom11,cs);  

////////////////////////////////////////////
// Bad Triples (A,B,C) in each case are 
// 1, cm*p2^(p-1)*q2^(p-1), p2*q2  and   cm*p1^(p-1), 1, p1

am,bm,cm := ambmcm(m);
p1 := bm;            
p2 := PrimeFactors(am+bm)[1];
q2 := PrimeFactors(am+bm)[2];
p0 := 11;

A := 1; B := cm*p2^(p0-1)*q2^(p0-1); C := p2*q2;
print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);

A := cm*p1^(p0-1); B := 1; C := p1;
print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);

print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
end for;

///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

// Case 12 (like case 1)

// EITHER

// cm = 6. 
// bm = p1*q1, and p1, q1 > 3
// am+bm = p2, and p2 > 3

//  m =  40  

// OR

// cm = 2. 
// bm = p1*q1, and p1, q1 > 2
// am+bm = p2, and p2, > 2

// m = 50

for m in [40, 50] do
print "Considering m =", m;

cs:=12;  // case number

print "Case",cs; 
print "This is part of Case 1 in the paper";

// computes possibilities for <A,SA> and <B,SB>

ABcase12:=function(m);       
         am,bm,cm:= ambmcm(m);

         p1 := PrimeFactors(bm)[1]; 
         q1 := PrimeFactors(bm)[2];           
         p2 := am+bm;
         
         p0:=11;
         al1s:=[0,1];
         al2s:=[0,1];
         if cm eq 2 then 
            be1s:=[0];
            be2s:=[0];
         else be1s:=[0,1];
              be2s:=[0,1];
         end if;
         gam1s:=[0,1,p0-1];
         del1s:=[0,1,p0-1];
         gam2s:=[0,1,p0-1];
         
         Ainfo:= {};
         for al1 in al1s do
             for be1 in be1s do
                 for gam1 in gam1s do
                     for del1 in del1s do
                         A:=2^al1*3^be1*p1^gam1*q1^del1;
                         SA:=Sequ(A);   
                         Ainfo := Ainfo join { <A,SA> };
                     end for;
                 end for;
             end for;
         end for;
            
         Binfo:= {};
         for al2 in al2s do
             for be2 in be2s do
                 for gam2 in gam2s do                    
                     B:=2^al2*3^be2*p2^gam2;
                     SB:=Sequ(B);
                     Binfo := Binfo join { <B,SB> };                     
                 end for;
             end for;
         end for;
           
         return Ainfo,Binfo;
end function;

Ainfo,Binfo:=ABcase12(m);

Denom12:=function(A,B,p,m);     
         am,bm,cm:= ambmcm(m);

         p1 := PrimeFactors(bm)[1]; 
         q1 := PrimeFactors(bm)[2];           
         p2 := am+bm;
         
         gam1 := Valuation(A,p1);
         del1 := Valuation(A,q1);
         gam2 := Valuation(B,p2);

         if cm eq 6 and A mod 3 ne 0 and B mod 3 ne 0 then 
            be3:=1;
         else be3:=0;
         end if;

         CC:=3^be3;              
         if gam1 ne 0 then 
            CC := CC*p1^(p-gam1);
         end if;
         if del1 ne 0 then 
            CC := CC*q1^(p-del1);
         end if;
         if gam2 ne 0 then
            CC := CC*p2^(p-gam2);
         end if;
         return CC;
end function;

Bp:=Pyramidal(Ainfo,Binfo,m,Denom12,cs);  

////////////////////////////////////////////
// Bad Triples (A,B,C) in each case are 
// 1, cm*p2^(p-1), p2  and   cm*p1^(p-1)*q1^(p-1), 1, p1*q1

am,bm,cm := ambmcm(m);
p1 := PrimeFactors(bm)[1]; 
q1 := PrimeFactors(bm)[2];           
p2 := am+bm;
p0 := 11;

A := 1; B := cm*p2^(p0-1); C := p2;
print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);

A := cm*p1^(p0-1)*q1^(p0-1); B := 1; C := p1*q1;
print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);

print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
end for;

///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

// Case 21 (like case 2)

// EITHER

// cm = 6. 
// bm = 2*p1, and p1 > 3
// am+bm = p2*q2 and p2, q2 > 3

// m = 31

// OR

// cm = 2. 
// bm = 2*p1, and p1 > 2
// am+bm = p2*q2 and p2,q2 > 2

// m = 35

for m in [31, 35] do
print "Considering m =", m;

cs:=21;  // case number

print "Case",cs; 
print "This is part of Case 2 in the paper";

ABcase21:=function(m);       
         am,bm,cm:= ambmcm(m);

         p1 := PrimeFactors(bm)[2];            
         p2 := PrimeFactors(am+bm)[1];
         q2 := PrimeFactors(am+bm)[2];

         p0:=11;
         al1s:=[0,1];
         al2s:=[0,1];
         if cm eq 2 then 
            be1s:=[0];
            be2s:=[0];
         else be1s:=[0,1];
              be2s:=[0,1];
         end if;
         gam1s:=[0,1,p0-1];
         gam2s:=[0,1,p0-1];
         del2s:=[0,1,p0-1];
         
         Ainfo:= {};
         for al1 in al1s do
             for be1 in be1s do
                 for gam1 in gam1s do
                     A:=2^al1*3^be1*p1^gam1;
                     SA:=Sequ(A);    
                     Ainfo := Ainfo join { <A,SA> };
                 end for;
             end for;
         end for;
            
         Binfo:= {};
         for al2 in al2s do
             for be2 in be2s do
                 for gam2 in gam2s do
                     for del2 in del2s do
                         B:=2^al2*3^be2*p2^gam2*q2^del2;
                         SB:=Sequ(B);
                         Binfo := Binfo join { <B,SB> };
                     end for;
                 end for;
             end for;
         end for;
           
         return Ainfo,Binfo;
end function;

Ainfo,Binfo:=ABcase21(m);

Denom21:=function(A,B,p,m);    
         am,bm,cm:= ambmcm(m);

         p1 := PrimeFactors(bm)[2];            
         p2 := PrimeFactors(am+bm)[1];
         q2 := PrimeFactors(am+bm)[2];

         gam1 := Valuation(A,p1);
         gam2 := Valuation(B,p2);
         del2 := Valuation(B,q2);

         if A mod 2 ne 0 and B mod 2 ne 0 then 
            al3:=1;
         else al3:=0;
         end if;

         if cm eq 6 and A mod 3 ne 0 and B mod 3 ne 0 then 
            be3:=1;
         else be3:=0;
         end if;
        
         CC:=2^al3*3^be3;               
         if gam1 ne 0 then 
            CC := CC*p1^(p-gam1);
         end if;
         if gam2 ne 0 then 
            CC := CC*p2^(p-gam2);
         end if;
         if del2 ne 0 then
            CC := CC*q2^(p-del2);
         end if;
         return CC;
end function;

Bp:=Pyramidal(Ainfo,Binfo,m,Denom21,cs);  

////////////////////////////////////////////
// Bad Triples (A,B,C) in each case are 
// 1, cm*p2^(p-1)*q2^(p-1), p2*q2  and   (cm/2)*p1^(p-1), 1, p1

am,bm,cm := ambmcm(m);
p1 := PrimeFactors(bm)[2];            
p2 := PrimeFactors(am+bm)[1];
q2 := PrimeFactors(am+bm)[2];

p0 := 11;

A := 1; B := cm*p2^(p0-1)*q2^(p0-1); C := p2*q2;
print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);

A := (Integers() ! (cm/2))*p1^(p0-1); B := 1; C := p1;
print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);

print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
end for;

///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

// Case 31 (like case 3)

// cm = 6. 
// bm = 4*p1, and p1 > 3
// am+bm = p2*q2, and p2, q2 > 3

// m = 49

for m in [49] do
print "Considering m =", m;

cs:=31;  

print "Case",cs; 
print "This is part of Case 3 in the paper";

ABcase31:=function(m);       
         am,bm,cm:= ambmcm(m);

         p1 := PrimeFactors(bm)[2]; 
         p2 := PrimeFactors(am+bm)[1];
         q2 := PrimeFactors(am+bm)[2];

         p0:=11;
         al1s:=[0,2,p0-1];
         al2s:=[0,1];
         if cm eq 2 then 
            be1s:=[0];
            be2s:=[0];
         else be1s:=[0,1];
              be2s:=[0,1];
         end if;
         gam1s:=[0,1,p0-1];
         gam2s:=[0,1,p0-1];
         del2s:=[0,1,p0-1];
         
         Ainfo:= {};
         for al1 in al1s do
             for be1 in be1s do
                 for gam1 in gam1s do
                     A:=2^al1*3^be1*p1^gam1;
                     SA:=Sequ(A);    
                     Ainfo := Ainfo join { <A,SA> };
                 end for;
             end for;
         end for;
            
         Binfo:= {};
         for al2 in al2s do
             for be2 in be2s do
                 for gam2 in gam2s do
                     for del2 in del2s do
                         B:=2^al2*3^be2*p2^gam2*q2^del2;
                         SB:=Sequ(B);
                         Binfo := Binfo join { <B,SB> };
                     end for;
                 end for;
             end for;
         end for;
           
         return Ainfo,Binfo;
end function;

Ainfo,Binfo:=ABcase31(m);

Denom31:=function(A,B,p,m);    
         am,bm,cm:= ambmcm(m);

         p1 := PrimeFactors(bm)[2]; 
         p2 := PrimeFactors(am+bm)[1];
         q2 := PrimeFactors(am+bm)[2];

         al1:=Valuation(A,2);
         gam1 := Valuation(A,p1);
         gam2 := Valuation(B,p2);
         del2 := Valuation(B,q2);
         
         if  al1 eq p-1 then 
             al3:=2;
         elif al1 eq 2 then
             al3:=p-1;
         else al3:=0;
         end if;

         if cm eq 6 and A mod 3 ne 0 and B mod 3 ne 0 then 
            be3:=1;
         else be3:=0;
         end if;
        
         CC:=2^al3*3^be3;               
         if gam1 ne 0 then 
            CC := CC*p1^(p-gam1);
         end if;
         if gam2 ne 0 then 
            CC := CC*p2^(p-gam2);
         end if;
         if del2 ne 0 then
            CC := CC*q2^(p-del2);
         end if;
         return CC;
end function;

Bp:=Pyramidal(Ainfo,Binfo,m,Denom31,cs);  

////////////////////////////////////////////
// Bad Triples (A,B,C) in each case are 
// 1, cm*p2^(p-1)*q2^(p-1), p2*q2  and   2^(p-1)*(cm/2)*p1^(p-1), 1, 2^2*p1

am,bm,cm := ambmcm(m);
p1 := PrimeFactors(bm)[2]; 
p2 := PrimeFactors(am+bm)[1];
q2 := PrimeFactors(am+bm)[2];

p0 := 11;

A := 1; B := cm*p2^(p0-1)*q2^(p0-1); C := p2*q2;
print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);

A := 2^(p0-1)* (Integers() ! (cm/2)) *p1^(p0-1); B := 1; C := 2^2*p1;
print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);

print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
end for;

///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

// Case 4

// EITHER

// cm = 6. 
// bm = 8*p1^r1 for r1 = 0,1  and p1 > 3
// am+bm = p2, and p2 > 3

// m = 13, 45

// OR

// cm = 2. 
// bm = 8
// am+bm = p2, and p2 > 2

// m = 29

for m in [13, 45, 29] do
print "Considering m =", m;

cs:=4;  

print "Case",cs; 

// (Extra cases needed below for p = 3)

ABcase4:=function(m);       
         am,bm,cm:= ambmcm(m);

         if bm eq 8 then
            p1 := 1;
         else p1 := PrimeFactors(bm)[2];
         end if;
 
         p2 := am+bm;
       
         p0:=11;
         al1s:=[0,3,p0-2];
         al2s:=[0,1];
         if cm eq 2 then 
            be1s:=[0];
            be2s:=[0];
         else be1s:=[0,1];
              be2s:=[0,1];
         end if;
         gam1s:=[0,1,p0-1];
         gam2s:=[0,1,p0-1];
         
         Ainfo:= {};
         for al1 in al1s do
             for be1 in be1s do
                 for gam1 in gam1s do
                     A:=2^al1*3^be1*p1^gam1;
                     SA:=Sequ(A);    
                     Ainfo := Ainfo join { <A,SA> };
                 end for;
             end for;
         end for;
            
         Binfo:= {};
         for al2 in al2s do
             for be2 in be2s do
                 for gam2 in gam2s do
                     B:=2^al2*3^be2*p2^gam2;
                     SB:=Sequ(B);
                     Binfo := Binfo join { <B,SB> };
                 end for;
             end for;
         end for;
           
         return Ainfo,Binfo;
end function;

Ainfo,Binfo:=ABcase4(m);

Denom4:=function(A,B,p,m);    
         am,bm,cm:= ambmcm(m);

         if bm eq 8 then
            gam1 := 0;
         else p1 := PrimeFactors(bm)[2];
              gam1 := Valuation(A,p1);
         end if;
         
         p2 := PrimeFactors(am+bm)[1];
         gam2 := Valuation(B,p2);
         al1:=Valuation(A,2);

         if  al1 eq p-2 then 
             al3:=3;
         elif al1 eq 3 then
             al3:=p-2;
         else al3:=0;
         end if;

         if cm eq 6 and A mod 3 ne 0 and B mod 3 ne 0 then 
            be3:=1;
         else be3:=0;
         end if;
        
         CC:=2^al3*3^be3;               
         if gam1 ne 0 then 
            CC := CC*p1^(p-gam1);
         end if;
         if gam2 ne 0 then 
            CC := CC*p2^(p-gam2);
         end if;
         return CC;
end function;

Bp:=Pyramidal(Ainfo,Binfo,m,Denom4,cs);  


////////////////////////////////////////////
// Bad Triples (A,B,C) in each case are 
// 1, cm*p2^(p-1), p2  and   2^(p-2)*(cm/2)*p1^(p-r1), 1, 2^3*p1^r1

cs := 4;
am,bm,cm := ambmcm(m);
if bm eq 8 then
   p1 := 1;
   r1:= 0;
else p1 := PrimeFactors(bm)[2];
     r1 := Valuation(bm,p1);
end if; 
p2 := am+bm;

p0 := 11;

A := 1; B := cm*p2^(p0-1); C := p2;
print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);

A := 2^(p0-2)* (Integers() ! (cm/2)) *p1^(p0-r1); B := 1; C := 2^3*p1^r1;
print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);

print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
end for;

///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

// Case 5

// cm = 6. 
// bm = 16 
// am+bm = p2*q2, and p2, q2 > 3

// m = 21

for m in [21] do
print "Considering m =", m;

cs:=5;  

print "Case",cs; 

// (Extra cases needed below for p = 3 and p = 5)

ABcase5:=function(m);       
         am,bm,cm:= ambmcm(m);

         p2 := PrimeFactors(am+bm)[1];
         q2 := PrimeFactors(am+bm)[2];

         p0:=11;
         al1s:=[0,4,p0-3];
         al2s:=[0,1];
         be1s:=[0,1];
         be2s:=[0,1];
         gam2s:=[0,1,p0-1];
         del2s:=[0,1,p0-1];
         
         Ainfo:= {};
         for al1 in al1s do
             for be1 in be1s do                 
                 A:=2^al1*3^be1;
                 SA:=Sequ(A);    
                 Ainfo := Ainfo join { <A,SA> };                
             end for;
         end for;
            
         Binfo:= {};
         for al2 in al2s do
             for be2 in be2s do
                 for gam2 in gam2s do
                     for del2 in del2s do
                         B:=2^al2*3^be2*p2^gam2*q2^del2;
                         SB:=Sequ(B);
                         Binfo := Binfo join { <B,SB> };
                     end for;
                 end for;
             end for;
         end for;
           
         return Ainfo,Binfo;
end function;

Ainfo,Binfo:=ABcase5(m);

Denom5:=function(A,B,p,m);    
         am,bm,cm:= ambmcm(m);

         p2 := PrimeFactors(am+bm)[1];
         q2 := PrimeFactors(am+bm)[2];

         gam2 := Valuation(B,p2);
         del2 := Valuation(B,q2);
         al1:=Valuation(A,2);

         if  al1 eq p-3 and IsOdd(B) then // need this extra detail for p = 3
             al3:=4;
         elif al1 eq p-3 and IsEven(B) then // need this extra detail for p = 3
             assert p eq 3; // sanity check
             al3:=1;
         elif al1 eq 4 then
             al3:=p-3;
         else al3:=0;
         end if;

         if cm eq 6 and A mod 3 ne 0 and B mod 3 ne 0 then 
            be3:=1;
         else be3:=0;
         end if;
        
         CC:=2^al3*3^be3;               
         if gam2 ne 0 then 
            CC := CC*p2^(p-gam2);
         end if;
         if del2 ne 0 then 
            CC := CC*q2^(p-del2);
         end if;
         return CC;
end function;

Bp:=Pyramidal(Ainfo,Binfo,m,Denom5,cs);  

////////////////////////////////////////////
// Bad Triples (A,B,C) in each case are 
// 1, cm*p2^(p-1)*q2^(p-1), p2*q2  and   2^(p-3)*(cm/2), 1, 2^4

am,bm,cm := ambmcm(m);
p2 := PrimeFactors(am+bm)[1];
q2 := PrimeFactors(am+bm)[2];
p0 := 11;

A := 1; B := cm*p2^(p0-1)*q2^(p0-1); C := p2*q2;
print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);

A := 2^(p0-3)*(Integers() ! (cm/2)); B := 1; C := 2^4;
print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);

print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
end for;

///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

// Case 6

// p = 3 not treated here.
// (Extra cases needed below for p = 3 and p = 5)

// cm = 6. 
// bm = 32 
// am+bm = p2, and p2 > 3

// m = 37

for m in [37] do
print "Considering m =", m;

cs:=6;  

print "Case",cs; 

// (Extra cases needed below for p = 3, p = 5, and p = 7)

ABcase6:=function(m);       
         am,bm,cm:= ambmcm(m);
         p2 := am+bm;
         
         p0:=11;
         al1s:=[0,5,p0-4];
         al2s:=[0,1];
         be1s:=[0,1];
         be2s:=[0,1];
         gam2s:=[0,1,p0-1];
         
         Ainfo:= {};
         for al1 in al1s do
             for be1 in be1s do                 
                 A:=2^al1*3^be1;
                 SA:=Sequ(A);    
                 Ainfo := Ainfo join { <A,SA> };                
             end for;
         end for;
            
         Binfo:= {};
         for al2 in al2s do
             for be2 in be2s do
                 for gam2 in gam2s do                    
                     B:=2^al2*3^be2*p2^gam2;
                     SB:=Sequ(B);
                     Binfo := Binfo join { <B,SB> };                    
                 end for;
             end for;
         end for;
           
         return Ainfo,Binfo;
end function;

Ainfo,Binfo:=ABcase6(m);

Denom6:=function(A,B,p,m);    
         am,bm,cm:= ambmcm(m);

         p2 := am+bm;
         
         gam2 := Valuation(B,p2);
         al1:=Valuation(A,2);

         if  al1 eq p-4 then 
             al3:=5;
         elif al1 eq 5 then
             al3:=p-4;
         else al3:=0;
         end if;

         if cm eq 6 and A mod 3 ne 0 and B mod 3 ne 0 then 
            be3:=1;
         else be3:=0;
         end if;
        
         CC:=2^al3*3^be3;               
         if gam2 ne 0 then 
            CC := CC*p2^(p-gam2);
         end if;
         return CC;
end function;

Bp:=Pyramidal(Ainfo,Binfo,m,Denom6,cs);  

////////////////////////////////////////////
// Bad Triples (A,B,C) in each case are 
// 1, cm*p2^(p-1), p2 and   2^(p-4)*(cm/2), 1, 2^5
cs := 6;
am,bm,cm := ambmcm(m);
p2 := am+bm;
p0 := 11;

A := 1; B := cm*p2^(p0-1); C := p2;
print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);

A := 2^(p0-4)*(Integers() ! (cm/2)); B := 1; C := 2^5;
print "Modular method for <A,B,C> =", <Factorisation(A),Factorisation(B),Factorisation(C)>;
Mm := Modular(A,Sequ(A),B,Sequ(B),C,m);

print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
end for;


print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
print "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";

///////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////

// Extra Cases 

print "Considering extra cases for small p and bm = 2^t with t > 2";

///////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////

// Extra cases when p = 3 and 2^2 || x, am*x-bm

// m = 29, cm = 2, bm = 8, am+bm = 17

m := 29;
am,bm,cm := ambmcm(m);
p:=3; 
al:=2;

ExtraTriples := [ [2^al,1,2^al], [2^al, am+bm, (am+bm)^(p-1)*2^al], [2^al, (am+bm)^(p-1), (am+bm)*2^al] ];

for Ex in ExtraTriples do
    assert SysThue( Triples(Ex[1],Ex[2],Ex[3],m), p) eq 0;
end for;

// m = 13, cm = 6, bm = 8, am+bm = 19

m := 13;
am,bm,cm := ambmcm(m);
p2 := am+bm;
p:=3;
al := 2;

dels := [[0,0,0],[0,1,p-1],[0,p-1,1]];
bes :=  [[1,0,0],[0,1,0],[0,0,1]];

Ext := [];
for del in dels do
    for be in bes do
        Ext:= Ext cat [[2^al*3^be[1], 3^be[2]*p2^del[2], 2^al*3^be[3]*p2^del[3]]];
    end for;
end for;

for Ex in Ext do
    assert SysThue( Triples(Ex[1],Ex[2],Ex[3],m), p) eq 0;
end for;

// m = 45, cm = 6, bm = 8*5, am+bm = 83

m := 45;
am,bm,cm := ambmcm(m);
p2 := am+bm;
pm := 5;
p:=3;
al:=2;

gams := [[0,0,0],[1,0,p-1],[p-1,0,1]];
dels := [[0,0,0],[0,1,p-1],[0,p-1,1]];
bes :=  [[1,0,0],[0,1,0],[0,0,1]];

Ext := [];
for del in dels do
    for be in bes do
        for gam in gams do
            Ext:= Ext cat [[2^al*3^be[1]*p1^gam[1], 3^be[2]*p2^del[2], 2^al*3^be[3]*p2^del[3]*p1^gam[3]]];
        end for;
    end for;
end for;

for Ex in Ext do
    assert SysThue( Triples(Ex[1],Ex[2],Ex[3],m), p) eq 0;
end for;


///////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////

// m = 21, cm = 6, bm = 16, am+bm = 35

// Extra cases when p = 3 and 2^2 || x, am*x-bm
// Extra cases when p = 5 and 2^3 || x, am*x-bm

m := 21;
am,bm,cm := ambmcm(m);
p2:=PrimeFactors(am+bm)[1];
q2:=PrimeFactors(am+bm)[2];
p:=3; 
al:=2;
// p:=5;
// al:=3;

dels := [[0,0,0],[0,1,p-1],[0,p-1,1]];
epss := [[0,0,0],[0,1,p-1],[0,p-1,1]];
bes :=  [[1,0,0],[0,1,0],[0,0,1]];

Ext := [];
for del in dels do
    for eps in epss do
        for be in bes do
            Ext:= Ext cat [[2^al*3^be[1], 3^be[2]*p2^del[2]*q2^eps[2], 2^al*3^be[3]*p2^del[3]*q2^eps[3]]];
        end for;
    end for;
end for;

for Ex in Ext do
    if p eq 3 then 
       assert SysThue( Triples(Ex[1],Ex[2],Ex[3],m), p) eq 0;
    end if;
    if p eq 5 then 
       assert SysLocal( Triples(Ex[1],Ex[2],Ex[3],m), p) eq 0;
    end if;
end for;


///////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////

// m = 37, cm = 6, bm = 32, am+bm = 67

// Extra cases when p = 3 and 2^2 || x, am*x-bm
// Extra cases when p = 5 and 2^3 || x, am*x-bm
// Extra cases when p = 7 and 2^4 || x, am*x-bm

m := 37;

p := 3;
al := 2;
// p:=5; 
// al:=3;
// p:=7; 
// al:=4;

am,bm,cm := ambmcm(m);
p2 := am+bm;

dels := [[0,0,0],[0,1,p-1],[0,p-1,1]];
bes :=  [[1,0,0],[0,1,0],[0,0,1]];

Ext := [];
for del in dels do
    for be in bes do
        Ext:= Ext cat [[2^al*3^be[1], 3^be[2]*p2^del[2], 2^al*3^be[3]*p2^del[3]]];
    end for;
end for;

for Ex in Ext do
    if p eq 3 then
       assert SysThue( Triples(Ex[1],Ex[2],Ex[3],m), p) eq 0;
    end if;
    if p in [5,7] then
       assert SysLocal( Triples(Ex[1],Ex[2],Ex[3],m), p) eq 0;
    end if;
end for;

///////////////////////////////////////////////////////////////////////////////////////////////////////////

// Remaining cases when p = 3 for m = 37

p:=3;

m := 37;
am,bm,cm := ambmcm(m);
p2 := am+bm;

als := [ [0,1,0],[2,0,2]];
dels := [ [0,0,0],[0,1,p-1],[0,p-1,1] ];
bes :=  [ [1,0,0],[0,1,0],[0,0,1] ];

Ext := [];
for al in als do
    for del in dels do
        for be in bes do
            Ext:= Ext cat [[2^al[1]*3^be[1], 2^al[2]*3^be[2]*p2^del[2], 2^al[3]*3^be[3]*p2^del[3]]];
        end for;
    end for;
end for;

for Ex in Ext do
    if SysThue( Triples(Ex[1],Ex[2],Ex[3],m), p) ne 0 then
       Ex;
    end if;
end for;

print "No unexpected solutions found from extra cases";

