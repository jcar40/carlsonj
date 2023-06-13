
/*
	The programs in this package were written by Jon Carlson. 
	They are provided as a service to anyone who might be
	interested. There are no guarantees or implied warantees
	with this package. The programs are meant to run in MAGMA.
	To use the programs follow the instructions. 
*/

/*
	The programs below compute the module structure of a 
	permutation module M for a finite group G with point stabilizer
	H over a finite field k, as well as the structure of the 
	action algebra A which is the image of the group algebra kG 
	in End(M) and the Hecke algebra which is the commuting ring
	of A, Hom_{kG}(M,M). 

*/

     // 1). Enter the group, call it G. 
     // For example, write  "G := Sym(8);" or "G := PSL(3,5);".
     // Or you might try "load j1";

G :=        ;        
     
// 2). Define the subgroup H. For example, write 
     // "H := Normalizer(G,Sylow(G,2));". Or if G is the symmetric group
     // on 8 letters then you might want "H := YoungSubgroup([4,2,2])" to 
     // get the Young subgroup for the partition [4,2,2]. If you use the
     // YoungSubgroup function, then you must load this function into
     // Magma BEFORE you load this file. Simply copy the function given
     // below and load it into magma. 

H :=        ; 

     // 3). Define the field of coefficients k. It must be a finite field.
     // For example, "k := GF(4);".

k :=        ;

     // 4). Give the name of the file where the html output is to be written.
     //       The file name must be given in the form of a string (in quotes),
     //       and the string must be called    ast. 

ast := "     ";

     // 5). (optional) If you wish to see verbose output then uncomment 
     //         the following line.

// SetVerbose("Presentation",1);

     // 6)  Now load this file into MAGMA. 

//**********************************************************************

/* 
      The following are functions that are required required by varions 
      parts of the programs. These can be put into a separate file and 
      loaded into MAGMA if the user prefers.

*/


YoungSubgroup := function(P);
// Here P is a partition.

n := &+P;
G := Sym(n);
w := [x:x in P|x ne 1];
r := #w;
if r eq 0 then
H := sub<G|>;
elif r eq 1 then
H := G!!Sym(P[1]);
else
H := G!!DirectProduct([Sym(x):x in w]);
end if;

   return H;

end function;

//================================================================

Blocks:= function(CM); 

cm := Nrows(CM);
rows := [];
for k := 1 to cm do
   rows[k] := {x:x in [1 .. cm]|CM[k][x] ne 0};
end for;
flag := true;
bks := [];
while flag do
   a := rows[1];
   Remove(~rows,1);
   if #rows eq 0 then
      flag := false;
      Append(~bks,Sort(Setseq(a)));
   else 
      for j := #rows to 1 by -1 do
         if #(rows[j] meet a) ne 0 then 
            a := a join rows[j];
            Remove(~rows,j);
         end if;
      end for;
      Append(~bks,Sort(Setseq(a)));
      if #rows eq 0 then 
         flag := false;
      end if;
   end if;
end while;

return  bks;

end function;

//==================================================================

MakeProjectiveModule := function(A, F, n);

// we are creating projective module number n for the algebra A. F here
// is the free algebra covering A and the projective module is actually
// a module over F. The function assumes that the algebra is in standard
// form and that the projective module is small. 

ff := BaseRing(A);
g := Ngens(A);
// Ids := PrimitiveIdempotents(A);
bb := Basis(A);          // want something more clever if dim A is big.
d := Degree(A);
W := sub<KMatrixSpace(ff,d,d)|[A.n*x:x in bb]>;
                         // this can likely be improved.
cc := Basis(W);
ccc := [Vector(x):x in cc];
mat := KMatrixSpace(ff,#ccc,d^2)!ccc;
amats := [MatrixAlgebra(ff,#ccc)!
     [Solution(mat,Vector(cc[i]*A.j)):i in [1 .. #ccc]]:j in [1 .. Ngens(A)]];
M := AModule(F,amats);

return M;

end function;

//======================================================================

LoewyLayers := function(M);
// computes the radical filtration of M.


rads := [M];
flag := true;
while flag do
Append(~rads, JacobsonRadical(rads[#rads]));
if Dimension(rads[#rads]) eq 0 then
flag := false;
end if;
end while;

return rads;

end function;

//====================================================================

StructureOfRadicalFiltration := function(A,M);

// this assumes that the algebra of M is basic, but not 
// necessarily split basic. 

cc := SimpleQuotientAlgebras(A)`DegreesOfCenters;
S := [];
rads := LoewyLayers(M);
for i := 1 to #rads-1 do
L := quo<rads[i]|rads[i+1]>;
ssi := [Rank(Action(L).j) div cc[j]: j in [1 .. #cc]];
t := [];
for j := 1 to #cc do
if ssi[j] ne 0 then 
t cat:= [j : k in [1 .. ssi[j]]];
end if;
end for;
Append(~S,t);
end for;
 
return S;

end function;

//====================================================================

StructureOfSocleFiltration := function(A,M);

// Again we  that the algebra of M is basic, but not 
// necessarily split basic. 

LL := M;
cc := SimpleQuotientAlgebras(A)`DegreesOfCenters;
S := [];
flag := true;
while flag do

L := Socle(LL);
ssi := [Rank(Action(L).j) div cc[j]: j in [1 .. #cc]];
t := [];
for j := 1 to #cc do
if ssi[j] ne 0 then 
t cat:= [j : k in [1 .. ssi[j]]];
end if;
end for;
Append(~S,t);
if Dimension(L) eq Dimension (LL) then 
flag := false;
else 
LL := quo<LL|L>;
end if;
end while;
 
return Reverse(S);

end function;

//********************************************************************

CartanMatrixByRadicalFiltration := function(RF);

M := RMatrixSpace(Integers(),#RF,#RF)!0;
for i := 1 to #RF do 
for j := 1 to #RF do
M[i,j] := #[x:x in RF[i]|x eq j];
end for;
end for;

return M;

end function;

//********************************************************************

MinimallyGeneratedAlgebra := function(A);
// This is a stupid function for getting the minimal generators for
// an algebra A. Use this only in the case that the dimension of a 
// subalgebra is likely to be small (less than several thousand). 

d := Dimension(A);
n := 2;
flag := true;
while flag do
   for i := 1 to 5 do
      MM := MatrixAlgebra<BaseRing(A), Degree(A)|[Random(A): j in [1 .. n]]>;
      if Dimension(MM) eq d then 
         flag := true;
         return MM;
      end if;
   end for;
   n := n+1;
end while;

return MM;

end function;

//********************************************************************

ast;
PrintFile(ast, "<BODY><HTML>");
PrintFile(ast, "<body text = \"#AA0090\" bgcolor=\"#CCDDDD\">");
p := Characteristic(k);
PrintFile(ast,"<center><H1> Group G");
PrintFile(ast,"</H1></center>");
PrintFile(ast, G);

PrintFile(ast,"<center><H1> Subgroup H");
PrintFile(ast,"</H1></center>");
PrintFile(ast, H);

PrintFile(ast,"<center><H1> Field k");
PrintFile(ast,"</H1></center>");
PrintFile(ast, k);
PrintFile(ast,"<H3> The Hecke algebra for the group G with point 
stabilizer being the group H in characteristic  " 
cat  IntegerToString(p));
PrintFile(ast,"over the field k .</H4>");


M := PermutationModule(G, H, k);
A := Action(M);
time B := CondensedAlgebra(A);
PrintFile(ast,"<center><H2> The Module M </H2></center>");
PrintFile(ast,"The module M is the permutation module over the
field of chacteristic " cat IntegerToString(p) cat ", having point stablilizer
of order " cat IntegerToString(#H));
PrintFile(ast,". The dimension of M is  " cat IntegerToString(Dimension(M)) );
PrintFile(ast,". <br><br>");
N := RModule(B);
sf := StructureOfSocleFiltration(B,N);
rf := StructureOfRadicalFiltration(B,N);
PrintFile(ast,"The dimensions of the irreducible submodules modules are ");
aa := SimpleQuotientAlgebras(A)`DegreesOverCenters;	  
bb := SimpleQuotientAlgebras(A)`DegreesOfCenters;
cc := [aa[i]*bb[i]: i in [1 .. #aa]];
for j := 1 to #aa-1 do
PrintFile(ast,IntegerToString(cc[j]) cat ", ");
end for;
PrintFile(ast,IntegerToString(cc[#aa]));
PrintFile(ast,".<br><br>");
if #rf eq 1 then 
   PrintFile(ast,"The module M is semi-simple. It has composition factors");
   if #rf[1] eq 1 then 
      PrintFile(ast, IntegerToString(rf[1][1]) cat "<br>");
   else
      for v := 1 to #rf[1]-1 do
         PrintFile(ast, IntegerToString(rf[1][v]) cat ",");
      end for;
      PrintFile(ast, IntegerToString(rf[1][#rf[1]]));
      PrintFile(ast,"<br>");
   end if;	
else 
   PrintFile(ast,"The module M has radical filtration (Loewy series)");
   PrintFile(ast,"<br><center>");
   for u := 1 to #rf do
     if #rf[u] eq 1 then 
        PrintFile(ast, IntegerToString(rf[u][1]) cat "<br>");
     else
        for v := 1 to #rf[u]-1 do
           PrintFile(ast, IntegerToString(rf[u][v]) cat ",");
        end for;
        PrintFile(ast, IntegerToString(rf[u][#rf[u]]));
        PrintFile(ast,"<br>");
     end if;	 
   end for;
   PrintFile(ast,"</center><br><br>");
   PrintFile(ast,"The module M has socle filtration (socle series)");
   PrintFile(ast,"<br><center>");
   for u := 1 to #sf do
     if #sf[u] eq 1 then 
        PrintFile(ast, IntegerToString(sf[u][1]) cat "<br>");
     else
        for v := 1 to #sf[u]-1 do
           PrintFile(ast, IntegerToString(sf[u][v]) cat ",");
        end for;
        PrintFile(ast, IntegerToString(sf[u][#sf[u]]));
        PrintFile(ast,"<br>");
     end if;	 
   end for;
   PrintFile(ast,"</center><br><br>");
   UU := IndecomposableSummands(N);
   if #UU eq 1 then 
     PrintFile(ast,"The module M is indecomposable");
   else

     rfl := [StructureOfRadicalFiltration(B,x):x in UU];
     sfl := [StructureOfSocleFiltration(B,x):x in UU];
     vv := [0: j in [1 .. #aa+1]];
   for j := 1 to #rfl do
     if #rfl[j] eq 1 then 
        vv[rfl[j][1][1]] +:= 1;
     else 
        vv[#aa+1] +:= 1;
     end if;
   end for;
   if vv[#aa+1] ne 0 then
     if &+[vv[k]:k in [1 .. #aa]] eq 0 then
        PrintFile(ast,"<H4> The indecomposable components 
             of M have radical and 
             socle filtrations as follows: </H4>");
     else
        PrintFile(ast,"<H4> The module M has simple direct summands: </H4>");
        for j := 1 to #aa do
           if vv[j] ne 0 then 
             if vv[j] eq 1 then 
               PrintFile(ast, "<center>" cat IntegerToString(vv[j]) cat 
		        " copy of simple module number " 
                        cat IntegerToString(j) cat " </center>");
             else 
               PrintFile(ast, "<center>" cat IntegerToString(vv[j]) cat 
		      " copies of simple module number " 
                      cat IntegerToString(j) cat " </center>");
             end if;
           end if;
        end for;
        if vv[#aa+1] eq 1 then 
           PrintFile(ast,"<H4> The remaining indecomposable component of M 
              has radical and socle filtrations as follows: </H4>");
        else
           PrintFile(ast,"<H4> The remaining indecomposable components of M 
              have radical and socle filtrations as follows: </H4>");
        end if;
     end if;
     count := 1;
     for j := 1 to #UU do
        if #rfl[j] ne 1 then 
           if vv[#aa+1] ge 0 then 
             PrintFile(ast,"<H4> " cat IntegerToString(count) cat "). </H4>");
              count +:= 1;
           end if;
           rf := rfl[j];
           sf := sfl[j];
           PrintFile(ast,"<br><center> radical layers <br>");
           for u := 1 to #rf do
              if #rf[u] eq 1 then
                 PrintFile(ast, IntegerToString(rf[u][1]) cat "<br>");
              else
                 for v := 1 to #rf[u]-1 do
                    PrintFile(ast, IntegerToString(rf[u][v]) cat ",");
                 end for;
                 PrintFile(ast, IntegerToString(rf[u][#rf[u]]));
                 PrintFile(ast,"<br>");
              end if;
           end for;
           PrintFile(ast,"</center><br><br>");
           PrintFile(ast,"<br><center> socle layers <br>");
           for u := 1 to #sf do
              if #sf[u] eq 1 then
                 PrintFile(ast, IntegerToString(sf[u][1]) cat "<br>");
              else
                 for v := 1 to #sf[u]-1 do
                    PrintFile(ast, IntegerToString(sf[u][v]) cat ",");
                 end for;
                 PrintFile(ast, IntegerToString(sf[u][#sf[u]]));
                 PrintFile(ast,"<br>");
              end if;
           end for;
           PrintFile(ast,"</center><br><br>");

        end if;
     end for;
   end if;     // vv[#aa+1] ne 0
  end if;     // #UU eq 1
end if;       // #rf eq 1
PrintFile(ast,"<center><H2> The Action Algebra </H2></center>");
PrintFile(ast,"The action algebra A is the image of kG in the 
k-endomorphism ring of M. It's simple modules are the irreducible
submodules of M.");
PrintFile(ast,"<br><br>");

if #rf eq 1 then
PrintFile(ast,"The algebra A is a direct product of matrix algebras
of dimension ");
   if #aa eq 1 then 
      PrintFile(ast, IntegerToString(aa[1]));
   else
      for v := 1 to #aa-1 do
         PrintFile(ast, IntegerToString(aa[v]) cat ",");
      end for;
      PrintFile(ast, IntegerToString(aa[#aa]));
   end if;
PrintFile(ast,"  over field extensions of the base field of degrees  ");
	   if #bb eq 1 then 
      PrintFile(ast, IntegerToString(bb[1]));
   else
      for v := 1 to #bb-1 do
         PrintFile(ast, IntegerToString(bb[v]) cat ",");
      end for;
      PrintFile(ast, IntegerToString(bb[#bb]));
PrintFile(ast, ".<br>");
   end if;

else       // #rf eq 1

P := FreeAlgebra(BaseRing(A),Ngens(B));
pm := [MakeProjectiveModule(B,P,j): j in [ 1 .. #aa]]; 
rfa := [StructureOfRadicalFiltration(B,pm[j]): j in [1 .. #aa]];
print rfa;
rfb := [&cat x: x in rfa];
print rfb;
CM := CartanMatrixByRadicalFiltration(rfb);
print CM;
dd := [&+[CM[j][k]*cc[k]: k in [1 .. #aa]]: j in [1 .. #aa]];

PrintFile(ast,"The dimensions of the projective modules are ");
for j := 1 to #aa-1 do
PrintFile(ast,IntegerToString(dd[j]) cat ", ");
end for;
PrintFile(ast,IntegerToString(dd[#aa]));
PrintFile(ast,".<br><br>");

PrintFile(ast,"<H4> The cartan matrix of A is </H4>");
PrintFile(ast,"<br>");
PrintFile(ast,"<ul>");
ncm := Nrows(CM);
   if ncm eq 1 then 
      PrintFile(ast, CM[1][1]);
   else 
      for u := 1 to ncm do
         for v := 1 to ncm -1 do
            PrintFile(ast, IntegerToString(CM[u][v]) cat ",");
         end for;
         PrintFile(ast, IntegerToString(CM[u][ncm]));
         PrintFile(ast,"<br>");
      end for;
   end if;
PrintFile(ast,"</ul>");
PrintFile(ast,"<br>");
PrintFile(ast,"The determinant of the Cartan matrix is " cat 
IntegerToString(Determinant(CM)) cat ".<br><br>");

BL := Blocks(CM);
if #BL gt 1 then
   PrintFile(ast,"<H4> The blocks of A consist of the following irreducible
   modules: </H4>");
   PrintFile(ast,"<ul>");
   for j := 1 to #BL do
      PrintFile(ast," (" cat IntegerToString(j) cat "). ");
      if #BL[j] eq 1 then 
         PrintFile(ast, IntegerToString(BL[j][1]) cat " <br>");
      else
         for k := 1 to #BL[j]-1 do
            PrintFile(ast,IntegerToString(BL[j][k]) cat ", ");
         end for;
         PrintFile(ast,IntegerToString(BL[j][#BL[j]]) cat "<br>");
      end if;
   end for;
   PrintFile(ast,"</ul>");
end if;

dda := [j: j in [1 .. #dd]|dd[j] eq cc[j]];
ddb := [j: j in [1 .. #dd]|dd[j] ne cc[j]];

if #ddb gt 0 then 
   if #dda eq 0 then
     PrintFile(ast,"<H4>The radical and socle filtrations of the projective 
         modules for A are the following:</H4>");
   elif #dda eq 1 then 
     PrintFile(ast,"<H4>Projective module number " cat 
         IntegerToString(dda[1]) cat " is simple.</H4>");
     if #ddb eq 1 then 
        PrintFile(ast,"<H4>The radical and socle filtrations of the remaining
         projective module for A are the following:</H4>");
     else 
        PrintFile(ast,"<H4>The radical and socle filtrations of the remaining
         projective modules for A are the following:</H4>");
    end if;


   else
     PrintFile(ast,"<H4>Projective modules number ");
     for j := 1 to #dda -1 do 
        PrintFile(ast,IntegerToString(dda[j]) cat ", ");
     end for;
     PrintFile(ast,IntegerToString(dda[#dda]));
     PrintFile(ast," are simple.</H4>");
     if #ddb eq 1 then 
        PrintFile(ast,"<H4>The radical and socle filtrations of the remaining
         projective module for A are the following:</H4>");
     else 
        PrintFile(ast,"<H4>The radical and socle filtrations of the remaining
         projective modules for A are the following:</H4>");
     end if;
   end if;

for j in ddb do
PrintFile(ast,"<br><H4>Projective module number " cat IntegerToString(j) cat
"</H4>");
sf := StructureOfSocleFiltration(B,pm[j]);
rf := rfa[j];
PrintFile(ast,"<br><center> radical layers <br>");
for u := 1 to #rf do
   if #rf[u] eq 1 then
      PrintFile(ast, IntegerToString(rf[u][1]) cat "<br>");
   else
      for v := 1 to #rf[u]-1 do
         PrintFile(ast, IntegerToString(rf[u][v]) cat ",");
      end for;
      PrintFile(ast, IntegerToString(rf[u][#rf[u]]));
      PrintFile(ast,"<br>");
   end if;
end for;
PrintFile(ast,"</center><br><br>");
PrintFile(ast,"<br><center> socle layers <br>");
for u := 1 to #sf do
   if #sf[u] eq 1 then
      PrintFile(ast, IntegerToString(sf[u][1]) cat "<br>");
   else
      for v := 1 to #sf[u]-1 do
         PrintFile(ast, IntegerToString(sf[u][v]) cat ",");
      end for;
      PrintFile(ast, IntegerToString(sf[u][#sf[u]]));
      PrintFile(ast,"<br>");
   end if;
end for;
PrintFile(ast,"</center><br><br>");
end for;
end if;

PrintFile(ast,"The degrees of the splitting fields are ");
uu := SimpleQuotientAlgebras(A)`DegreesOfCenters;
   for v := 1 to #uu -1 do
      PrintFile(ast, IntegerToString(uu[v]) cat ", ");
   end for;
   PrintFile(ast, uu[#uu]);
   PrintFile(ast,".<br><br>");
N := RModule(B);
E := AHom(N,N);
EE := MatrixAlgebra<k,Nrows(E.1)|[E.i: i in [1 .. Ngens(E)]]>;
DE := MinimallyGeneratedAlgebra(EE);
FE := CondensedAlgebra(DE);
ag := AlgebraGenerators(FE);
CE := MatrixAlgebra<BaseRing(FE), Degree(FE)| ag`PrimitiveIdempotents cat
		    ag`SequenceRadicalGenerators>;

//=======================================================================

PrintFile(ast,"<center><H2> The Hecke Algebra </H2></center>");
PrintFile(ast,"The Hecke algebra H of the module M is the A-endomorphism
ring of M.");
PrintFile(ast,"<br><br>");

PrintFile(ast,"The dimension of H is ");
PrintFile(ast,Dimension(EE));
PrintFile(ast,".<br>");
PrintFile(ast,"<br>");

PrintFile(ast,"The dimensions of the irreducible H-modules are ");
aa := SimpleQuotientAlgebras(DE)`DegreesOverCenters;	  
bb := SimpleQuotientAlgebras(DE)`DegreesOfCenters;
cc := [aa[i]*bb[i]: i in [1 .. #aa]];
for j := 1 to #aa-1 do
PrintFile(ast,IntegerToString(cc[j]) cat ", ");
end for;
PrintFile(ast,IntegerToString(cc[#aa]));
PrintFile(ast,".<br><br>");
print aa, bb;
//------

PrintFile(ast,"The degrees of the splitting fields are ");
uu := SimpleQuotientAlgebras(DE)`DegreesOfCenters;
   for v := 1 to #uu -1 do
      PrintFile(ast, IntegerToString(uu[v]) cat ", ");
   end for;
   PrintFile(ast, uu[#uu]);
   PrintFile(ast,".<br><br>");

P := FreeAlgebra(BaseRing(A),Ngens(CE));
pm := [MakeProjectiveModule(CE,P,j): j in [ 1 .. #aa]];
rfa := [StructureOfRadicalFiltration(CE,pm[j]): j in [1 .. #aa]];
rfb := [&cat x: x in rfa];
CM := CartanMatrixByRadicalFiltration(rfb);
dd := [&+[CM[j][k]*cc[k]: k in [1 .. #aa]]: j in [1 .. #aa]];

PrintFile(ast,"The dimensions of the projective modules of H are ");
for j := 1 to #aa-1 do
PrintFile(ast,IntegerToString(&+[CM[j][k]*cc[k]: k in [1 .. #aa]]) cat ", ");
end for;
PrintFile(ast,IntegerToString(&+[CM[#aa][k]*cc[k]: k in [1 .. #aa]]));
PrintFile(ast,".<br><br>");

PrintFile(ast,"<H4> The cartan matrix of H is </H4>");
PrintFile(ast,"<br>");
PrintFile(ast,"<ul>");
ncm := Nrows(CM);
   if ncm eq 1 then
      PrintFile(ast, CM[1][1]);
   else
      for u := 1 to ncm do
         for v := 1 to ncm -1 do
            PrintFile(ast, IntegerToString(CM[u][v]) cat ",");
         end for;
         PrintFile(ast, IntegerToString(CM[u][ncm]));
         PrintFile(ast,"<br>");
      end for;
   end if;
PrintFile(ast,"</ul>");
PrintFile(ast,"<br>");
PrintFile(ast,"The determinant of the Cartan matrix is " cat 
IntegerToString(Determinant(CM)) cat ".<br><br>");

//--------------

BL := Blocks(CM);
if #BL gt 1 then
   PrintFile(ast,"<H4> The blocks of H consist of the following irreducible
   modules: </H4>");
   PrintFile(ast,"<ul>");
   for j := 1 to #BL do
      PrintFile(ast," (" cat IntegerToString(j) cat "). ");
      if #BL[j] eq 1 then 
         PrintFile(ast, IntegerToString(BL[j][1]) cat " <br>");
      else
         for k := 1 to #BL[j]-1 do
            PrintFile(ast,IntegerToString(BL[j][k]) cat ", ");
         end for;
         PrintFile(ast,IntegerToString(BL[j][#BL[j]]) cat "<br>");
      end if;
   end for;
   PrintFile(ast,"</ul>");
end if;



//--------------

dd := [&+[CM[j][k]*cc[k]: k in [1 .. #aa]]: j in [1 .. #aa]];

dda := [j: j in [1 .. #dd]|dd[j] eq cc[j]];
ddb := [j: j in [1 .. #dd]|dd[j] ne cc[j]];

if #ddb gt 0 then
   if #dda eq 0 then
     PrintFile(ast,"<H4>The radical and socle filtrations of the projective
         modules for H are the following:</H4>");
   elif #dda eq 1 then
     PrintFile(ast,"<H4>Projective module number " cat
         IntegerToString(dda[1]) cat " is simple.</H4>");
     if #ddb eq 1 then
        PrintFile(ast,"<H4>The radical and socle filtrations of the remaining
         projective module for H are the following:</H4>");
     else
        PrintFile(ast,"<H4>The radical and socle filtrations of the remaining
         projective modules for H are the following:</H4>");
     end if;
   else
     PrintFile(ast,"<H4>Projective modules number ");
     for j := 1 to #dda -1 do
        PrintFile(ast,IntegerToString(dda[j]) cat ", ");
     end for;
     PrintFile(ast,IntegerToString(dda[#dda]));
     PrintFile(ast," are simple.</H4>");
     if #ddb eq 1 then
        PrintFile(ast,"<H4>The radical and socle filtrations of the remaining
         projective module for H are the following:</H4>");
     else
        PrintFile(ast,"<H4>The radical and socle filtrations of the remaining
         projective modules for H are the following:</H4>");
     end if;
   end if;

for j in ddb do
PrintFile(ast,"<br><H4>Projective module number " cat IntegerToString(j) cat
"</H4>");
sf := StructureOfSocleFiltration(CE,pm[j]);
rf := rfa[j];
PrintFile(ast,"<br><center> radical layers <br>");
for u := 1 to #rf do
   if #rf[u] eq 1 then
      PrintFile(ast, IntegerToString(rf[u][1]) cat "<br>");
   else
      for v := 1 to #rf[u]-1 do
         PrintFile(ast, IntegerToString(rf[u][v]) cat ",");
      end for;
      PrintFile(ast, IntegerToString(rf[u][#rf[u]]));
      PrintFile(ast,"<br>");
   end if;
end for;
PrintFile(ast,"</center><br><br>");
PrintFile(ast,"<br><center> socle layers <br>");
for u := 1 to #sf do
   if #sf[u] eq 1 then
      PrintFile(ast, IntegerToString(sf[u][1]) cat "<br>");
   else
      for v := 1 to #sf[u]-1 do
         PrintFile(ast, IntegerToString(sf[u][v]) cat ",");
      end for;
      PrintFile(ast, IntegerToString(sf[u][#sf[u]]));
      PrintFile(ast,"<br>");
   end if;
end for;
PrintFile(ast,"</center><br><br>");
end for;
end if;

end if;                                // #rf eq 1;

//--------------

