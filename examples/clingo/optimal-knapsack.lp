item(a,3,4). item(b,4,5). item(c,2,3).   % item(Name, Weight, Value)
{ take(I) : item(I,_,_) }.
:- #sum { W,I : take(I), item(I,W,_) } > 6.
#maximize { V,I : take(I), item(I,_,V) }.
#show take/1.
