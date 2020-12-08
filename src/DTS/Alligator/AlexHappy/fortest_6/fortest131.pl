:- style_check(-singleton).

:-use_module(swi_alligator,[prove/2]).
:- op(500,xfx,:).
:- op(300,yfx,-).
:- op(400,xfy,=>).
:- op(400,xfy,&).
:- op(300,fy,~).
:- dynamic checktheorem/6.
writeResult(Logic,ID,Prediction,Gold,Fname) :-
format('~w&~w&~w&~w&~w~n', [Logic,ID,Prediction,Gold,Fname]).
evalyes(Logic,ID) :-
  checkTheorem(Logic,ID,Context,Theorem,Gold,Fname),
  ( prove(Context,_ : Theorem) -> writeResult(Logic,ID,yes,Gold,Fname)).
evalno(Logic,ID) :-
  checkTheorem(Logic,ID,Context,Theorem,Gold,Fname),
  ( prove(Context,_ : ( ~ (Theorem) ) ) -> writeResult(Logic,ID,no,Gold,Fname) ).
checkTheorem(syn , 762 , [ type:set ,bigX4 : (( type )) , bigX3 : (( type )) , bigX17 : (( type )) , bigX16 : (( type )) , bigX15 : (( type )) , bigX14 : (( type )) , bigX13 : (( type )) , bigX12 : (( type )) , bigX11 : (( type )) , bigX10 : (( type )) , bigX22 : (( type )) , bigX23 : (( type )) , bigX21 : (( type )) , bigX20 : (( type )) , c14 : (( type )) , f6 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX26 : (( type )) , p8 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX25 : (( type )) , bigX24 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX2 : (( type )) , bigX1 : (( type )) , bigX8 : (( type )) , bigX7 : (( type )) , bigX6 : (( type )) , bigX5 : (( type )) , bigX19 : (( type )) , bigX18 : (( type )) , f7 : (( ( type ) ) -> ( ( prop ) )) , bigX9 : (( ( type ) ) -> ( ( prop ) )) , f4 : (( ( type ) ) -> ( ( prop ) )) , f5 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , c13 : (( type )) , c12 : (( ( type ) ) -> ( ( prop ) )) , c11 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , f3 : (( ( type ) ) -> ( ( prop ) )) , c10 : (( type )) , c9 : (( ( type ) ) -> ( ( prop ) )) , p2 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX0 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) ] , ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ~( ( ( p2 ) )-( ( bigX0 ) )-( ( bigX0 ) ) ) ) ) & ( ~( ( ( p2 ) )-( ( c9 ) )-( ( ( f3 ) )-( ( c10 ) ) ) ) ) ) ) & ( ( ( p2 ) )-( ( c11 ) )-( ( ( f4 ) )-( ( ( f5 ) )-( ( c12 ) )-( ( c13 ) ) ) ) ) ) ) & ( ( ( p2 ) )-( ( ( f4 ) )-( ( bigX9 ) ) )-( ( ( f5 ) )-( ( bigX9 ) )-( ( ( f3 ) )-( ( ( f7 ) )-( ( c10 ) ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f7 ) )-( ( bigX18 ) ) )-( ( ( f7 ) )-( ( bigX19 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX18 ) )-( ( bigX19 ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f3 ) )-( ( bigX5 ) ) )-( ( ( f3 ) )-( ( bigX6 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX5 ) )-( ( bigX6 ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f4 ) )-( ( bigX7 ) ) )-( ( ( f4 ) )-( ( bigX8 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX7 ) )-( ( bigX8 ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( bigX1 ) )-( ( bigX2 ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX0 ) )-( ( bigX1 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX0 ) )-( ( bigX2 ) ) ) ) ) ) ) ) & ( ( ( ( p8 ) )-( ( bigX24 ) )-( ( bigX25 ) ) ) \/ ( ( ~( ( ( p8 ) )-( ( bigX24 ) )-( ( bigX26 ) ) ) ) \/ ( ~( ( ( p8 ) )-( ( bigX26 ) )-( ( bigX25 ) ) ) ) ) ) ) ) & ( ( ( p8 ) )-( ( ( f6 ) )-( ( c9 ) )-( ( ( f4 ) )-( ( c12 ) ) ) )-( ( ( f6 ) )-( ( c9 ) )-( ( ( f4 ) )-( ( ( f5 ) )-( ( c12 ) )-( ( c14 ) ) ) ) ) ) ) ) & ( ~( ( ( p8 ) )-( ( ( f6 ) )-( ( c9 ) )-( ( ( f4 ) )-( ( c12 ) ) ) )-( ( ( f6 ) )-( ( c9 ) )-( ( ( f4 ) )-( ( ( f4 ) )-( ( ( f5 ) )-( ( c12 ) )-( ( c14 ) ) ) ) ) ) ) ) ) ) & ( ( ( ( p8 ) )-( ( bigX20 ) )-( ( bigX21 ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX23 ) )-( ( bigX21 ) ) ) ) \/ ( ( ~( ( ( p8 ) )-( ( bigX22 ) )-( ( bigX23 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX22 ) )-( ( bigX20 ) ) ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f5 ) )-( ( bigX10 ) )-( ( bigX11 ) ) )-( ( ( f5 ) )-( ( bigX12 ) )-( ( bigX13 ) ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX10 ) )-( ( bigX12 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX11 ) )-( ( bigX13 ) ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f6 ) )-( ( bigX14 ) )-( ( bigX15 ) ) )-( ( ( f6 ) )-( ( bigX16 ) )-( ( bigX17 ) ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX15 ) )-( ( bigX17 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX14 ) )-( ( bigX16 ) ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( bigX3 ) )-( ( ( f3 ) )-( ( c10 ) ) ) ) \/ ( ( ( p8 ) )-( ( ( f6 ) )-( ( bigX3 ) )-( ( bigX4 ) ) )-( ( ( f6 ) )-( ( bigX3 ) )-( ( ( f5 ) )-( ( bigX4 ) )-( ( ( f3 ) )-( ( ( f7 ) )-( ( c10 ) ) ) ) ) ) ) ) , no , '../../TPTP-v7.3.0/Problems/SYN/SYN560-1.p').
checkTheorem(syn , 763 , [ type:set ,bigX27 : (( type )) , bigX28 : (( type )) , bigX14 : (( type )) , bigX13 : (( type )) , bigX12 : (( type )) , bigX11 : (( type )) , bigX18 : (( type )) , bigX17 : (( type )) , bigX16 : (( type )) , bigX15 : (( type )) , bigX6 : (( type )) , bigX5 : (( type )) , bigX4 : (( type )) , bigX3 : (( type )) , bigX21 : (( type )) , bigX22 : (( type )) , bigX20 : (( type )) , bigX19 : (( type )) , bigX25 : (( type )) , bigX26 : (( type )) , bigX24 : (( type )) , bigX23 : (( type )) , bigX2 : (( type )) , bigX1 : (( type )) , bigX8 : (( type )) , bigX7 : (( type )) , bigX10 : (( type )) , bigX9 : (( type )) , f3 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , c13 : (( type )) , f4 : (( ( type ) ) -> ( ( prop ) )) , f5 : (( ( type ) ) -> ( ( prop ) )) , c12 : (( ( type ) ) -> ( ( prop ) )) , c16 : (( type )) , f6 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , c15 : (( type )) , f7 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , p8 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , c11 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , p9 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , c10 : (( type )) , c14 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , p2 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX0 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) ] , ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ~( ( ( p2 ) )-( ( bigX0 ) )-( ( bigX0 ) ) ) ) ) & ( ( ( p9 ) )-( ( c14 ) )-( ( c10 ) ) ) ) ) & ( ( ( p8 ) )-( ( c11 ) )-( ( c14 ) ) ) ) ) & ( ( ( p2 ) )-( ( ( f7 ) )-( ( c10 ) )-( ( c14 ) ) )-( ( c15 ) ) ) ) ) & ( ( ( p2 ) )-( ( ( f6 ) )-( ( c15 ) )-( ( c11 ) ) )-( ( c16 ) ) ) ) ) & ( ( ( p2 ) )-( ( ( f3 ) )-( ( ( f4 ) )-( ( ( f5 ) )-( ( c12 ) ) ) )-( ( c13 ) ) )-( ( c16 ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f5 ) )-( ( bigX9 ) ) )-( ( ( f5 ) )-( ( bigX10 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX9 ) )-( ( bigX10 ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f4 ) )-( ( bigX7 ) ) )-( ( ( f4 ) )-( ( bigX8 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX7 ) )-( ( bigX8 ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( bigX1 ) )-( ( bigX2 ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX0 ) )-( ( bigX1 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX0 ) )-( ( bigX2 ) ) ) ) ) ) ) ) & ( ( ( ( p9 ) )-( ( bigX23 ) )-( ( bigX24 ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX26 ) )-( ( bigX24 ) ) ) ) \/ ( ( ~( ( ( p9 ) )-( ( bigX25 ) )-( ( bigX26 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX25 ) )-( ( bigX23 ) ) ) ) ) ) ) ) ) & ( ( ( ( p8 ) )-( ( bigX19 ) )-( ( bigX20 ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX22 ) )-( ( bigX20 ) ) ) ) \/ ( ( ~( ( ( p8 ) )-( ( bigX21 ) )-( ( bigX22 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX21 ) )-( ( bigX19 ) ) ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f3 ) )-( ( bigX3 ) )-( ( bigX4 ) ) )-( ( ( f3 ) )-( ( bigX5 ) )-( ( bigX6 ) ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX3 ) )-( ( bigX5 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX4 ) )-( ( bigX6 ) ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f7 ) )-( ( bigX15 ) )-( ( bigX16 ) ) )-( ( ( f7 ) )-( ( bigX17 ) )-( ( bigX18 ) ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX15 ) )-( ( bigX17 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX16 ) )-( ( bigX18 ) ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f6 ) )-( ( bigX11 ) )-( ( bigX12 ) ) )-( ( ( f6 ) )-( ( bigX13 ) )-( ( bigX14 ) ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX12 ) )-( ( bigX14 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX11 ) )-( ( bigX13 ) ) ) ) ) ) ) ) & ( ( ~( ( ( p9 ) )-( ( bigX28 ) )-( ( c10 ) ) ) ) \/ ( ( ~( ( ( p8 ) )-( ( c11 ) )-( ( bigX28 ) ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( ( f7 ) )-( ( c10 ) )-( ( bigX28 ) ) )-( ( bigX27 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( ( f6 ) )-( ( bigX27 ) )-( ( c11 ) ) )-( ( ( f3 ) )-( ( ( f4 ) )-( ( ( f5 ) )-( ( c12 ) ) ) )-( ( c13 ) ) ) ) ) ) ) ) , no , '../../TPTP-v7.3.0/Problems/SYN/SYN561-1.p').
checkTheorem(syn , 764 , [ type:set ,bigX3 : (( type )) , bigX2 : (( type )) , bigX1 : (( type )) , bigX0 : (( type )) , bigX21 : (( type )) , bigX20 : (( type )) , bigX6 : (( type )) , bigX5 : (( type )) , bigX10 : (( type )) , f4 : (( ( type ) ) -> ( ( prop ) )) , bigX9 : (( ( type ) ) -> ( ( prop ) )) , bigX12 : (( type )) , f5 : (( ( type ) ) -> ( ( prop ) )) , bigX11 : (( ( type ) ) -> ( ( prop ) )) , bigX14 : (( type )) , f7 : (( ( type ) ) -> ( ( prop ) )) , bigX13 : (( ( type ) ) -> ( ( prop ) )) , bigX16 : (( type )) , bigX15 : (( type )) , bigX18 : (( type )) , bigX17 : (( type )) , bigX8 : (( type )) , bigX7 : (( type )) , f8 : (( ( type ) ) -> ( ( prop ) )) , f3 : (( ( type ) ) -> ( ( prop ) )) , c12 : (( type )) , f9 : (( ( type ) ) -> ( ( prop ) )) , c11 : (( ( type ) ) -> ( ( prop ) )) , p10 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX22 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , p6 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX19 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , p2 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX4 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) ] , ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ~( ( ( p2 ) )-( ( bigX4 ) )-( ( bigX4 ) ) ) ) ) & ( ( ( p6 ) )-( ( bigX19 ) )-( ( bigX19 ) ) ) ) ) & ( ~( ( ( p10 ) )-( ( bigX22 ) )-( ( bigX22 ) ) ) ) ) ) & ( ( ( p2 ) )-( ( ( f9 ) )-( ( c11 ) ) )-( ( ( f3 ) )-( ( c12 ) ) ) ) ) ) & ( ( ( p2 ) )-( ( ( f8 ) )-( ( c11 ) ) )-( ( ( f3 ) )-( ( c12 ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f3 ) )-( ( bigX7 ) ) )-( ( ( f3 ) )-( ( bigX8 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX7 ) )-( ( bigX8 ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f9 ) )-( ( bigX17 ) ) )-( ( ( f9 ) )-( ( bigX18 ) ) ) ) \/ ( ~( ( ( p6 ) )-( ( bigX17 ) )-( ( bigX18 ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f8 ) )-( ( bigX15 ) ) )-( ( ( f8 ) )-( ( bigX16 ) ) ) ) \/ ( ~( ( ( p6 ) )-( ( bigX15 ) )-( ( bigX16 ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f7 ) )-( ( bigX13 ) ) )-( ( ( f7 ) )-( ( bigX14 ) ) ) ) \/ ( ~( ( ( p6 ) )-( ( bigX13 ) )-( ( bigX14 ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f5 ) )-( ( bigX11 ) ) )-( ( ( f5 ) )-( ( bigX12 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX11 ) )-( ( bigX12 ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f4 ) )-( ( bigX9 ) ) )-( ( ( f4 ) )-( ( bigX10 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX9 ) )-( ( bigX10 ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( bigX5 ) )-( ( bigX6 ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX4 ) )-( ( bigX5 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX4 ) )-( ( bigX6 ) ) ) ) ) ) ) ) & ( ( ( ( p6 ) )-( ( bigX20 ) )-( ( bigX21 ) ) ) \/ ( ( ~( ( ( p6 ) )-( ( bigX19 ) )-( ( bigX20 ) ) ) ) \/ ( ~( ( ( p6 ) )-( ( bigX19 ) )-( ( bigX21 ) ) ) ) ) ) ) ) & ( ( ( ( p10 ) )-( ( bigX0 ) )-( ( bigX1 ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX2 ) )-( ( bigX0 ) ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX3 ) )-( ( bigX1 ) ) ) ) \/ ( ~( ( ( p10 ) )-( ( bigX2 ) )-( ( bigX3 ) ) ) ) ) ) ) ) ) & ( ( ( p2 ) )-( ( ( f7 ) )-( ( c11 ) ) )-( ( ( f3 ) )-( ( ( f4 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( c12 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) & ( ( ( p10 ) )-( ( ( f7 ) )-( ( c11 ) ) )-( ( ( f3 ) )-( ( ( f4 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( ( f5 ) )-( ( c12 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) , no , '../../TPTP-v7.3.0/Problems/SYN/SYN562-1.p').
checkTheorem(syn , 765 , [ type:set ,bigX14 : (( type )) , bigX15 : (( type )) , bigX13 : (( type )) , bigX12 : (( type )) , bigX25 : (( type )) , bigX26 : (( type )) , bigX24 : (( type )) , bigX23 : (( type )) , bigX9 : (( type )) , bigX8 : (( type )) , bigX7 : (( type )) , bigX19 : (( type )) , bigX18 : (( type )) , bigX17 : (( type )) , bigX2 : (( type )) , bigX1 : (( type )) , bigX6 : (( type )) , bigX5 : (( type )) , bigX4 : (( type )) , bigX3 : (( type )) , bigX27 : (( type )) , bigX11 : (( type )) , bigX10 : (( type )) , bigX16 : (( type )) , p5 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX21 : (( type )) , bigX20 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , f3 : (( ( type ) ) -> ( ( prop ) )) , c8 : (( type )) , f4 : (( ( type ) ) -> ( ( prop ) )) , c7 : (( ( type ) ) -> ( ( prop ) )) , p6 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX22 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , p2 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX0 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) ] , ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ~( ( ( p2 ) )-( ( bigX0 ) )-( ( bigX0 ) ) ) ) ) & ( ( ( p6 ) )-( ( bigX22 ) )-( ( bigX22 ) ) ) ) ) & ( ~( ( ( p6 ) )-( ( ( f4 ) )-( ( c7 ) ) )-( ( c8 ) ) ) ) ) ) & ( ( ( p2 ) )-( ( ( f4 ) )-( ( c7 ) ) )-( ( ( f4 ) )-( ( c8 ) ) ) ) ) ) & ( ~( ( ( p6 ) )-( ( ( f4 ) )-( ( c7 ) ) )-( ( ( f3 ) )-( ( ( f4 ) )-( ( c8 ) ) ) ) ) ) ) ) & ( ( ( ( p6 ) )-( ( bigX20 ) )-( ( bigX21 ) ) ) \/ ( ~( ( ( p5 ) )-( ( bigX20 ) )-( ( bigX21 ) ) ) ) ) ) ) & ( ( ( p5 ) )-( ( ( f3 ) )-( ( ( f3 ) )-( ( bigX16 ) ) ) )-( ( ( f3 ) )-( ( ( f4 ) )-( ( bigX16 ) ) ) ) ) ) ) & ( ( ( ( p5 ) )-( ( bigX10 ) )-( ( bigX11 ) ) ) \/ ( ~( ( ( p6 ) )-( ( ( f4 ) )-( ( bigX10 ) ) )-( ( bigX11 ) ) ) ) ) ) ) & ( ( ( ( p6 ) )-( ( c7 ) )-( ( ( f3 ) )-( ( bigX27 ) ) ) ) \/ ( ~( ( ( p6 ) )-( ( c7 ) )-( ( bigX27 ) ) ) ) ) ) ) & ( ( ( ( p6 ) )-( ( ( f4 ) )-( ( bigX10 ) ) )-( ( bigX11 ) ) ) \/ ( ~( ( ( p5 ) )-( ( bigX10 ) )-( ( bigX11 ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f3 ) )-( ( bigX3 ) ) )-( ( ( f3 ) )-( ( bigX4 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX3 ) )-( ( bigX4 ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f4 ) )-( ( bigX5 ) ) )-( ( ( f4 ) )-( ( bigX6 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX5 ) )-( ( bigX6 ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( bigX1 ) )-( ( bigX2 ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX0 ) )-( ( bigX1 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX0 ) )-( ( bigX2 ) ) ) ) ) ) ) ) & ( ( ( ( p6 ) )-( ( bigX17 ) )-( ( bigX18 ) ) ) \/ ( ( ~( ( ( p6 ) )-( ( bigX17 ) )-( ( bigX19 ) ) ) ) \/ ( ~( ( ( p6 ) )-( ( bigX19 ) )-( ( bigX18 ) ) ) ) ) ) ) ) & ( ( ( ( p5 ) )-( ( bigX7 ) )-( ( bigX8 ) ) ) \/ ( ( ~( ( ( p5 ) )-( ( bigX9 ) )-( ( bigX8 ) ) ) ) \/ ( ~( ( ( p6 ) )-( ( bigX7 ) )-( ( bigX9 ) ) ) ) ) ) ) ) & ( ( ( ( p6 ) )-( ( bigX23 ) )-( ( bigX24 ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX26 ) )-( ( bigX23 ) ) ) ) \/ ( ( ~( ( ( p6 ) )-( ( bigX26 ) )-( ( bigX25 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX25 ) )-( ( bigX24 ) ) ) ) ) ) ) ) ) & ( ( ( ( p5 ) )-( ( bigX12 ) )-( ( bigX13 ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX15 ) )-( ( bigX13 ) ) ) ) \/ ( ( ~( ( ( p5 ) )-( ( bigX14 ) )-( ( bigX15 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX14 ) )-( ( bigX12 ) ) ) ) ) ) ) , no , '../../TPTP-v7.3.0/Problems/SYN/SYN563-1.p').
checkTheorem(syn , 766 , [ type:set ,bigX29 : (( type )) , bigX28 : (( type )) , bigX27 : (( type )) , bigX26 : (( type )) , bigX22 : (( type )) , bigX21 : (( type )) , bigX20 : (( type )) , bigX19 : (( type )) , bigX15 : (( type )) , bigX14 : (( type )) , bigX13 : (( type )) , bigX12 : (( type )) , bigX37 : (( type )) , bigX36 : (( type )) , bigX35 : (( type )) , bigX34 : (( type )) , bigX3 : (( type )) , bigX2 : (( type )) , bigX1 : (( type )) , bigX0 : (( type )) , bigX6 : (( type )) , bigX5 : (( type )) , bigX4 : (( type )) , f9 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , c12 : (( type )) , c11 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , p10 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , f3 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX8 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX7 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX25 : (( type )) , bigX24 : (( type )) , bigX11 : (( type )) , bigX10 : (( type )) , bigX31 : (( type )) , bigX30 : (( type )) , bigX17 : (( type )) , bigX16 : (( type )) , bigX33 : (( type )) , bigX32 : (( type )) , f6 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , f8 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX39 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX38 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , f5 : (( ( type ) ) -> ( ( prop ) )) , f7 : (( ( type ) ) -> ( ( prop ) )) , bigX18 : (( ( type ) ) -> ( ( prop ) )) , p4 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX23 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , p2 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX9 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) ] , ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ~( ( ( p2 ) )-( ( bigX9 ) )-( ( bigX9 ) ) ) ) ) & ( ( ( p4 ) )-( ( bigX23 ) )-( ( bigX23 ) ) ) ) ) & ( ( ( p2 ) )-( ( ( f5 ) )-( ( ( f7 ) )-( ( bigX18 ) ) ) )-( ( ( f5 ) )-( ( bigX18 ) ) ) ) ) ) & ( ( ( p4 ) )-( ( ( f8 ) )-( ( bigX38 ) )-( ( bigX39 ) ) )-( ( ( f6 ) )-( ( bigX38 ) )-( ( ( f7 ) )-( ( bigX39 ) ) ) ) ) ) ) & ( ( ( p4 ) )-( ( ( f7 ) )-( ( ( f8 ) )-( ( bigX32 ) )-( ( bigX33 ) ) ) )-( ( ( f8 ) )-( ( bigX33 ) )-( ( bigX32 ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f5 ) )-( ( bigX16 ) ) )-( ( ( f5 ) )-( ( bigX17 ) ) ) ) \/ ( ~( ( ( p4 ) )-( ( bigX16 ) )-( ( bigX17 ) ) ) ) ) ) ) & ( ( ( ( p4 ) )-( ( ( f7 ) )-( ( bigX30 ) ) )-( ( ( f7 ) )-( ( bigX31 ) ) ) ) \/ ( ~( ( ( p4 ) )-( ( bigX30 ) )-( ( bigX31 ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( bigX10 ) )-( ( bigX11 ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX9 ) )-( ( bigX10 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX9 ) )-( ( bigX11 ) ) ) ) ) ) ) ) & ( ( ( ( p4 ) )-( ( bigX24 ) )-( ( bigX25 ) ) ) \/ ( ( ~( ( ( p4 ) )-( ( bigX23 ) )-( ( bigX24 ) ) ) ) \/ ( ~( ( ( p4 ) )-( ( bigX23 ) )-( ( bigX25 ) ) ) ) ) ) ) ) & ( ( ( p10 ) )-( ( ( f5 ) )-( ( bigX7 ) ) )-( ( ( f3 ) )-( ( ( f5 ) )-( ( ( f6 ) )-( ( bigX7 ) )-( ( bigX8 ) ) ) )-( ( ( f5 ) )-( ( bigX8 ) ) ) ) ) ) ) & ( ~( ( ( p10 ) )-( ( ( f9 ) )-( ( ( f5 ) )-( ( c11 ) ) )-( ( ( f5 ) )-( ( c12 ) ) ) )-( ( ( f5 ) )-( ( ( f8 ) )-( ( c11 ) )-( ( c12 ) ) ) ) ) ) ) ) & ( ( ( ( p10 ) )-( ( bigX4 ) )-( ( ( f3 ) )-( ( bigX5 ) )-( ( bigX6 ) ) ) ) \/ ( ~( ( ( p10 ) )-( ( ( f9 ) )-( ( bigX4 ) )-( ( bigX6 ) ) )-( ( bigX5 ) ) ) ) ) ) ) & ( ( ( ( p10 ) )-( ( ( f9 ) )-( ( bigX4 ) )-( ( bigX6 ) ) )-( ( bigX5 ) ) ) \/ ( ~( ( ( p10 ) )-( ( bigX4 ) )-( ( ( f3 ) )-( ( bigX5 ) )-( ( bigX6 ) ) ) ) ) ) ) ) & ( ( ( ( p10 ) )-( ( bigX0 ) )-( ( bigX1 ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX2 ) )-( ( bigX0 ) ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX3 ) )-( ( bigX1 ) ) ) ) \/ ( ~( ( ( p10 ) )-( ( bigX2 ) )-( ( bigX3 ) ) ) ) ) ) ) ) ) & ( ( ( ( p4 ) )-( ( ( f8 ) )-( ( bigX34 ) )-( ( bigX35 ) ) )-( ( ( f8 ) )-( ( bigX36 ) )-( ( bigX37 ) ) ) ) \/ ( ( ~( ( ( p4 ) )-( ( bigX34 ) )-( ( bigX36 ) ) ) ) \/ ( ~( ( ( p4 ) )-( ( bigX35 ) )-( ( bigX37 ) ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f3 ) )-( ( bigX12 ) )-( ( bigX13 ) ) )-( ( ( f3 ) )-( ( bigX14 ) )-( ( bigX15 ) ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX12 ) )-( ( bigX14 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX13 ) )-( ( bigX15 ) ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f9 ) )-( ( bigX19 ) )-( ( bigX20 ) ) )-( ( ( f9 ) )-( ( bigX21 ) )-( ( bigX22 ) ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX19 ) )-( ( bigX21 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX20 ) )-( ( bigX22 ) ) ) ) ) ) ) ) & ( ( ( ( p4 ) )-( ( ( f6 ) )-( ( bigX26 ) )-( ( bigX27 ) ) )-( ( ( f6 ) )-( ( bigX28 ) )-( ( bigX29 ) ) ) ) \/ ( ( ~( ( ( p4 ) )-( ( bigX26 ) )-( ( bigX28 ) ) ) ) \/ ( ~( ( ( p4 ) )-( ( bigX27 ) )-( ( bigX29 ) ) ) ) ) ) , no , '../../TPTP-v7.3.0/Problems/SYN/SYN564-1.p').
checkTheorem(syn , 767 , [ type:set ,bigX29 : (( type )) , bigX28 : (( type )) , bigX27 : (( type )) , bigX26 : (( type )) , bigX22 : (( type )) , bigX21 : (( type )) , bigX20 : (( type )) , bigX19 : (( type )) , bigX15 : (( type )) , bigX14 : (( type )) , bigX13 : (( type )) , bigX12 : (( type )) , bigX37 : (( type )) , bigX36 : (( type )) , bigX35 : (( type )) , bigX34 : (( type )) , bigX3 : (( type )) , bigX2 : (( type )) , bigX1 : (( type )) , bigX0 : (( type )) , bigX6 : (( type )) , bigX5 : (( type )) , bigX4 : (( type )) , f9 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , c12 : (( type )) , c11 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , p10 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , f3 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX8 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX7 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX25 : (( type )) , bigX24 : (( type )) , bigX11 : (( type )) , bigX10 : (( type )) , bigX31 : (( type )) , bigX30 : (( type )) , bigX17 : (( type )) , bigX16 : (( type )) , bigX33 : (( type )) , bigX32 : (( type )) , f6 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , f8 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX39 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX38 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , f5 : (( ( type ) ) -> ( ( prop ) )) , f7 : (( ( type ) ) -> ( ( prop ) )) , bigX18 : (( ( type ) ) -> ( ( prop ) )) , p4 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX23 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , p2 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigX9 : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) ] , ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ~( ( ( p2 ) )-( ( bigX9 ) )-( ( bigX9 ) ) ) ) ) & ( ( ( p4 ) )-( ( bigX23 ) )-( ( bigX23 ) ) ) ) ) & ( ( ( p2 ) )-( ( ( f5 ) )-( ( ( f7 ) )-( ( bigX18 ) ) ) )-( ( ( f5 ) )-( ( bigX18 ) ) ) ) ) ) & ( ( ( p4 ) )-( ( ( f8 ) )-( ( bigX38 ) )-( ( bigX39 ) ) )-( ( ( f6 ) )-( ( bigX38 ) )-( ( ( f7 ) )-( ( bigX39 ) ) ) ) ) ) ) & ( ( ( p4 ) )-( ( ( f7 ) )-( ( ( f8 ) )-( ( bigX32 ) )-( ( bigX33 ) ) ) )-( ( ( f8 ) )-( ( bigX33 ) )-( ( bigX32 ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f5 ) )-( ( bigX16 ) ) )-( ( ( f5 ) )-( ( bigX17 ) ) ) ) \/ ( ~( ( ( p4 ) )-( ( bigX16 ) )-( ( bigX17 ) ) ) ) ) ) ) & ( ( ( ( p4 ) )-( ( ( f7 ) )-( ( bigX30 ) ) )-( ( ( f7 ) )-( ( bigX31 ) ) ) ) \/ ( ~( ( ( p4 ) )-( ( bigX30 ) )-( ( bigX31 ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( bigX10 ) )-( ( bigX11 ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX9 ) )-( ( bigX10 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX9 ) )-( ( bigX11 ) ) ) ) ) ) ) ) & ( ( ( ( p4 ) )-( ( bigX24 ) )-( ( bigX25 ) ) ) \/ ( ( ~( ( ( p4 ) )-( ( bigX23 ) )-( ( bigX24 ) ) ) ) \/ ( ~( ( ( p4 ) )-( ( bigX23 ) )-( ( bigX25 ) ) ) ) ) ) ) ) & ( ( ( p10 ) )-( ( ( f5 ) )-( ( bigX7 ) ) )-( ( ( f3 ) )-( ( ( f5 ) )-( ( ( f6 ) )-( ( bigX7 ) )-( ( bigX8 ) ) ) )-( ( ( f5 ) )-( ( bigX8 ) ) ) ) ) ) ) & ( ~( ( ( p10 ) )-( ( ( f9 ) )-( ( ( f5 ) )-( ( c11 ) ) )-( ( ( f5 ) )-( ( c12 ) ) ) )-( ( ( f5 ) )-( ( ( f8 ) )-( ( c12 ) )-( ( c11 ) ) ) ) ) ) ) ) & ( ( ( ( p10 ) )-( ( bigX4 ) )-( ( ( f3 ) )-( ( bigX5 ) )-( ( bigX6 ) ) ) ) \/ ( ~( ( ( p10 ) )-( ( ( f9 ) )-( ( bigX4 ) )-( ( bigX6 ) ) )-( ( bigX5 ) ) ) ) ) ) ) & ( ( ( ( p10 ) )-( ( ( f9 ) )-( ( bigX4 ) )-( ( bigX6 ) ) )-( ( bigX5 ) ) ) \/ ( ~( ( ( p10 ) )-( ( bigX4 ) )-( ( ( f3 ) )-( ( bigX5 ) )-( ( bigX6 ) ) ) ) ) ) ) ) & ( ( ( ( p10 ) )-( ( bigX0 ) )-( ( bigX1 ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX2 ) )-( ( bigX0 ) ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX3 ) )-( ( bigX1 ) ) ) ) \/ ( ~( ( ( p10 ) )-( ( bigX2 ) )-( ( bigX3 ) ) ) ) ) ) ) ) ) & ( ( ( ( p4 ) )-( ( ( f8 ) )-( ( bigX34 ) )-( ( bigX35 ) ) )-( ( ( f8 ) )-( ( bigX36 ) )-( ( bigX37 ) ) ) ) \/ ( ( ~( ( ( p4 ) )-( ( bigX34 ) )-( ( bigX36 ) ) ) ) \/ ( ~( ( ( p4 ) )-( ( bigX35 ) )-( ( bigX37 ) ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f3 ) )-( ( bigX12 ) )-( ( bigX13 ) ) )-( ( ( f3 ) )-( ( bigX14 ) )-( ( bigX15 ) ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX12 ) )-( ( bigX14 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX13 ) )-( ( bigX15 ) ) ) ) ) ) ) ) & ( ( ( ( p2 ) )-( ( ( f9 ) )-( ( bigX19 ) )-( ( bigX20 ) ) )-( ( ( f9 ) )-( ( bigX21 ) )-( ( bigX22 ) ) ) ) \/ ( ( ~( ( ( p2 ) )-( ( bigX19 ) )-( ( bigX21 ) ) ) ) \/ ( ~( ( ( p2 ) )-( ( bigX20 ) )-( ( bigX22 ) ) ) ) ) ) ) ) & ( ( ( ( p4 ) )-( ( ( f6 ) )-( ( bigX26 ) )-( ( bigX27 ) ) )-( ( ( f6 ) )-( ( bigX28 ) )-( ( bigX29 ) ) ) ) \/ ( ( ~( ( ( p4 ) )-( ( bigX26 ) )-( ( bigX28 ) ) ) ) \/ ( ~( ( ( p4 ) )-( ( bigX27 ) )-( ( bigX29 ) ) ) ) ) ) , no , '../../TPTP-v7.3.0/Problems/SYN/SYN565-1.p').