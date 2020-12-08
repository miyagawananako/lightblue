
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
checkTheorem(syn , 90 , [ type:set ,bigF : (( type )) , bigE : (( type )) , sk10 : (( type )) , sk9 : (( type )) , sk7 : (( type )) , sk8 : (( type )) , sk11 : (( type )) , a : (( type )) , sk3 : (( ( type ) ) -> ( ( prop ) )) , sk4 : (( ( type ) ) -> ( ( prop ) )) , bigA : (( type )) , big_p : (( ( type ) ) -> ( ( prop ) )) , bigC : (( type )) , sk5 : (( ( type ) ) -> ( ( prop ) )) , sk6 : (( ( type ) ) -> ( ( prop ) )) , bigD : (( ( type ) ) -> ( ( prop ) )) , big_r : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , sk1 : (( ( type ) ) -> ( ( prop ) )) , sk2 : (( ( type ) ) -> ( ( prop ) )) , bigB : (( ( type ) ) -> ( ( prop ) )) ] , ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ~( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigB ) ) )-( ( ( sk1 ) )-( ( bigB ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk6 ) )-( ( bigD ) ) )-( ( ( sk5 ) )-( ( bigD ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigD ) )-( ( bigC ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_r ) )-( ( bigB ) )-( ( ( sk2 ) )-( ( bigB ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk6 ) )-( ( bigD ) ) )-( ( ( sk5 ) )-( ( bigD ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigD ) )-( ( bigC ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_r ) )-( ( bigD ) )-( ( ( sk6 ) )-( ( bigD ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigB ) ) )-( ( ( sk1 ) )-( ( bigB ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigD ) )-( ( bigC ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_r ) )-( ( bigD ) )-( ( ( sk6 ) )-( ( bigD ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigB ) )-( ( ( sk2 ) )-( ( bigB ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigD ) )-( ( bigC ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigB ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk6 ) )-( ( bigD ) ) )-( ( ( sk5 ) )-( ( bigD ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigD ) )-( ( bigC ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigB ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigD ) )-( ( ( sk6 ) )-( ( bigD ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigD ) )-( ( bigC ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( ( sk5 ) )-( ( bigD ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigB ) ) )-( ( ( sk1 ) )-( ( bigB ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigD ) )-( ( bigC ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( ( sk5 ) )-( ( bigD ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigB ) )-( ( ( sk2 ) )-( ( bigB ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigD ) )-( ( bigC ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigB ) ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk5 ) )-( ( bigD ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigD ) )-( ( bigC ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigA ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigA ) ) )-( ( ( sk1 ) )-( ( bigA ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk6 ) )-( ( bigC ) ) )-( ( ( sk5 ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigB ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigC ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigA ) ) ) \/ ( ( ( ( big_r ) )-( ( bigC ) )-( ( ( sk6 ) )-( ( bigC ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigA ) ) )-( ( ( sk1 ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigB ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigC ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigA ) ) ) \/ ( ( ( ( big_r ) )-( ( bigA ) )-( ( ( sk2 ) )-( ( bigA ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk6 ) )-( ( bigC ) ) )-( ( ( sk5 ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigB ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigC ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigA ) ) ) \/ ( ( ( ( big_r ) )-( ( bigC ) )-( ( ( sk6 ) )-( ( bigC ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigA ) )-( ( ( sk2 ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigB ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigC ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigA ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk5 ) )-( ( bigC ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigA ) ) )-( ( ( sk1 ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigB ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigC ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigA ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk5 ) )-( ( bigC ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigA ) )-( ( ( sk2 ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigB ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigC ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigC ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigB ) ) )-( ( ( sk1 ) )-( ( bigB ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk4 ) )-( ( bigC ) ) )-( ( ( sk3 ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigC ) ) ) \/ ( ( ( ( big_r ) )-( ( bigB ) )-( ( ( sk2 ) )-( ( bigB ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk4 ) )-( ( bigC ) ) )-( ( ( sk3 ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigC ) ) ) \/ ( ( ( ( big_r ) )-( ( bigC ) )-( ( ( sk4 ) )-( ( bigC ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigB ) ) )-( ( ( sk1 ) )-( ( bigB ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigC ) ) ) \/ ( ( ( ( big_r ) )-( ( bigC ) )-( ( ( sk4 ) )-( ( bigC ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigB ) )-( ( ( sk2 ) )-( ( bigB ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigC ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigB ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk4 ) )-( ( bigC ) ) )-( ( ( sk3 ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigC ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigB ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigC ) )-( ( ( sk4 ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigC ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk3 ) )-( ( bigC ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigB ) ) )-( ( ( sk1 ) )-( ( bigB ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigC ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk3 ) )-( ( bigC ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigB ) )-( ( ( sk2 ) )-( ( bigB ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigC ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigB ) ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk3 ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigB ) ) ) \/ ( ( ( ( big_p ) )-( ( bigA ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigA ) ) )-( ( ( sk1 ) )-( ( bigA ) ) ) ) \/ ( ( ( big_r ) )-( ( ( sk4 ) )-( ( bigB ) ) )-( ( ( sk3 ) )-( ( bigB ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigB ) ) ) \/ ( ( ( ( big_p ) )-( ( bigA ) ) ) \/ ( ( ( ( big_r ) )-( ( bigB ) )-( ( ( sk4 ) )-( ( bigB ) ) ) ) \/ ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigA ) ) )-( ( ( sk1 ) )-( ( bigA ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigB ) ) ) \/ ( ( ( ( big_p ) )-( ( bigA ) ) ) \/ ( ( ( ( big_r ) )-( ( bigA ) )-( ( ( sk2 ) )-( ( bigA ) ) ) ) \/ ( ( ( big_r ) )-( ( ( sk4 ) )-( ( bigB ) ) )-( ( ( sk3 ) )-( ( bigB ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigB ) ) ) \/ ( ( ( ( big_p ) )-( ( bigA ) ) ) \/ ( ( ( ( big_r ) )-( ( bigB ) )-( ( ( sk4 ) )-( ( bigB ) ) ) ) \/ ( ( ( big_r ) )-( ( bigA ) )-( ( ( sk2 ) )-( ( bigA ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigB ) ) ) \/ ( ( ( ( big_p ) )-( ( bigA ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk3 ) )-( ( bigB ) ) ) ) \/ ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigA ) ) )-( ( ( sk1 ) )-( ( bigA ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigB ) ) ) \/ ( ( ( ( big_p ) )-( ( bigA ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk3 ) )-( ( bigB ) ) ) ) \/ ( ( ( big_r ) )-( ( bigA ) )-( ( ( sk2 ) )-( ( bigA ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigA ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigA ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk6 ) )-( ( bigC ) ) )-( ( ( sk5 ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigB ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigC ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigA ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigA ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigC ) )-( ( ( sk6 ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigB ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigC ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigA ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigA ) ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk5 ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigB ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigC ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigB ) ) ) \/ ( ( ( ( big_p ) )-( ( bigA ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigA ) ) ) ) \/ ( ( ( big_r ) )-( ( ( sk4 ) )-( ( bigB ) ) )-( ( ( sk3 ) )-( ( bigB ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigB ) ) ) \/ ( ( ( ( big_p ) )-( ( bigA ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigA ) ) ) ) \/ ( ( ( big_r ) )-( ( bigB ) )-( ( ( sk4 ) )-( ( bigB ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigB ) ) ) \/ ( ( ( ( big_p ) )-( ( bigA ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigA ) ) ) ) \/ ( ( ( big_p ) )-( ( ( sk3 ) )-( ( bigB ) ) ) ) ) ) ) ) ) & ( ( ( big_p ) )-( ( a ) ) ) ) ) & ( ( ( ( big_p ) )-( ( sk11 ) ) ) \/ ( ( ( ( big_p ) )-( ( sk8 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk7 ) ) ) ) \/ ( ~( ( ( big_p ) )-( ( sk9 ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( sk8 ) ) ) \/ ( ( ( ( big_r ) )-( ( sk10 ) )-( ( sk11 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk7 ) ) ) ) \/ ( ~( ( ( big_p ) )-( ( sk9 ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( sk8 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk7 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk9 ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( sk10 ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( sk11 ) ) ) \/ ( ( ( ( big_p ) )-( ( sk8 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk7 ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( sk9 ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( sk8 ) ) ) \/ ( ( ( ( big_r ) )-( ( sk10 ) )-( ( sk11 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk7 ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( sk9 ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( sk8 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk7 ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigD ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( sk10 ) )-( ( bigD ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( sk9 ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( sk11 ) ) ) \/ ( ( ( ( big_r ) )-( ( sk7 ) )-( ( sk8 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk7 ) ) ) ) \/ ( ~( ( ( big_p ) )-( ( sk9 ) ) ) ) ) ) ) ) ) & ( ( ( ( big_r ) )-( ( sk10 ) )-( ( sk11 ) ) ) \/ ( ( ( ( big_r ) )-( ( sk7 ) )-( ( sk8 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk7 ) ) ) ) \/ ( ~( ( ( big_p ) )-( ( sk9 ) ) ) ) ) ) ) ) ) & ( ( ( ( big_r ) )-( ( sk7 ) )-( ( sk8 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk7 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk9 ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( sk10 ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( sk11 ) ) ) \/ ( ( ( ( big_r ) )-( ( sk7 ) )-( ( sk8 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk7 ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( sk9 ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_r ) )-( ( sk10 ) )-( ( sk11 ) ) ) \/ ( ( ( ( big_r ) )-( ( sk7 ) )-( ( sk8 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk7 ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( sk9 ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_r ) )-( ( sk7 ) )-( ( sk8 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk7 ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigD ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( sk10 ) )-( ( bigD ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( sk9 ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( sk11 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk9 ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( sk7 ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_r ) )-( ( sk10 ) )-( ( sk11 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk9 ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( sk7 ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) & ( ( ~( ( ( big_p ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk9 ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigD ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( sk10 ) )-( ( bigD ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( sk7 ) )-( ( bigB ) ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( sk11 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigD ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( sk7 ) )-( ( bigB ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( sk9 ) )-( ( bigD ) ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_r ) )-( ( sk10 ) )-( ( sk11 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigD ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( sk7 ) )-( ( bigB ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( sk9 ) )-( ( bigD ) ) ) ) ) ) ) ) ) ) ) ) & ( ( ~( ( ( big_p ) )-( ( bigE ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigF ) )-( ( bigE ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigD ) )-( ( bigC ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigB ) )-( ( bigA ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( sk10 ) )-( ( bigF ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( sk7 ) )-( ( bigB ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( sk9 ) )-( ( bigD ) ) ) ) ) ) ) ) ) ) ) ) , no , '../../TPTP-v7.3.0/Problems/SYN/SYN067-2.p').
checkTheorem(syn , 91 , [ type:set ,bigP4 : (( type )) , bigO4 : (( type )) , bigN4 : (( type )) , bigM4 : (( type )) , bigL4 : (( type )) , bigK4 : (( type )) , bigJ4 : (( type )) , bigI4 : (( type )) , bigH4 : (( type )) , bigG4 : (( type )) , bigF4 : (( type )) , bigE4 : (( type )) , sk9 : (( type )) , sk7 : (( type )) , sk8 : (( type )) , sk10 : (( type )) , bigD4 : (( type )) , bigC4 : (( type )) , bigB4 : (( type )) , bigA4 : (( type )) , bigZ3 : (( type )) , bigY3 : (( type )) , bigX3 : (( type )) , bigW3 : (( type )) , bigV3 : (( type )) , bigU3 : (( type )) , bigT3 : (( type )) , bigS3 : (( type )) , bigR3 : (( type )) , bigQ3 : (( type )) , bigP3 : (( type )) , bigO3 : (( type )) , bigN3 : (( type )) , bigM3 : (( type )) , bigL3 : (( type )) , bigK3 : (( type )) , bigJ3 : (( type )) , bigI3 : (( type )) , bigH3 : (( type )) , bigG3 : (( type )) , bigF3 : (( type )) , bigE3 : (( type )) , bigD3 : (( type )) , bigC3 : (( type )) , bigB3 : (( type )) , bigA3 : (( type )) , bigZ2 : (( type )) , bigY2 : (( type )) , bigX2 : (( type )) , bigW2 : (( type )) , bigV2 : (( type )) , bigU2 : (( type )) , bigT2 : (( type )) , bigS2 : (( type )) , bigR2 : (( type )) , bigQ2 : (( type )) , bigP2 : (( type )) , bigO2 : (( type )) , bigN2 : (( type )) , bigM2 : (( type )) , bigL2 : (( type )) , bigK2 : (( type )) , bigJ2 : (( type )) , bigI2 : (( type )) , bigH2 : (( type )) , bigG2 : (( type )) , bigF2 : (( type )) , bigE2 : (( type )) , bigD2 : (( type )) , bigC2 : (( type )) , bigB2 : (( type )) , bigA2 : (( type )) , bigZ1 : (( type )) , bigY1 : (( type )) , bigX1 : (( type )) , bigW1 : (( type )) , bigV1 : (( type )) , bigU1 : (( type )) , bigT1 : (( type )) , bigS1 : (( type )) , bigR1 : (( type )) , bigQ1 : (( type )) , bigP1 : (( type )) , bigO1 : (( type )) , bigN1 : (( type )) , bigM1 : (( type )) , bigL1 : (( type )) , bigK1 : (( type )) , bigJ1 : (( type )) , bigI1 : (( type )) , bigH1 : (( type )) , bigG1 : (( type )) , bigF1 : (( type )) , bigE1 : (( type )) , bigD1 : (( type )) , bigC1 : (( type )) , bigB1 : (( type )) , bigA1 : (( type )) , bigZ : (( type )) , bigY : (( type )) , bigX : (( type )) , bigW : (( type )) , bigV : (( type )) , bigU : (( type )) , bigT : (( type )) , bigS : (( type )) , bigR : (( type )) , sk6 : (( ( type ) ) -> ( ( prop ) )) , bigQ : (( type )) , bigP : (( ( type ) ) -> ( ( prop ) )) , bigO : (( type )) , sk5 : (( ( type ) ) -> ( ( prop ) )) , bigN : (( type )) , bigM : (( ( type ) ) -> ( ( prop ) )) , bigL : (( type )) , bigK : (( type )) , bigJ : (( type )) , bigI : (( type )) , sk2 : (( ( type ) ) -> ( ( prop ) )) , bigH : (( type )) , bigG : (( ( type ) ) -> ( ( prop ) )) , bigF : (( type )) , bigE : (( type )) , big_r : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , sk4 : (( ( type ) ) -> ( ( prop ) )) , bigD : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigC : (( ( type ) ) -> ( ( prop ) )) , a : (( type )) , sk3 : (( ( type ) ) -> ( ( prop ) )) , sk1 : (( ( type ) ) -> ( ( prop ) )) , bigB : (( ( type ) ) -> ( ( prop ) )) , big_p : (( ( type ) ) -> ( ( prop ) )) , bigA : (( ( type ) ) -> ( ( prop ) )) ] , ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ( ~( ~( ( ( ( big_p ) )-( ( bigA ) ) ) \/ ( ( ( ( big_p ) )-( ( bigB ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigB ) ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk3 ) )-( ( bigA ) ) ) ) \/ ( ~( ( ( big_p ) )-( ( a ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigC ) ) ) \/ ( ( ( ( big_p ) )-( ( bigD ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigD ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigC ) )-( ( ( sk4 ) )-( ( bigC ) ) ) ) \/ ( ~( ( ( big_p ) )-( ( a ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigE ) ) ) \/ ( ( ( ( big_p ) )-( ( bigF ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigF ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk4 ) )-( ( bigE ) ) )-( ( ( sk3 ) )-( ( bigE ) ) ) ) \/ ( ~( ( ( big_p ) )-( ( a ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigG ) ) ) \/ ( ( ( ( big_p ) )-( ( bigH ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk3 ) )-( ( bigG ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigH ) )-( ( ( sk2 ) )-( ( bigH ) ) ) ) \/ ( ~( ( ( big_p ) )-( ( a ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigI ) ) ) \/ ( ( ( ( big_p ) )-( ( bigJ ) ) ) \/ ( ( ( ( big_r ) )-( ( bigI ) )-( ( ( sk4 ) )-( ( bigI ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigJ ) )-( ( ( sk2 ) )-( ( bigJ ) ) ) ) \/ ( ~( ( ( big_p ) )-( ( a ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigK ) ) ) \/ ( ( ( ( big_p ) )-( ( bigL ) ) ) \/ ( ( ( ( big_r ) )-( ( bigL ) )-( ( ( sk2 ) )-( ( bigL ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk4 ) )-( ( bigK ) ) )-( ( ( sk3 ) )-( ( bigK ) ) ) ) \/ ( ~( ( ( big_p ) )-( ( a ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigM ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigM ) ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk5 ) )-( ( bigN ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigO ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigN ) )-( ( bigO ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigP ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigP ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigQ ) )-( ( ( sk6 ) )-( ( bigQ ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigR ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigQ ) )-( ( bigR ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigS ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigS ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk6 ) )-( ( bigT ) ) )-( ( ( sk5 ) )-( ( bigT ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigU ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigT ) )-( ( bigU ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigV ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk5 ) )-( ( bigW ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigV ) )-( ( ( sk2 ) )-( ( bigV ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigX ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigW ) )-( ( bigX ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigY ) ) ) \/ ( ( ( ( big_r ) )-( ( bigZ ) )-( ( ( sk6 ) )-( ( bigZ ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigY ) )-( ( ( sk2 ) )-( ( bigY ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA1 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigZ ) )-( ( bigA1 ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigB1 ) ) ) \/ ( ( ( ( big_r ) )-( ( bigB1 ) )-( ( ( sk2 ) )-( ( bigB1 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk6 ) )-( ( bigC1 ) ) )-( ( ( sk5 ) )-( ( bigC1 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigD1 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigC1 ) )-( ( bigD1 ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigE1 ) ) ) \/ ( ( ( ( big_p ) )-( ( bigF1 ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk3 ) )-( ( bigE1 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigF1 ) ) )-( ( ( sk1 ) )-( ( bigF1 ) ) ) ) \/ ( ~( ( ( big_p ) )-( ( a ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigG1 ) ) ) \/ ( ( ( ( big_p ) )-( ( bigH1 ) ) ) \/ ( ( ( ( big_r ) )-( ( bigG1 ) )-( ( ( sk4 ) )-( ( bigG1 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigH1 ) ) )-( ( ( sk1 ) )-( ( bigH1 ) ) ) ) \/ ( ~( ( ( big_p ) )-( ( a ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigI1 ) ) ) \/ ( ( ( ( big_p ) )-( ( bigJ1 ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigJ1 ) ) )-( ( ( sk1 ) )-( ( bigJ1 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk4 ) )-( ( bigI1 ) ) )-( ( ( sk3 ) )-( ( bigI1 ) ) ) ) \/ ( ~( ( ( big_p ) )-( ( a ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigK1 ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigL1 ) ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk3 ) )-( ( bigK1 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigM1 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigL1 ) )-( ( bigM1 ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigN1 ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk3 ) )-( ( bigN1 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigO1 ) )-( ( ( sk2 ) )-( ( bigO1 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigP1 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigO1 ) )-( ( bigP1 ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigQ1 ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigR1 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigQ1 ) )-( ( ( sk4 ) )-( ( bigQ1 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigS1 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigR1 ) )-( ( bigS1 ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigT1 ) ) ) \/ ( ( ( ( big_r ) )-( ( bigT1 ) )-( ( ( sk4 ) )-( ( bigT1 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigU1 ) )-( ( ( sk2 ) )-( ( bigU1 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigV1 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigU1 ) )-( ( bigV1 ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigW1 ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk3 ) )-( ( bigW1 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigX1 ) ) )-( ( ( sk1 ) )-( ( bigX1 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigY1 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigX1 ) )-( ( bigY1 ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigZ1 ) ) ) \/ ( ( ( ( big_r ) )-( ( bigZ1 ) )-( ( ( sk4 ) )-( ( bigZ1 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigA2 ) ) )-( ( ( sk1 ) )-( ( bigA2 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigB2 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigA2 ) )-( ( bigB2 ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigC2 ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigD2 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk4 ) )-( ( bigC2 ) ) )-( ( ( sk3 ) )-( ( bigC2 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigE2 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigD2 ) )-( ( bigE2 ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigF2 ) ) ) \/ ( ( ( ( big_r ) )-( ( bigG2 ) )-( ( ( sk2 ) )-( ( bigG2 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk4 ) )-( ( bigF2 ) ) )-( ( ( sk3 ) )-( ( bigF2 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigH2 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigG2 ) )-( ( bigH2 ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigI2 ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigJ2 ) ) )-( ( ( sk1 ) )-( ( bigJ2 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk4 ) )-( ( bigI2 ) ) )-( ( ( sk3 ) )-( ( bigI2 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigK2 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigJ2 ) )-( ( bigK2 ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigL2 ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk5 ) )-( ( bigM2 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigL2 ) ) )-( ( ( sk1 ) )-( ( bigL2 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigN2 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigM2 ) )-( ( bigN2 ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigO2 ) ) ) \/ ( ( ( ( big_r ) )-( ( bigP2 ) )-( ( ( sk6 ) )-( ( bigP2 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigO2 ) ) )-( ( ( sk1 ) )-( ( bigO2 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigQ2 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigP2 ) )-( ( bigQ2 ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( bigR2 ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigR2 ) ) )-( ( ( sk1 ) )-( ( bigR2 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk6 ) )-( ( bigS2 ) ) )-( ( ( sk5 ) )-( ( bigS2 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigT2 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigS2 ) )-( ( bigT2 ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigU2 ) ) ) ) \/ ( ( ( ( big_p ) )-( ( ( sk5 ) )-( ( bigV2 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigW2 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigX2 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigV2 ) )-( ( bigW2 ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigU2 ) )-( ( bigX2 ) ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( ( sk5 ) )-( ( bigY2 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigZ2 ) )-( ( ( sk2 ) )-( ( bigZ2 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigA3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigB3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigY2 ) )-( ( bigA3 ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigZ2 ) )-( ( bigB3 ) ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigC3 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigD3 ) )-( ( ( sk6 ) )-( ( bigD3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigE3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigF3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigD3 ) )-( ( bigE3 ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigC3 ) )-( ( bigF3 ) ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_r ) )-( ( bigG3 ) )-( ( ( sk6 ) )-( ( bigG3 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( bigH3 ) )-( ( ( sk2 ) )-( ( bigH3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigI3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigJ3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigG3 ) )-( ( bigI3 ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigH3 ) )-( ( bigJ3 ) ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( ( sk5 ) )-( ( bigK3 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigL3 ) ) )-( ( ( sk1 ) )-( ( bigL3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigM3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigN3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigK3 ) )-( ( bigM3 ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigL3 ) )-( ( bigN3 ) ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_r ) )-( ( bigO3 ) )-( ( ( sk6 ) )-( ( bigO3 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigP3 ) ) )-( ( ( sk1 ) )-( ( bigP3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigQ3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigR3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigO3 ) )-( ( bigQ3 ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigP3 ) )-( ( bigR3 ) ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( ( sk1 ) )-( ( bigS3 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk6 ) )-( ( bigT3 ) ) )-( ( ( sk5 ) )-( ( bigT3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigU3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigV3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigT3 ) )-( ( bigU3 ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigS3 ) )-( ( bigV3 ) ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_r ) )-( ( bigW3 ) )-( ( ( sk2 ) )-( ( bigW3 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk6 ) )-( ( bigX3 ) ) )-( ( ( sk5 ) )-( ( bigX3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigY3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigZ3 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigX3 ) )-( ( bigY3 ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigW3 ) )-( ( bigZ3 ) ) ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_r ) )-( ( ( sk2 ) )-( ( bigA4 ) ) )-( ( ( sk1 ) )-( ( bigA4 ) ) ) ) \/ ( ( ( ( big_r ) )-( ( ( sk6 ) )-( ( bigB4 ) ) )-( ( ( sk5 ) )-( ( bigB4 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigC4 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigD4 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( a ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigB4 ) )-( ( bigC4 ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( bigA4 ) )-( ( bigD4 ) ) ) ) ) ) ) ) ) ) ) ) & ( ( ( big_p ) )-( ( a ) ) ) ) ) & ( ( ( ( big_p ) )-( ( sk10 ) ) ) \/ ( ( ( ( big_p ) )-( ( sk8 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk7 ) ) ) ) \/ ( ~( ( ( big_p ) )-( ( sk9 ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( sk8 ) ) ) \/ ( ( ( ( big_r ) )-( ( sk9 ) )-( ( sk10 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk7 ) ) ) ) \/ ( ~( ( ( big_p ) )-( ( sk9 ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( sk10 ) ) ) \/ ( ( ( ( big_r ) )-( ( sk7 ) )-( ( sk8 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk7 ) ) ) ) \/ ( ~( ( ( big_p ) )-( ( sk9 ) ) ) ) ) ) ) ) ) & ( ( ( ( big_r ) )-( ( sk7 ) )-( ( sk8 ) ) ) \/ ( ( ( ( big_r ) )-( ( sk9 ) )-( ( sk10 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk7 ) ) ) ) \/ ( ~( ( ( big_p ) )-( ( sk9 ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( sk8 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigE4 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk7 ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigF4 ) )-( ( bigE4 ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( sk9 ) )-( ( bigF4 ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_r ) )-( ( sk7 ) )-( ( sk8 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigG4 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk7 ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigH4 ) )-( ( bigG4 ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( sk9 ) )-( ( bigH4 ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_p ) )-( ( sk10 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigI4 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk9 ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigJ4 ) )-( ( bigI4 ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( sk7 ) )-( ( bigJ4 ) ) ) ) ) ) ) ) ) ) & ( ( ( ( big_r ) )-( ( sk9 ) )-( ( sk10 ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigK4 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( sk9 ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigL4 ) )-( ( bigK4 ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( sk7 ) )-( ( bigL4 ) ) ) ) ) ) ) ) ) ) & ( ( ~( ( ( big_p ) )-( ( bigM4 ) ) ) ) \/ ( ( ~( ( ( big_p ) )-( ( bigN4 ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigO4 ) )-( ( bigM4 ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( bigP4 ) )-( ( bigN4 ) ) ) ) \/ ( ( ~( ( ( big_r ) )-( ( sk7 ) )-( ( bigP4 ) ) ) ) \/ ( ~( ( ( big_r ) )-( ( sk9 ) )-( ( bigO4 ) ) ) ) ) ) ) ) ) , no , '../../TPTP-v7.3.0/Problems/SYN/SYN067-3.p').
checkTheorem(syn , 92 , [ type:set ,big_j : (( ( type ) ) -> ( ( prop ) )) , a : (( type )) , g : (( type )) , big_h : (( type )) , big_g : (( type )) , f : (( type )) , big_f : (( ( type ) ) -> ( ( prop ) )) , bigX : (( type )) , axiom5 : (( ~( ( ( big_f ) )-( ( bigX ) ) ) ) \/ ( ( ( big_g ) )-( ( ( f ) )-( ( bigX ) ) ) )) , axiom4 : (( ~( ( ( big_f ) )-( ( bigX ) ) ) ) \/ ( ( ( big_h ) )-( ( bigX ) )-( ( ( f ) )-( ( bigX ) ) ) )) , axiom3 : (( ~( ( ( big_f ) )-( ( bigX ) ) ) ) \/ ( ( ( big_g ) )-( ( ( g ) )-( ( bigX ) ) ) )) , axiom2 : (( ~( ( ( big_f ) )-( ( bigX ) ) ) ) \/ ( ~( ( ( big_h ) )-( ( bigX ) )-( ( ( g ) )-( ( bigX ) ) ) ) )) , axiom1 : (( ( big_j ) )-( ( a ) )) , axiom0 : (( ~( ( ( big_g ) )-( ( bigX ) ) ) ) \/ ( ( ( big_h ) )-( ( a ) )-( ( bigX ) ) )) ] , ~( ( ~( ( ( big_j ) )-( ( bigX ) ) ) ) \/ ( ( ( big_f ) )-( ( bigX ) ) ) ) , no , '../../TPTP-v7.3.0/Problems/SYN/SYN068-1.p').
checkTheorem(syn , 93 , [ type:set ,big_j : (( ( type ) ) -> ( ( prop ) )) , big_h : (( type )) , big_g : (( type )) , big_f : (( ( type ) ) -> ( ( prop ) )) , axiom1 : (pi(X:type,( ( ( big_f ) )-( ( bigX ) ) ) -> ( ( sigma(Y:type,( ( ( big_g ) )-( ( bigY ) ) ) & ( ( ( big_h ) )-( ( bigX ) )-( ( bigY ) ) )) ) & ( sigma(Y1:type,( ( ( big_g ) )-( ( bigY1 ) ) ) & ( ~( ( ( big_h ) )-( ( bigX ) )-( ( bigY1 ) ) ) )) ) ))) , axiom0 : (sigma(X:type,( ( ( big_j ) )-( ( bigX ) ) ) & ( pi(Y:type,( ( ( big_g ) )-( ( bigY ) ) ) -> ( ( ( big_h ) )-( ( bigX ) )-( ( bigY ) ) )) ))) ] , sigma(X:type,( ( ( big_j ) )-( ( bigX ) ) ) & ( ~( ( ( big_f ) )-( ( bigX ) ) ) )) , yes , '../../TPTP-v7.3.0/Problems/SYN/SYN068+1.p').
checkTheorem(syn , 94 , [ type:set ,g : (( ( type ) ) -> ( ( prop ) )) , a : (( type )) , big_l : (( type )) , big_j : (( type )) , big_k : (( type )) , big_h : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , bigY : (( type )) , big_g : (( ( type ) ) -> ( ( prop ) )) , f : (( type )) , big_f : (( ( type ) ) -> ( ( prop ) )) , bigX : (( type )) , axiom6 : (( ~( ( ( big_f ) )-( ( bigX ) ) ) ) \/ ( ( ( ( big_g ) )-( ( ( f ) )-( ( bigX ) ) ) ) \/ ( ( ~( ( ( big_g ) )-( ( bigY ) ) ) ) \/ ( ( ~( ( ( big_h ) )-( ( bigX ) )-( ( bigY ) ) ) ) \/ ( ( ( big_k ) )-( ( bigY ) ) ) ) ) )) , axiom5 : (( ~( ( ( big_f ) )-( ( bigX ) ) ) ) \/ ( ( ( ( big_h ) )-( ( bigX ) )-( ( ( f ) )-( ( bigX ) ) ) ) \/ ( ( ~( ( ( big_g ) )-( ( bigY ) ) ) ) \/ ( ( ~( ( ( big_h ) )-( ( bigX ) )-( ( bigY ) ) ) ) \/ ( ( ( big_k ) )-( ( bigY ) ) ) ) ) )) , axiom4 : (( ~( ( ( big_f ) )-( ( bigX ) ) ) ) \/ ( ( ~( ( ( big_j ) )-( ( bigX ) )-( ( ( f ) )-( ( bigX ) ) ) ) ) \/ ( ( ~( ( ( big_g ) )-( ( bigY ) ) ) ) \/ ( ( ~( ( ( big_h ) )-( ( bigX ) )-( ( bigY ) ) ) ) \/ ( ( ( big_k ) )-( ( bigY ) ) ) ) ) )) , axiom3 : (( ~( ( ( big_l ) )-( ( bigX ) ) ) ) \/ ( ~( ( ( big_k ) )-( ( bigX ) ) ) )) , axiom2 : (( ( big_f ) )-( ( a ) )) , axiom1 : (( ~( ( ( big_h ) )-( ( a ) )-( ( bigX ) ) ) ) \/ ( ( ( big_l ) )-( ( bigX ) ) )) , axiom0 : (( ~( ( ( big_g ) )-( ( bigX ) ) ) ) \/ ( ( ~( ( ( big_h ) )-( ( a ) )-( ( bigX ) ) ) ) \/ ( ( ( big_j ) )-( ( a ) )-( ( bigX ) ) ) )) ] , ( ~( ~( ( ~( ( ( big_f ) )-( ( bigX ) ) ) ) \/ ( ( ( big_g ) )-( ( ( g ) )-( ( bigX ) ) ) ) ) ) ) & ( ( ~( ( ( big_f ) )-( ( bigX ) ) ) ) \/ ( ( ( big_h ) )-( ( bigX ) )-( ( ( g ) )-( ( bigX ) ) ) ) ) , no , '../../TPTP-v7.3.0/Problems/SYN/SYN069-1.p').
checkTheorem(syn , 95 , [ type:set ,big_l : (( type )) , big_k : (( type )) , big_j : (( type )) , big_h : (( ( type ) ) -> ( ( ( type ) ) -> ( ( prop ) ) )) , big_g : (( ( type ) ) -> ( ( prop ) )) , big_f : (( ( type ) ) -> ( ( prop ) )) , axiom2 : (pi(X:type,( ( ( ( big_f ) )-( ( bigX ) ) ) & ( pi(Y:type,( ( ( ( big_g ) )-( ( bigY ) ) ) & ( ( ( big_h ) )-( ( bigX ) )-( ( bigY ) ) ) ) -> ( ( ( big_j ) )-( ( bigX ) )-( ( bigY ) ) )) ) ) -> ( pi(Y1:type,( ( ( big_g ) )-( ( bigY1 ) ) ) & ( ( ( ( big_h ) )-( ( bigX ) )-( ( bigY1 ) ) ) & ( ( ( big_k ) )-( ( bigY1 ) ) ) )) ))) , axiom1 : (~( sigma(Y:type,( ( ( big_l ) )-( ( bigY ) ) ) & ( ( ( big_k ) )-( ( bigY ) ) )) )) , axiom0 : (sigma(X:type,( ( ( big_f ) )-( ( bigX ) ) ) & ( ( pi(Y:type,( ( ( big_h ) )-( ( bigX ) )-( ( bigY ) ) ) -> ( ( ( big_l ) )-( ( bigY ) ) )) ) & ( pi(Y1:type,( ( ( ( big_g ) )-( ( bigY1 ) ) ) & ( ( ( big_h ) )-( ( bigX ) )-( ( bigY1 ) ) ) ) -> ( ( ( big_j ) )-( ( bigX ) )-( ( bigY1 ) ) )) ) ))) ] , sigma(X:type,( ( ( big_f ) )-( ( bigX ) ) ) & ( ~( sigma(Y:type,( ( ( big_g ) )-( ( bigY ) ) ) & ( ( ( big_h ) )-( ( bigX ) )-( ( bigY ) ) )) ) )) , yes , '../../TPTP-v7.3.0/Problems/SYN/SYN069+1.p').