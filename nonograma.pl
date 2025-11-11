% Ejercicio 1
matriz(0,_,[]).
matriz(Filas, Columnas, [Fila | Resto]) :-
	Filas > 0,
	length(Fila, Columnas),
	F1 is Filas-1,
	matriz(F1, Columnas, Resto).

% Ejercicio 2
replicar(_, 0, []).
replicar(Elemento, Cantidad, [Elemento | Resto]) :-
	Cantidad > 0,
	C1 is Cantidad-1,
	replicar(Elemento, C1, Resto).

% Ejercicio 3
obtener_columna_n([],_,[]).
obtener_columna_n([FilaActual | RestoMatriz], NumeroColumna, [Columna | RestoColumnas]) :-  
	nth1(NumeroColumna, FilaActual, Columna),
	obtener_columna_n(RestoMatriz, NumeroColumna, RestoColumnas).

primeras_n_columnas(_, 0, []).
primeras_n_columnas(Matriz, Cantidad, [Columna | RestoColumnas]) :- 
	C1 is Cantidad-1,
	obtener_columna_n(Matriz, Cantidad, Columna),
	primeras_n_columnas(Matriz, C1, RestoColumnas).

reverse([], []).
reverse([Elemento | Lista], Reversa) :-
	reverse(Lista, XS),
	append(XS, [Elemento], Reversa).

transponer([], []).
transponer([Fila | RestoMatriz], Transpuesta) :-
	length(Fila, CantColumnas),
	primeras_n_columnas([Fila | RestoMatriz], CantColumnas, Matriz),
	reverse(Matriz, Transpuesta).

% Predicado dado armarNono/3
armarNono(RF, RC, nono(M, RS)) :-
	length(RF, F),
	length(RC, C),
	matriz(F, C, M),
	transponer(M, Mt),
	zipR(RF, M, RSFilas),
	zipR(RC, Mt, RSColumnas),
	append(RSFilas, RSColumnas, RS).

zipR([], [], []).
zipR([R|RT], [L|LT], [r(R,L)|T]) :- zipR(RT, LT, T).

% Ejercicio 4
suma_reestricciones(r(Restriccion, _), Pintadas) :-
	sum_list(Restriccion, Pintadas).

cantidad_blancos(r(Restriccion, Celdas), Blancos) :-
	length(Celdas, Largo),
	suma_reestricciones(r(Restriccion, Celdas), Pintadas),
	Blancos is Largo - Pintadas.

pintadasValidas(r(Restriccion, Celdas)) :- 
	cantidad_blancos(r(Restriccion, Celdas), Blancos),
	between(0, Blancos, CantidadEspacios),
	pintadasValidas(r(Restriccion, Celda), CantidadEspacios, Blancos).

pintadasValidas(r([], Celdas), 0, 0) :-
	length(Celdas, Largo),
	replicar(o, Largo, Celdas).

pintadasValidas(r([0], []), 0, _).

pintadasValidas(r([Restriccion | RestoRestricciones], [Celda | RestoCeldas]), 0, Blancos) :-
	CantidadPintados is Restriccion-1,
	Celda = x,
	pintadasValidas(r([CantidadPintados | RestoRestricciones], RestoCeldas), 0, Blancos).

pintadasValidas(r([0 | Restricciones], Celdas), 0, Blancos) :-
	between(1, Blancos, CantidadEspacios),
	pintadasValidas(r(Restricciones, Celdas), CantidadEspacios, Blancos).

pintadasValidas(r(Restriccion, [Celda | RestoCeldas]), CantidadEspacios, Blancos) :- 
	Celda = o,
	N_Blancos is Blancos - 1,
	CantidadEspacios > 0,
	N_CantidadEspacios is CantidadEspacios-1,
	pintadasValidas(r(Restriccion, RestoCeldas), N_CantidadEspacios, N_Blancos).

% Ejercicio 5
resolverNaive(nono(_, Restricciones)) :-
	maplist(pintadasValidas, Restricciones).

% Ejercicio 6
pintarObligatorias(r(Restriccion, Celdas)) :- 
	armar_combinaciones(r(Restriccion, Celdas), Combinaciones),
	reducir_combinaciones(Combinaciones, Celdas).

armar_combinaciones(r(Restriccion, Celdas), X) :-
	bagof(Celdas, pintadasValidas(r(Restriccion, Celdas)), Matriz),
	transponer(Matriz, X).

reducir_combinaciones([Celda], [CeldaReducida]) :-
	reducir_celdas(Celda, CeldaReducida).
reducir_combinaciones([Celda | RestoCeldas], [CeldaReducida | RestoReducidas]) :-
	reducir_celdas(Celda, CeldaReducida),
	reducir_combinaciones(RestoCeldas, RestoReducidas).

reducir_celdas([Celda], Celda).
reducir_celdas([Celda | RestoCeldas], CeldaReducida) :-
	reducir_celdas(RestoCeldas, XS),
	combinarCelda(Celda, XS, CeldaReducida).

% Predicado dado combinarCelda/3
combinarCelda(A, B, _) :- var(A), var(B).
combinarCelda(A, B, _) :- nonvar(A), var(B).
combinarCelda(A, B, _) :- var(A), nonvar(B).
combinarCelda(A, B, A) :- nonvar(A), nonvar(B), A = B.
combinarCelda(A, B, _) :- nonvar(A), nonvar(B), A \== B.

% Ejercicio 7
deducir1Pasada(nono(_, Restricciones)) :-
	maplist(pintarObligatorias, Restricciones).

% Predicado dado
cantidadVariablesLibres(T, N) :- term_variables(T, LV), length(LV, N).

% Predicado dado
deducirVariasPasadas(NN) :-
	NN = nono(M,_),
	cantidadVariablesLibres(M, VI), % VI = cantidad de celdas sin instanciar en M en este punto
	deducir1Pasada(NN),
	cantidadVariablesLibres(M, VF), % VF = cantidad de celdas sin instanciar en M en este punto
	deducirVariasPasadasCont(NN, VI, VF).

% Predicado dado
deducirVariasPasadasCont(_, A, A). % Si VI = VF entonces no hubo más cambios y frenamos.
deducirVariasPasadasCont(NN, A, B) :- A =\= B, deducirVariasPasadas(NN).

% Ejercicio 8: R va a ser la restriccion con menor cantidad de variables no instanciadas si no hay ninguna otra restriccion con menos variables no instanciadas.
restriccionConMenosLibres(nono(_, Restricciones), R) :- 
	nth1(Indice1, Restricciones, R),
	R = r(_, Celdas),
	cantidadVariablesLibres(Celdas, VariablesLibres),
	VariablesLibres > 0,
	not( (
		nth1(Indice2, Restricciones, R2),
		Indice1 \= Indice2,
		R2 = r(_, Celdas2),
		cantidadVariablesLibres(Celdas2, VariablesLibres2),
		VariablesLibres2 > 0,
		VariablesLibres2 < VariablesLibres
	) ).

% Ejercicio 9
resolverDeduciendo(NN) :-
	deducirVariasPasadas(NN),
	not(restriccionConMenosLibres(NN, _)).
resolverDeduciendo(nono(Matriz, Restricciones)) :- 
	deducirVariasPasadas(nono(Matriz, Restricciones)),
	restriccionConMenosLibres(nono(Matriz, Restricciones), r(Restriccion, Celdas)),
	!,
	pintadasValidas(r(Restriccion, Celdas)),
	resolverDeduciendo(nono(Matriz, Restricciones)).

% Ejercicio 10
solucionUnica(NN) :- 
	bagof(NN, resolverDeduciendo(NN), Solucion),
	length(Solucion, 1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                              %
%    Ejemplos de nonogramas    %
%        NO MODIFICAR          %
%    pero se pueden agregar    %
%                              %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Fáciles
nn(0, NN) :- armarNono([[1],[2]],[[],[2],[1]], NN).
nn(1, NN) :- armarNono([[4],[2,1],[2,1],[1,1],[1]],[[4],[3],[1],[2],[3]], NN).
nn(2, NN) :- armarNono([[4],[3,1],[1,1],[1],[1,1]],[[4],[2],[2],[1],[3,1]], NN).
nn(3, NN) :- armarNono([[2,1],[4],[3,1],[3],[3,3],[2,1],[2,1],[4],[4,4],[4,2]], [[1,2,1],[1,1,2,2],[2,3],[1,3,3],[1,1,1,1],[2,1,1],[1,1,2],[2,1,1,2],[1,1,1],[1]], NN).
nn(4, NN) :- armarNono([[1, 1], [5], [5], [3], [1]], [[2], [4], [4], [4], [2]], NN).
nn(5, NN) :- armarNono([[], [1, 1], [], [1, 1], [3]], [[1], [1, 1], [1], [1, 1], [1]], NN).
nn(6, NN) :- armarNono([[5], [1], [1], [1], [5]], [[1, 1], [2, 2], [1, 1, 1], [1, 1], [1, 1]], NN).
nn(7, NN) :- armarNono([[1, 1], [4], [1, 3, 1], [5, 1], [3, 2], [4, 2], [5, 1], [6, 1], [2, 3, 2], [2, 6]], [[2, 1], [1, 2, 3], [9], [7, 1], [4, 5], [5], [4], [2, 1], [1, 2, 2], [4]], NN).
nn(8, NN) :- armarNono([[5], [1, 1], [1, 1, 1], [5], [7], [8, 1], [1, 8], [1, 7], [2, 5], [7]], [[4], [2, 2, 2], [1, 4, 1], [1, 5, 1], [1, 8], [1, 7], [1, 7], [2, 6], [3], [3]], NN).
nn(9, NN) :- armarNono([[4], [1, 3], [2, 2], [1, 1, 1], [3]], [[3], [1, 1, 1], [2, 2], [3, 1], [4]], NN).
nn(10, NN) :- armarNono([[1], [1], [1], [1, 1], [1, 1]], [[1, 1], [1, 1], [1], [1], [ 1]], NN).
nn(11, NN) :- armarNono([[1, 1, 1, 1], [3, 3], [1, 1], [1, 1, 1, 1], [8], [6], [10], [6], [2, 4, 2], [1, 1]], [[2, 1, 2], [4, 1, 1], [2, 4], [6], [5], [5], [6], [2, 4], [4, 1, 1], [2, 1, 2]], NN).
nn(12, NN) :- armarNono([[9], [1, 1, 1, 1], [10], [2, 1, 1], [1, 1, 1, 1], [1, 10], [1, 1, 1], [1, 1, 1], [1, 1, 1, 1, 1], [1, 9], [1, 2, 1, 1, 2], [2, 1, 1, 1, 1], [2, 1, 3, 1], [3, 1], [10]], [[], [9], [2, 2], [3, 1, 2], [1, 2, 1, 2], [3, 11], [1, 1, 1, 2, 1], [1, 1, 1, 1, 1, 1], [3, 1, 3, 1, 1], [1, 1, 1, 1, 1, 1], [1, 1, 1, 3, 1, 1], [3, 1, 1, 1, 1], [1, 1, 2, 1], [11], []], NN).
nn(13, NN) :- armarNono([[2], [1,1], [1,1], [1,1], [1], [], [2], [1,1], [1,1], [1,1], [1]], [[1], [1,3], [3,1,1], [1,1,3], [3]], NN).
nn(14, NN) :- armarNono([[1,1], [1,1], [1,1], [2]], [[2], [1,1], [1,1], [1,1]], NN).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                              %
%    Predicados auxiliares     %
%        NO MODIFICAR          %
%                              %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%! completar(+S)
%
% Indica que se debe completar el predicado. Siempre falla.
completar(S) :- write("COMPLETAR: "), write(S), nl, fail.

%! mostrarNono(+NN)
%
% Muestra una estructura nono(...) en pantalla
% Las celdas x (pintadas) se muestran como ██.
% Las o (no pintasdas) se muestran como ░░.
% Las no instanciadas se muestran como ¿?.
mostrarNono(nono(M,_)) :- mostrarMatriz(M).

%! mostrarMatriz(+M)
%
% Muestra una matriz. Solo funciona si las celdas
% son valores x, o, o no instanciados.
mostrarMatriz(M) :-
	M = [F|_], length(F, Cols),
	mostrarBorde('╔',Cols,'╗'),
	maplist(mostrarFila, M),
	mostrarBorde('╚',Cols,'╝').

mostrarBorde(I,N,F) :-
	write(I),
	stringRepeat('══', N, S),
	write(S),
	write(F),
	nl.

stringRepeat(_, 0, '').
stringRepeat(Str, N, R) :- N > 0, Nm1 is N - 1, stringRepeat(Str, Nm1, Rm1), string_concat(Str, Rm1, R).

%! mostrarFila(+M)
%
% Muestra una lista (fila o columna). Solo funciona si las celdas
% son valores x, o, o no instanciados.
mostrarFila(Fila) :-
	write('║'),
	maplist(mostrarCelda, Fila),
	write('║'),
	nl.

mostrarCelda(C) :- nonvar(C), C = x, write('██').
mostrarCelda(C) :- nonvar(C), C = o, write('░░').
mostrarCelda(C) :- var(C), write('¿?').

% Predicado para Ejercicio 11.
% Tamaño de una matriz.
% tam(-N, -T)
tam(N, (F, C)) :- nn(N, nono(M, _)), length(M, F), M = [X | _], length(X, C), matriz(F, C, M).