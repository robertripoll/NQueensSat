:- use_module(library(lists)). % Necessari per al l'ús del predicat "delete"

%%%%%%%%%%%%
% sat(F,I,M)
% si F es satisfactible, M sera el model de F afegit a la interpretació I (a la primera crida I sera buida).
% Assumim invariant que no hi ha literals repetits a les clausules ni la clausula buida inicialment.

sat([],I,I):-     write('SAT!!'),nl,!.
sat(CNF,I,M):-
% Ha de triar un literal d’una clausula unitaria, si no n’hi ha cap, llavors un literal pendent qualsevol.
decideix(CNF,Lit),

% Simplifica la CNF amb el Lit triat (compte pq pot fallar, es a dir si troba la clausula buida fallara i fara backtraking).
simplif(Lit,CNF,CNFS),

% crida recursiva amb la CNF i la interpretacio actualitzada
sat(CNFS, [Lit|I], M).


%%%%%%%%%%%%%%%%%%
% decideix(F, Lit)
% Donat una CNF,
% -> el segon parametre sera un literal de CNF
%  - si hi ha una clausula unitaria sera aquest literal, sino
%  - un qualsevol o el seu negat.
% ...

% Hem trobat una clàusula unitària, l'agafem i deixem de buscar
decideix([[X]|F], X) :- !.
% Hem trobat una clàusula NO unitària però queden més clàusules, continuem cercant
decideix([[_|_]|F], X) :- decideix(F, X).
% Hem arribat a l'última clàusula de la llista (no n'hi ha més), agafem el seu primer literal
decideix([[X|_]], X).
decideix([[X|_]], Y) :- Y is X*(-1).

%%%%%%%%%%%%%%%%%%%%%
% simplif(Lit, F, FS)
% Donat un literal Lit i una CNF,
% -> el tercer parametre sera la CNF que ens han donat simplificada:
%  - sense les clausules que tenen lit
%  - treient -Lit de les clausules on hi es, si apareix la clausula buida fallara.
% ...

% No hi ha clàusules
simplif(_, [], []).
% Si Lit negat apareix a C i després de treure'l de C és buida fallem sense buscar alternatives, permetent trobar alternatives (backtracking) si s'escau
%simplif(Lit, [C|F], [CS|FS]) :- NotLit is -Lit, member(NotLit, C), delete(C, NotLit, CS), empty(CS), !, fail.
% Si Lit negat apareix a C i després de treure'l de C, C' no és buida sense buscar alternatives, la guardem a FS
simplif(Lit, [C|F], [CS|FS]) :- NotLit is -Lit, member(NotLit, C), delete(C, NotLit, CS), !, \+empty(CS), simplif(Lit, F, FS).
% Si Lit no apareix a la clàusula C, no busquem alternatives (!) i afegim C a FS
simplif(Lit, [C|F], [C|FS]) :- \+(member(Lit, C)), !, simplif(Lit, F, FS).
% Altrament (Lit apareix a C), no afegim la clàusula i seguim iterant
simplif(Lit, [_|F], FS) :- simplif(Lit, F, FS).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%
% comaminimUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a minim una sigui certa.
% ...

comaminimUn(L, [L]).

%%%%%%%%%%%%%%%%%%%
% comamoltUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a molt una sigui certa.
% ...

treurePrimer([], []).
treurePrimer([_|L1], L1).

% No queden més variables per emparellar
parelles([], [], []) :- !.
% Emparellem una variable de la primera llista amb la segona llista, de manera que s'emparellin de forma negada
parelles([X|L1], [Y|L2], [[X2,Y2]|P]) :- X2 is X*(-1), Y2 is Y*(-1), parelles([X|L1], L2, P).
% No queden més variables de la segona llista, passem a emparellar a partir del següent element de la primera llista
parelles([X|L1], [], P) :- treurePrimer(L1, L2), parelles(L1, L2, P).


% Comencem el procés d'emparellament a partir d'una primera llista formada per la llista del paràmetre i d'una segona llista
% sense el primer element de la primera llista
parelles([X|L], P) :- parelles([X|L], L, P).

comamoltUn(L, CNF) :- parelles(L, P), append([L], P, CNF).

%%%%%%%%%%%%%%%%%%%
% exactamentUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que exactament una sigui certa.
% ...

exactamentUn(L, CNF) :- comaminimUn(L, CNF), comamoltUn(L, CNF).

%%%%%%%%%%%%%%%%%%%%%%%%%%%
% fesTauler(+N,+PI,+PP,V,I)
% Donat una dimensio de tauler N, unes posicions inicials PI i
% unes prohibides PP
% -> V sera el la llista de llistes variables necessaries per codificar el tauler
% -> I sera la CNF codificant posicions inicials i prohibides
% ...
fesTauler(N,[],[],V,[]):- trosseja(L,N,V), llista(1, N*N, L).
fesTauler(N,PI,PP,V,I) :- trosseja(L,N,V), llista(1, N*N, L),
                          Prohibit is -1, toCNF(N,Prohibit,PP,L1),
                          Reines is 1, toCNF(N,Reines,PI,L2),
                          append(L1,L2,I).
                          
% toCNF(N,Signe,Posicions,CNF).
% Donada la mida N del costat del tauler NxN i donat un Signe (valor positiu o valor negatiu) i 
% donada una llista de parells d'enters (posicions (X,Y) del tauler)
% -> CNF serà la llista d'enters a partir de l'index amb la formula Signe*((X-1)*N+Y) 
% (posicions dins un vector).
toCNF(N,Signe,[],[]).
toCNF(N,Signe,[(X,Y)],CNF):- Res is Signe*((X-1)*N+Y), append([],[Res],CNF),!.
toCNF(N,Signe,[(X,Y)|R],CNF):- Res is Signe*((X-1)*N+Y), append([Res],LR, CNF), toCNF(N, Signe, R, LR).


% AUX
% llista(I,F,L)
% Donat un inici i un fi
% -> el tercer parametre sera una llista de numeros d'inici a fi
% ...
% Hem acabat de generar l'últim ítem de la llista
llista(I, F, []) :- I > F, !.
% Generem l'últim ítem de la llista
llista(F, F, [F|L]) :- !, I is F + 1, llista(I, F, L).
% Generem l'ítem número I de la llista
llista(I, F, [I|L]) :- I2 is I + 1, llista(I2, F, L).

% AUX

% Ja som fora l'interval, hem passat de "Final" i deixem de cercar
extreu(I, F, X, _, []) :- X > F, !.
% Som fora l'interval, encara hem d'arribar a "Inici"
extreu(I, F, X, [E|L], LL) :- X < I, X2 is X + 1, extreu(I, F, X2, L, LL).
% Estem dins l'interval, l'element iterat d'L es guarda a LL
extreu(I, F, X, [E|L], [E|LL]) :- X2 is X + 1, X >= I, X =< F, extreu(I, F, X2, L, LL).

% extreu(Inici, Fi, L, LL)
% Donada una llista L i un interval d'índexos dels elements desitjats
% (Inici i Fi), LL serà la llista amb els elements que es trobin dins
% d'aquest interval dins d'L.
extreu(I, F, L, LL) :- extreu(I, F, 1, L, LL).

% Ja hem fet els "NT" (número de trossos) trossos, deixem de cercar
trosseja(_, T, NT, _, []) :- T > NT, !.
% Trossejem L per T-èssim tros
trosseja(L, T, NT, MT, [X|LL]) :- T =< NT, T2 is T + 1, I is (MT * (T - 1)) + 1, F is MT * T, extreu(I, F, L, X), trosseja(L, T2, NT, MT, LL).

% trosseja(L,N,LL)
% Donada una llista (L) i el numero de trossos que en volem (N)
% -> LL sera la llista de N llistes de L amb la mateixa mida
% (S'assumeix que la llargada de L i N ho fan possible)
% ...
trosseja(L, N, LL) :- length(L, NE), MT is NE//N, trosseja(L, 1, N, MT, LL).

% AUX
% fixa(PI,N,F)
% donada una llista de tuples de posicions PI i una mida de tauler N
% -> F es la CNF fixant les corresponents variables de posicions a certa
% ...

% AUX
% prohibeix(PP,N,P)
% donada una llista de tuples de posicions prohibides PP i una mida  tauler N
% -> P es la CNF posant les corresponents variables de posicions a fals
% ...

%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesFiles(+V,F)
% donada la matriu de variables,
% -> F sera la CNF que codifiqui que no s'amenecen les reines de les mateixes files
% ...
noAmenacesFiles([],[]).
noAmenacesFiles([H],F):- append(L,[],F), comamoltUn(H,L).
noAmenacesFiles([H|T],F):- comamoltUn(H,L), noAmenacesFiles(T,CNFaux), append(L,CNFaux,F).

transpose([[]|_], []).
transpose(Matrix, [Row|Rows]) :- transpose_1st_col(Matrix, Row, RestMatrix),
                                 transpose(RestMatrix, Rows).
transpose_1st_col([], [], []).
transpose_1st_col([[H|T]|Rows], [H|Hs], [T|Ts]) :- transpose_1st_col(Rows, Hs, Ts).


%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesColumnes(+V,C)
% donada la matriu de variables,
% -> C sera la CNF que codifiqui que no s'amenecen les reines de les mateixes columnes
% ...
noAmenacesColumnes([],[]).
noAmenacesColumnes([H],C):- noAmenacesFiles([H], C).
noAmenacesColumnes([H|T],C):- transpose([H|T], Tr), noAmenacesFiles(Tr, C).


% AQUEST PREDICAT ESTA PARCIALMENT FET. CAL QUE CALCULEU LES "ALTRES"
% DIAGONALS
%%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesDiagonals(+N,C)
% donada la mida del tauler,
% -> D sera la CNF que codifiqui que no s'amenecen les reines de les mateixes diagonals
noAmenacesDiagonals(N,D):-
    diagonals(N,L), llistesDiagonalsAVars(L,N,VARS), expandeix(VARS,D).
    
expandeix([],[]).
expandeix([H],L):- comamoltUn(H,Ls), append(Ls,[],L).
expandeix([H|R],L):- comamoltUn(H,Ls), append(Ls,Lr,L), expandeix(R,Lr).


% Genera les llistes de diagonals d'una matriu NxN. Cada diagonal es una llista de coordenades.
diagonals(N,L):- diagonalsIn(1,N,L1), diagonals2In(1,N,L2), append(L1,L2,L).

% diagonalsIn(D,N,L)
% Generem les diagonals dalt-dreta a baix-esquerra, D es el numero de
% diagonals, N la mida del tauler i L seran les diagonals generades
% Exemple:
% ?- diagonalsIn(1,3,L).
% L = [[(1,1)],[(1,2),(2,1)],[(1,3),(2,2),(3,1)],[(2,3),(3,2)],[(3,3)]]
% Evidentment les diagonals amb una sola coordenada les ignorarem...
diagonalsIn(D,N,[]):-D is 2*N,!.
diagonalsIn(D,N,[L1|L]):- D=<N,fesDiagonal(1,D,L1), D1 is D+1, diagonalsIn(D1,N,L).
diagonalsIn(D,N,[L1|L]):- D>N, F is D-N+1,fesDiagonalReves(F,N,N,L1), D1 is D+1, diagonalsIn(D1,N,L).

fesDiagonal(F,1,[(F,1)]):- !.
fesDiagonal(F,C,[(F,C)|R]):- F1 is F+1, C1 is C-1, fesDiagonal(F1,C1,R).

% quan la fila es N parem
fesDiagonalReves(N,C,N,[(N,C)]):-!.
fesDiagonalReves(F,C,N,[(F,C)|R]):-F1 is F+1, C1 is C-1, fesDiagonalReves(F1,C1,N,R). 


% diagonals2In(D,N,L)
% Generem les diagonals baix-dreta a dalt-esquerra
% Exemple
% ?- diagonals2In(1,3,L).
% L = [[(3,1)],[(3,2),(2,1)],[(3,3),(2,2),(1,1)],[(2,3),(1,2)],[(1,3)]]
% ...
diagonals2In(D,N,[]):-D is 2*N,!.
diagonals2In(D,N,[L1|L]):- D=<N, fesDiagonal2(N,D,L1), D1 is D+1, diagonals2In(D1,N,L).
diagonals2In(D,N,[L1|L]):- D>N, F is N*2-D,fesDiagonalReves2(F,N,N,L1), D1 is D+1, diagonals2In(D1,N,L).

fesDiagonal2(F,1,[(F,1)]):- !.
fesDiagonal2(F,C,[(F,C)|R]):- F1 is F-1, C1 is C-1, fesDiagonal2(F1,C1,R).

% quan la fila és 1 parem
fesDiagonalReves2(1,C,N,[(1,C)]):-!.
fesDiagonalReves2(F,C,N,[(F,C)|R]):-F1 is F-1, C1 is C-1, fesDiagonalReves2(F1,C1,N,R). 


% Passa una llista de coordenades  de tauler NxN a variables corresponents.
coordenadesAVars([],_,[]).
coordenadesAVars([(F,C)|R],N,[V|RV]):-V is (F-1)*N+C, coordenadesAVars(R,N,RV).

% Passa una llista de diagonals a llistes de llistes de variables
%llistesDiagonalsAVars(Lparells,N,Lvars).
%...
llistesDiagonalsAVars([],_,[]).
llistesDiagonalsAVars([H],N,L):- toCNF(N,1,H,Ls), append([Ls],[],L).
llistesDiagonalsAVars([H|R],N,L):- toCNF(N,1,H,Ls), append([Ls],Lr,L), llistesDiagonalsAVars(R,N,Lr).

%%%%%%%%%%%%%%%%%%%%%
% minimNReines(+V,FN)
% donada la matriu de variables (inicialment d'un tauler NxN),
% -> FN sera la CNF que codifiqui que hi ha d'haver com a minim N reines al tauler
% ...
minimNReines(V,F):- V=F.

llegeixNombre(X) :- read(X), number(X), !.

llegeixLlista([X|L]) :- read(X), number(X), X > 0, llegeixLlista(L).
llegeixLlista([]).

filtrarPositius([], []).
filtrarPositius([X|L], [X|P]) :- X > 0, !, filtrarPositius(L, P).
filtrarPositius([_|L], P) :- filtrarPositius(L, P).

%%%%%%%%%
% resol()
% Ens demana els parametres del tauler i l'estat inicial,
% codifica les restriccions del problema i en fa una formula
% que la enviem a resoldre amb el SAT solver
% i si te solucio en mostrem el tauler
resol :-
    write('Introdueix mida N del tauler NxN: '),
    llegeixNombre(N),
    write('Introdueix les posicions inicials (entra un <= 0 per acabar): \n'),
    llegeixLlista(I),
    write('Introdueix les posicions prohibides (entra un <= 0 per acabar): \n'),
    llegeixLlista(P),
    fesTauler(N, I, P, V, Ini),
    minimNReines(V, FN),
    append(Ini, FN, CNF),
    noAmenacesFiles(V, CNFfiles),
    append(CNFfiles, CNF, CNF2),
    noAmenacesColumnes(V, CNFcolumnes),
    append(CNFcolumnes, CNF2, CNF3),
    noAmenacesDiagonals(N, CNFdiagonals),
    append(CNFdiagonals, CNF3, CNF4),
    sat(CNF4, [], M),
    filtrarPositius(M, M2),
    mostraTauler(N, M2).


%%%%%%%%%%%%%%%%%%%
% mostraTauler(N,M)
% donat una mida de tauler N i una llista de numeros d'1 a N*N,
% mostra el tauler posant una Q a cada posicio recorrent per files
% d'equerra a dreta.
% Per exemple:
% | ?- mostraTauler(3,[1,5,8,9...]).
% -------
% |Q| | |
% -------
% | |Q| |
% -------
% | |Q|Q|
% -------
% Fixeu-vos que li passarem els literals positius del model de la nostra
% formula.
% ...

mostrar([], S, Q) :- !.
mostrar([[C|R]|L], S, Q) :- member(C, Q), write('|Q'), !, mostrar([R|L], S, Q).
mostrar([[C|R]|L], S, Q) :- write('| '), !, mostrar([R|L], S, Q).
mostrar([[C|[]]|L], S, Q) :- member(C, Q), write(' Q'), !, mostrar(L, S, Q).
mostrar([[C|[]]|L], S, Q) :- write(' '), !, mostrar(L, S, Q).
mostrar([[]|L], S, Q) :- write('|\n'), mostrarSeparador(S), !, mostrar(L, S, Q).

mostrarSeparador(0) :- write('\n').
mostrarSeparador(N) :- write('-'), N2 is N-1, mostrarSeparador(N2).

mostraTauler(N, Q) :- S is (N+1)+N, mostrarSeparador(S), M is N*N, llista(1, M, L), trosseja(L, N, C), mostrar(C, S, Q).































