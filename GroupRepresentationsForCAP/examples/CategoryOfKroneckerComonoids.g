#! @Chapter TODO
#! @Section Examples and Tests

#! @Example
LoadPackage( "GroupRepresentationsForCAP", false );
#! true

kron_comon := CategoryOfKroneckerComonoids( );;

Display( kron_comon );
#! A CAP category with name KroneckerComonoids:
#! 
#! 19 primitive operations were used to derive 56 operations for this categor\
#! y which algorithmically
#! * IsCartesianCategory
#! and furthermore mathematically
#! * IsSkeletalCategory

F_perms := IsomorphismFromCoreToPermutationCategory( kron_comon );;

Q := HomalgFieldOfRationals();;
rows := CategoryOfRows( Q );;
F_rows := EmbeddingOfKroneckerComonoidsIntoCategoryOfRows( kron_comon, rows );;

o0 := ObjectConstructor( kron_comon, 0 );;
o1 := ObjectConstructor( kron_comon, 1 );;
o2 := ObjectConstructor( kron_comon, 2 );;
o3 := ObjectConstructor( kron_comon, 3 );;
o4 := ObjectConstructor( kron_comon, 4 );;
o5 := ObjectConstructor( kron_comon, 5 );;
o9 := ObjectConstructor( kron_comon, 9 );;

m52_12 := MorphismConstructor( kron_comon, o5, [ 1, [ [1,2] ] ], o2 );;
m52_34 := MorphismConstructor( kron_comon, o5, [ 1, [ [3,4] ] ], o2 );;
m54_25 := MorphismConstructor( kron_comon, o5, [ 1, [ [2,5] ] ], o4 );;
m55_21435 := MorphismConstructor( kron_comon,
                o5,
                [ 5, [ [ 2, 2 ], [ 1, 1 ], [ 4, 4 ], [ 3, 3 ], [ 5, 5 ] ] ],
                o5 );;

IsWellDefinedForObjects( o5 );
#! true
IsWellDefinedForObjects( o4 );
#! true

IsWellDefinedForMorphisms( m52_12 );
#! true
IsWellDefinedForMorphisms( m52_34 );
#! true
IsWellDefinedForMorphisms( m54_25 );
#! true

id_o0 := IdentityMorphism( o0 );;
id_o1 := IdentityMorphism( o1 );;
id_o2 := IdentityMorphism( o2 );;
id_o3 := IdentityMorphism( o3 );;
id_o4 := IdentityMorphism( o4 );;
id_o5 := IdentityMorphism( o5 );;

IsWellDefinedForMorphisms( id_o1 );
#! true
IsWellDefinedForMorphisms( id_o2 );
#! true

terminal_object := TerminalObject( kron_comon );;
Display( terminal_object );
#! 0

Display( DirectProduct( o5, o4 ) );
#! 9
Display( TensorProductOnObjects( o5, o4 ) );
#! 20

##############################################################
# Functor to CategoryOfRows
##############################################################

Display( ApplyFunctor( F_perms, id_o5 ) );
#! 5 ⱶ()→ 5

Display( ApplyFunctor( F_perms, id_o4 ) );
#! 4 ⱶ()→ 4

Display( ApplyFunctor( F_perms, m55_21435 ) );
#! 5 ⱶ(1,2)(3,4)→ 5

##############################################################
# Functor to PermutationCategory
##############################################################

Display( ApplyFunctor( F_rows, id_o5 ) );
#! Source: 
#! A row module over Q of rank 5
#! 
#! Matrix: 
#! [ [  1,  0,  0,  0,  0 ],
#!   [  0,  1,  0,  0,  0 ],
#!   [  0,  0,  1,  0,  0 ],
#!   [  0,  0,  0,  1,  0 ],
#!   [  0,  0,  0,  0,  1 ] ]
#! 
#! Range: 
#! A row module over Q of rank 5
#! 
#! A morphism in Rows( Q )

Display( ApplyFunctor( F_rows, id_o4 ) );
#! Source: 
#! A row module over Q of rank 4
#! 
#! Matrix: 
#! [ [  1,  0,  0,  0 ],
#!   [  0,  1,  0,  0 ],
#!   [  0,  0,  1,  0 ],
#!   [  0,  0,  0,  1 ] ]
#! 
#! Range: 
#! A row module over Q of rank 4
#! 
#! A morphism in Rows( Q )

Display( ApplyFunctor( F_rows, m52_12 ) );
#! Source: 
#! A row module over Q of rank 5
#! 
#! Matrix: 
#! [ [  1,  0 ],
#!   [  0,  1 ],
#!   [  0,  0 ],
#!   [  0,  0 ],
#!   [  0,  0 ] ]
#! 
#! Range: 
#! A row module over Q of rank 2
#! 
#! A morphism in Rows( Q )

Display( ApplyFunctor( F_rows, m52_34 ) );
#! Source: 
#! A row module over Q of rank 5
#! 
#! Matrix: 
#! [ [  0,  0 ],
#!   [  0,  0 ],
#!   [  1,  0 ],
#!   [  0,  1 ],
#!   [  0,  0 ] ]
#! 
#! Range: 
#! A row module over Q of rank 2
#! 
#! A morphism in Rows( Q )

Display( ApplyFunctor( F_rows, m54_25 ) );
#! Source: 
#! A row module over Q of rank 5
#! 
#! Matrix: 
#! [ [  0,  0,  0,  0 ],
#!   [  1,  0,  0,  0 ],
#!   [  0,  1,  0,  0 ],
#!   [  0,  0,  1,  0 ],
#!   [  0,  0,  0,  1 ] ]
#! 
#! Range: 
#! A row module over Q of rank 4
#! 
#! A morphism in Rows( Q )

##############################################################
# IsEqualForMorphisms
##############################################################

id_5 := MorphismConstructor( kron_comon, o5, [ 2, [ [1,3], [4,5] ] ], o5 );;
id_5_alternate := MorphismConstructor( kron_comon, o5, [ 3, [ [1,2], [3,3], [4,5] ] ], o5 );;

m55 := MorphismConstructor( kron_comon, o5, [ 2, [ [2,2], [2,5] ] ], o5 );;
m55_54 := MorphismConstructor( kron_comon, o5, [ 3, [ [2,2], [3,3], [4,5] ] ], o4 );;

IsEqualForMorphisms( m52_12, m52_12 );
#! true

IsEqualForMorphisms( m55, m55 );
#! true

IsEqualForMorphisms( id_o0, IdentityMorphism( terminal_object ) );
#! true

IsEqualForMorphisms( id_5, m55 );
#! false

IsEqualForMorphisms( id_5_alternate, m55 );
#! false

IsEqualForMorphisms( id_5, IdentityMorphism( o5 ) );
#! false

IsEqualForMorphisms( id_5_alternate, IdentityMorphism( o5 ) );
#! false

IsEqualForMorphisms( id_5, id_5_alternate );
#! false

##############################################################
# SimplifyMorphism
##############################################################

SimplifyMorphism( UniversalMorphismIntoTerminalObject( TerminalObject( kron_comon ) ), 2 );

##############################################################
# IsCongruentForMorphisms
##############################################################

IsCongruentForMorphisms( m52_12, m52_12 );
#! true

IsCongruentForMorphisms( m55, m55 );
#! true

IsCongruentForMorphisms( id_o0, IdentityMorphism( terminal_object ) );
#! true

IsCongruentForMorphisms( id_5, IdentityMorphism( o5 ) );
#! true

IsCongruentForMorphisms( id_5_alternate, IdentityMorphism( o5 ) );
#! true

IsCongruentForMorphisms( id_5, id_5_alternate );
#! true

IsCongruentForMorphisms( id_5, m55 );
#! false

IsCongruentForMorphisms( id_5_alternate, m55 );
#! false

##############################################################
# IsTerminal
##############################################################

IsTerminal( terminal_object );
#! true

IsTerminal( o1 );
#! false

IsTerminal( o5 );
#! false

##############################################################
# UniversalMorphismIntoTerminalObject
##############################################################

Display( ApplyFunctor( F_rows, UniversalMorphismIntoTerminalObject( o4 ) ) );
#! Source: 
#! A row module over Q of rank 4
#! 
#! Matrix: 
#! (an empty 4 x 0 matrix)
#! 
#! Range: 
#! A row module over Q of rank 0
#! 
#! A morphism in Rows( Q )

Display( ApplyFunctor( F_rows, UniversalMorphismIntoTerminalObject( o5 ) ) );
#! Source: 
#! A row module over Q of rank 5
#! 
#! Matrix: 
#! (an empty 5 x 0 matrix)
#! 
#! Range: 
#! A row module over Q of rank 0
#! 
#! A morphism in Rows( Q )

NrBlockColumnsAndListOfBlockColumns( UniversalMorphismIntoTerminalObject( terminal_object ) );
#! [  ]
Display( ApplyFunctor( F_rows, UniversalMorphismIntoTerminalObject( terminal_object ) ) );
#! Source: 
#! A row module over Q of rank 0
#! 
#! Matrix: 
#! (an empty 0 x 0 matrix)
#! 
#! Range: 
#! A row module over Q of rank 0
#! 
#! A morphism in Rows( Q )

##############################################################
# ProjectionInFactorOfDirectProductWithGivenDirectProduct
##############################################################

proj := ApplyFunctor( F_rows, ProjectionInFactorOfDirectProduct( [ o3, o2, o5 ], 2 ) );;

Display( proj );
#! Source: 
#! A row module over Q of rank 10
#! 
#! Matrix: 
#! [ [  0,  0 ],
#!   [  0,  0 ],
#!   [  0,  0 ],
#!   [  1,  0 ],
#!   [  0,  1 ],
#!   [  0,  0 ],
#!   [  0,  0 ],
#!   [  0,  0 ],
#!   [  0,  0 ],
#!   [  0,  0 ] ]
#! 
#! Range: 
#! A row module over Q of rank 2
#! 
#! A morphism in Rows( Q )

proj_rows := ProjectionInFactorOfDirectProduct( [ CategoryOfRowsObject( rows, 3 ),
                                                  CategoryOfRowsObject( rows, 2 ),
                                                  CategoryOfRowsObject( rows, 5 ) ], 2 );

UnderlyingMatrix( proj ) = UnderlyingMatrix( proj_rows );
#! true

proj2 := ProjectionInFactorOfDirectProduct( [terminal_object, terminal_object, terminal_object ], 2 );;
NrBlockColumnsAndListOfBlockColumns( proj2 );
#! [ 0, [  ] ]

proj2 := ApplyFunctor( F_rows, proj2 );;

Display( proj2 );
#! Source: 
#! A row module over Q of rank 0
#! 
#! Matrix: 
#! (an empty 0 x 0 matrix)
#! 
#! Range: 
#! A row module over Q of rank 0
#! 
#! A morphism in Rows( Q )

proj2_rows := ProjectionInFactorOfDirectProduct( [ TerminalObject( rows ),
                                                   TerminalObject( rows ),
                                                   TerminalObject( rows ) ], 2 );

UnderlyingMatrix( proj2 ) = UnderlyingMatrix( proj2_rows );
#! true

##############################################################
# UniversalMorphismIntoDirectProduct
##############################################################

Display( ApplyFunctor( F_rows, UniversalMorphismIntoDirectProduct( [ id_o5, m52_34 ] ) ) );
#! Source: 
#! A row module over Q of rank 5
#! 
#! Matrix: 
#! [ [  1,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  1,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  1,  0,  0,  1,  0 ],
#!   [  0,  0,  0,  1,  0,  0,  1 ],
#!   [  0,  0,  0,  0,  1,  0,  0 ] ]
#! 
#! Range: 
#! A row module over Q of rank 7
#! 
#! A morphism in Rows( Q )

Display( ApplyFunctor( F_rows, UniversalMorphismIntoDirectProduct( [ id_o5, m54_25 ] ) ) );
#! Source: 
#! A row module over Q of rank 5
#! 
#! Matrix: 
#! [ [  1,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  1,  0,  0,  0,  1,  0,  0,  0 ],
#!   [  0,  0,  1,  0,  0,  0,  1,  0,  0 ],
#!   [  0,  0,  0,  1,  0,  0,  0,  1,  0 ],
#!   [  0,  0,  0,  0,  1,  0,  0,  0,  1 ] ]
#! 
#! Range: 
#! A row module over Q of rank 9
#! 
#! A morphism in Rows( Q )

Display( ApplyFunctor( F_rows, UniversalMorphismIntoDirectProduct( [ m54_25, id_o5 ] ) ) );
#! Source: 
#! A row module over Q of rank 5
#! 
#! Matrix: 
#! [ [  0,  0,  0,  0,  1,  0,  0,  0,  0 ],
#!   [  1,  0,  0,  0,  0,  1,  0,  0,  0 ],
#!   [  0,  1,  0,  0,  0,  0,  1,  0,  0 ],
#!   [  0,  0,  1,  0,  0,  0,  0,  1,  0 ],
#!   [  0,  0,  0,  1,  0,  0,  0,  0,  1 ] ]
#! 
#! Range: 
#! A row module over Q of rank 9
#! 
#! A morphism in Rows( Q )

##############################################################
# DirectProductFunctorial
##############################################################

Display( ApplyFunctor( F_rows, DirectProductFunctorial( [ m54_25, id_o5 ] ) ) );
#! Source: 
#! A row module over Q of rank 10
#! 
#! Matrix: 
#! [ [  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  1,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  1,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  1,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  1,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  1,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  1,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  1,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  1,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  1 ] ]
#! 
#! Range: 
#! A row module over Q of rank 9
#! 
#! A morphism in Rows( Q )

Display( ApplyFunctor( F_rows, DirectProductFunctorial( [ m54_25, m52_34 ] ) ) );
#! Source: 
#! A row module over Q of rank 10
#! 
#! Matrix: 
#! [ [  0,  0,  0,  0,  0,  0 ],
#!   [  1,  0,  0,  0,  0,  0 ],
#!   [  0,  1,  0,  0,  0,  0 ],
#!   [  0,  0,  1,  0,  0,  0 ],
#!   [  0,  0,  0,  1,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  1,  0 ],
#!   [  0,  0,  0,  0,  0,  1 ],
#!   [  0,  0,  0,  0,  0,  0 ] ]
#! 
#! Range: 
#! A row module over Q of rank 6
#! 
#! A morphism in Rows( Q )

product_functorial := DirectProductFunctorial( [ m54_25, UniversalMorphismIntoTerminalObject( o4 ) ] );;

Display( ApplyFunctor( F_rows, product_functorial ) );
#! Source: 
#! A row module over Q of rank 9
#! 
#! Matrix: 
#! [ [  0,  0,  0,  0 ],
#!   [  1,  0,  0,  0 ],
#!   [  0,  1,  0,  0 ],
#!   [  0,  0,  1,  0 ],
#!   [  0,  0,  0,  1 ],
#!   [  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0 ] ]
#! 
#! Range: 
#! A row module over Q of rank 4
#! 
#! A morphism in Rows( Q )

##############################################################
# TensorProductOnMorphisms
##############################################################

tp_mor := TensorProductOnMorphisms( id_o2, id_o2 );;
NrBlockColumnsAndListOfBlockColumns( tp_mor );
#! [ 2, [ [ 1, 2 ], [ 3, 4 ] ] ]

Display( ApplyFunctor( F_rows, tp_mor  ) );
#! Source: 
#! A row module over Q of rank 4
#! 
#! Matrix: 
#! [ [  1,  0,  0,  0 ],
#!   [  0,  1,  0,  0 ],
#!   [  0,  0,  1,  0 ],
#!   [  0,  0,  0,  1 ] ]
#! 
#! Range: 
#! A row module over Q of rank 4
#! 
#! A morphism in Rows( Q )

tp_mor := TensorProductOnMorphisms( id_o2, id_o3 );;
NrBlockColumnsAndListOfBlockColumns( tp_mor );
#! [ 2, [ 1, 3 ], [ 4, 6 ] ]
Display( ApplyFunctor( F_rows, tp_mor ) );
#! Source: 
#! A row module over Q of rank 6
#! 
#! Matrix: 
#! [ [  1,  0,  0,  0,  0,  0 ],
#!   [  0,  1,  0,  0,  0,  0 ],
#!   [  0,  0,  1,  0,  0,  0 ],
#!   [  0,  0,  0,  1,  0,  0 ],
#!   [  0,  0,  0,  0,  1,  0 ],
#!   [  0,  0,  0,  0,  0,  1 ] ]
#! 
#! Range: 
#! A row module over Q of rank 6
#! 
#! A morphism in Rows( Q )

tp_mor := TensorProductOnMorphisms( product_functorial, id_o2 );;
NrBlockColumnsAndListOfBlockColumns( tp_mor );
#! [ 4, [ 3, 4 ], [ 5, 6 ], [ 7, 8 ], [ 9, 10 ] ]
m1m2 := UnderlyingMatrix( ApplyFunctor( F_rows, tp_mor ) );;
Display( m1m2 );
#! [ [  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  1,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  1,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  1,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  1,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  1,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  1,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  1,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  1 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0 ] ]

m1 := UnderlyingMatrix( ApplyFunctor( F_rows, product_functorial ) );;
m2 := HomalgIdentityMatrix( 2, Q );;
m1m2 = KroneckerMat( m1, m2 );
#! true

m93 := MorphismConstructor( kron_comon, o9, [ 1, [ [5,7] ] ], o3 );;
m54 := MorphismConstructor( kron_comon, o5, [ 2, [ [2,3], [1,2] ] ], o4 );;

tp_mor := TensorProductOnMorphisms( m93, m54 );;
NrBlockColumnsAndListOfBlockColumns( tp_mor );
#! [ 6, 
#!   [ [ 22, 23 ], [ 21, 22 ], [ 27, 28 ], [ 26, 27 ], [ 32, 33 ], 
#!       [ 31, 32 ] ] ]
m93_times_m54 := UnderlyingMatrix( ApplyFunctor( F_rows, tp_mor ) );;
m93_times_m54 = KroneckerMat( UnderlyingMatrix( ApplyFunctor( F_rows, m93 ) ),
                              UnderlyingMatrix( ApplyFunctor( F_rows, m54 ) ) );
#! true

Display( m93_times_m54 );
#! [ [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  1,  0,  0,  1,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  1,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  1,  0,  0,  1,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  1,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0,  1 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 ] ]

m95 := MorphismConstructor( kron_comon, o9, [ 2, [ [4,5], [5,7] ] ], o5 );;
m55 := MorphismConstructor( kron_comon, o5, [ 2, [ [2,3], [1,3] ] ], o5 );;

tp_mor := TensorProductOnMorphisms( m95, m55 );;
NrBlockColumnsAndListOfBlockColumns( tp_mor );
#! [ 6, 
#!   [ [ 22, 23 ], [ 21, 22 ], [ 27, 28 ], [ 26, 27 ], [ 32, 33 ], 
#!       [ 31, 32 ] ] ]
m95_times_m55 := UnderlyingMatrix( ApplyFunctor( F_rows, tp_mor ) );;
m95_times_m55 = KroneckerMat( UnderlyingMatrix( ApplyFunctor( F_rows, m95 ) ),
                              UnderlyingMatrix( ApplyFunctor( F_rows, m55 ) ) );
#! true

Display( m95_times_m55 );
#! [ [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  1,  0,  0,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  1,  0,  0,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  1,  0,  0,  0,  0,  1,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  1,  0,  0,  1,  0,  1,  0,  0,  1,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  1,  0,  0,  1,  0,  1,  0,  0,  1,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0\
#! ,  1,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0\
#! ,  0,  1,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  1,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  1,  0,  0,  1,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  1,  0,  0,  1 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ],
#!   [  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0\
#! ,  0,  0,  0,  0,  0,  0,  0 ] ]

##############################################################
# TensorProductOfMorphismWithIdentityWithGivenTensorProducts
##############################################################

tp_mor := CATEGORY_OF_INSERTION_MATRICES_TensorProductOfMorphismWithIdentityWithGivenTensorProducts( kron_comon,
            TensorProductOnObjects( o5, o3 ),
            m52_34,
            id_o3,
            TensorProductOnObjects( o2, o3 ) );

matrix := UnderlyingMatrix( ApplyFunctor( F_rows, tp_mor ) );;
matrix = KroneckerMat( UnderlyingMatrix( ApplyFunctor( F_rows, m52_34 ) ),
                       UnderlyingMatrix( ApplyFunctor( F_rows, id_o3 ) ) );
#! true

tp_mor := CATEGORY_OF_INSERTION_MATRICES_TensorProductOfMorphismWithIdentityWithGivenTensorProducts( kron_comon,
            TensorProductOnObjects( o5, o5 ),
            m54_25,
            id_o5,
            TensorProductOnObjects( o4, o5 ) );

matrix := UnderlyingMatrix( ApplyFunctor( F_rows, tp_mor ) );;
matrix = KroneckerMat( UnderlyingMatrix( ApplyFunctor( F_rows, m54_25 ) ),
                       UnderlyingMatrix( ApplyFunctor( F_rows, id_o5 ) ) );
#! true

tp_mor := CATEGORY_OF_INSERTION_MATRICES_TensorProductOfMorphismWithIdentityWithGivenTensorProducts( kron_comon,
            TensorProductOnObjects( o5, o4 ),
            m55_54,
            id_o4,
            TensorProductOnObjects( o4, o4 ) );

matrix := UnderlyingMatrix( ApplyFunctor( F_rows, tp_mor ) );;
matrix = KroneckerMat( UnderlyingMatrix( ApplyFunctor( F_rows, m55_54 ) ),
                       UnderlyingMatrix( ApplyFunctor( F_rows, id_o4 ) ) );
#! true

tp_mor := CATEGORY_OF_INSERTION_MATRICES_TensorProductOfMorphismWithIdentityWithGivenTensorProducts( kron_comon,
            TensorProductOnObjects( o5, o0 ),
            m52_34,
            id_o0,
            TensorProductOnObjects( o2, o0 ) );

matrix := UnderlyingMatrix( ApplyFunctor( F_rows, tp_mor ) );;
matrix = KroneckerMat( UnderlyingMatrix( ApplyFunctor( F_rows, m52_34 ) ),
                       UnderlyingMatrix( ApplyFunctor( F_rows, id_o0 ) ) );
#! true

##############################################################
# TensorProductOfIdentityWithMorphismWithGivenTensorProducts
##############################################################

tp_mor := CATEGORY_OF_INSERTION_MATRICES_TensorProductOfIdentityWithMorphismWithGivenTensorProducts( kron_comon,
            TensorProductOnObjects( o3, o5 ),
            id_o3,
            m52_34,
            TensorProductOnObjects( o3, o2 ) );

matrix := UnderlyingMatrix( ApplyFunctor( F_rows, tp_mor ) );;
matrix = KroneckerMat( UnderlyingMatrix( ApplyFunctor( F_rows, id_o3 ) ),
                       UnderlyingMatrix( ApplyFunctor( F_rows, m52_34 ) ) );
#! true

tp_mor := CATEGORY_OF_INSERTION_MATRICES_TensorProductOfIdentityWithMorphismWithGivenTensorProducts( kron_comon,
            TensorProductOnObjects( o5, o5 ),
            id_o5,
            m54_25,
            TensorProductOnObjects( o5, o4 ) );

matrix := UnderlyingMatrix( ApplyFunctor( F_rows, tp_mor ) );;
matrix = KroneckerMat( UnderlyingMatrix( ApplyFunctor( F_rows, id_o5 ) ),
                       UnderlyingMatrix( ApplyFunctor( F_rows, m54_25 ) ) );
#! true

tp_mor := CATEGORY_OF_INSERTION_MATRICES_TensorProductOfIdentityWithMorphismWithGivenTensorProducts( kron_comon,
            TensorProductOnObjects( o4, o5 ),
            id_o4,
            m55_54,
            TensorProductOnObjects( o4, o4 ) );

matrix := UnderlyingMatrix( ApplyFunctor( F_rows, tp_mor ) );;
matrix = KroneckerMat( UnderlyingMatrix( ApplyFunctor( F_rows, id_o4 ) ),
                       UnderlyingMatrix( ApplyFunctor( F_rows, m55_54 ) ) );
#! true

tp_mor := CATEGORY_OF_INSERTION_MATRICES_TensorProductOfIdentityWithMorphismWithGivenTensorProducts( kron_comon,
            TensorProductOnObjects( o0, o5 ),
            id_o0,
            m52_34,
            TensorProductOnObjects( o0, o2 ) );

matrix := UnderlyingMatrix( ApplyFunctor( F_rows, tp_mor ) );;
matrix = KroneckerMat( UnderlyingMatrix( ApplyFunctor( F_rows, id_o0 ) ),
                       UnderlyingMatrix( ApplyFunctor( F_rows, m52_34 ) ) );
#! true

##############################################################
# RowRotation
##############################################################

source := ObjectConstructor( kron_comon, 56 );;
target := ObjectConstructor( kron_comon, 6 );;

mor := MorphismConstructor( kron_comon, source, [ 2, [ [ 1, 4 ], [ 25, 26 ] ] ], target );;
IsWellDefinedForMorphisms( mor );
#! true

mor_shift_1 := CATEGORY_OF_INSERTION_MATRICES_RowDownwardShift( kron_comon, mor, 1 );;
mor_shift_2 := CATEGORY_OF_INSERTION_MATRICES_RowDownwardShift( kron_comon, mor, 2 );;
mor_shift_3 := CATEGORY_OF_INSERTION_MATRICES_RowDownwardShift( kron_comon, mor, 3 );;
mor_shift_4 := CATEGORY_OF_INSERTION_MATRICES_RowDownwardShift( kron_comon, mor, 4 );;
mor_shift_5 := CATEGORY_OF_INSERTION_MATRICES_RowDownwardShift( kron_comon, mor, 5 );;
mor_shift_6 := CATEGORY_OF_INSERTION_MATRICES_RowDownwardShift( kron_comon, mor, 6 );;

IsWellDefinedForMorphisms( mor_shift_1 );
#! true
IsWellDefinedForMorphisms( mor_shift_2 );
#! true
IsWellDefinedForMorphisms( mor_shift_3 );
#! true
IsWellDefinedForMorphisms( mor_shift_4 );
#! true
IsWellDefinedForMorphisms( mor_shift_5 );
#! true

Display( mor );
#! [ 2, [ [ 1, 4 ], [ 25, 26 ] ] ]
Display( mor_shift_1 );
#! [ 2, [ [ 5, 8 ], [ 27, 28 ] ] ]
Display( mor_shift_2 );
#! [ 2, [ [ 9, 12 ], [ 29, 30 ] ] ]
Display( mor_shift_3 );
#! [ 2, [ [ 13, 16 ], [ 31, 32 ] ] ]
Display( mor_shift_4 );
#! [ 2, [ [ 17, 20 ], [ 33, 34 ] ] ]
Display( mor_shift_5 );
#! [ 2, [ [ 21, 24 ], [ 35, 36 ] ] ]

#! @EndExample
