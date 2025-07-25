#! @Chapter TODO
#! @Section Examples and Tests

#! @Example
LoadPackage( "GroupRepresentationsForCAP", false );
#! true

ins_mat := CategoryOfInsertionMatrices( );;

Display( ins_mat );
#! A CAP category with name CategoryOfInsertionMatrices:
#! 
#! 19 primitive operations were used to derive 56 operations for this categor\
#! y which algorithmically
#! * IsCartesianCategory
#! and furthermore mathematically
#! * IsSkeletalCategory

Q := HomalgFieldOfRationals();
rows := CategoryOfRows( Q );

F := Functorins_matToCategoryOfRows( ins_mat, rows );

o0 := ObjectConstructor( ins_mat, 0 );
o1 := ObjectConstructor( ins_mat, 1 );
o2 := ObjectConstructor( ins_mat, 2 );
o3 := ObjectConstructor( ins_mat, 3 );
o4 := ObjectConstructor( ins_mat, 4 );
o5 := ObjectConstructor( ins_mat, 5 );
o9 := ObjectConstructor( ins_mat, 9 );

m52_12 := MorphismConstructor( ins_mat, o5, [ 1, [ [1,2] ] ], o2 );
m52_34 := MorphismConstructor( ins_mat, o5, [ 1, [ [3,4] ] ], o2 );
m54_25 := MorphismConstructor( ins_mat, o5, [ 1, [ [2,5] ] ], o4 );

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

terminal_object := TerminalObject( ins_mat );;
Display( terminal_object );
#! 0

Display( DirectProduct( o5, o4 ) );
#! 9
Display( TensorProductOnObjects( o5, o4 ) );
#! 20

Display( ApplyFunctor( F, id_o5 ) );
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

Display( ApplyFunctor( F, id_o4 ) );
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

Display( ApplyFunctor( F, m52_12 ) );
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

Display( ApplyFunctor( F, m52_34 ) );
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

Display( ApplyFunctor( F, m54_25 ) );
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

id_5 := MorphismConstructor( ins_mat, o5, [ 2, [ [1,3], [4,5] ] ], o5 );
id_5_alternate := MorphismConstructor( ins_mat, o5, [ 3, [ [1,2], [3,3], [4,5] ] ], o5 );

m55 := MorphismConstructor( ins_mat, o5, [ 2, [ [2,2], [2,5] ] ], o5 );
m55_54 := MorphismConstructor( ins_mat, o5, [ 3, [ [2,2], [3,3], [4,5] ] ], o4 );

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

SimplifyMorphism( UniversalMorphismIntoTerminalObject( TerminalObject( ins_mat ) ), 2 );

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

Display( ApplyFunctor( F, UniversalMorphismIntoTerminalObject( o4 ) ) );
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

Display( ApplyFunctor( F, UniversalMorphismIntoTerminalObject( o5 ) ) );
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
Display( ApplyFunctor( F, UniversalMorphismIntoTerminalObject( terminal_object ) ) );
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

proj := ApplyFunctor( F, ProjectionInFactorOfDirectProduct( [ o3, o2, o5 ], 2 ) );

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

proj2 := ProjectionInFactorOfDirectProduct( [terminal_object, terminal_object, terminal_object ], 2 );
NrBlockColumnsAndListOfBlockColumns( proj2 );
#! [ 0, [  ] ]

proj2 := ApplyFunctor( F, proj2 );

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

Display( ApplyFunctor( F, UniversalMorphismIntoDirectProduct( [ id_o5, m52_34 ] ) ) );
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

Display( ApplyFunctor( F, UniversalMorphismIntoDirectProduct( [ id_o5, m54_25 ] ) ) );
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

Display( ApplyFunctor( F, UniversalMorphismIntoDirectProduct( [ m54_25, id_o5 ] ) ) );
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

Display( ApplyFunctor( F, DirectProductFunctorial( [ m54_25, id_o5 ] ) ) );
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

Display( ApplyFunctor( F, DirectProductFunctorial( [ m54_25, m52_34 ] ) ) );
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

Display( ApplyFunctor( F, product_functorial ) );
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

Display( ApplyFunctor( F, tp_mor  ) );
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
Display( ApplyFunctor( F, tp_mor ) );
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
m1m2 := UnderlyingMatrix( ApplyFunctor( F, tp_mor ) );;
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

m1 := UnderlyingMatrix( ApplyFunctor( F, product_functorial ) );;
m2 := HomalgIdentityMatrix( 2, Q );;
m1m2 = KroneckerMat( m1, m2 );
#! true

m93 := MorphismConstructor( ins_mat, o9, [ 1, [ [5,7] ] ], o3 );;
m54 := MorphismConstructor( ins_mat, o5, [ 2, [ [2,3], [1,2] ] ], o4 );;

tp_mor := TensorProductOnMorphisms( m93, m54 );;
NrBlockColumnsAndListOfBlockColumns( tp_mor );
#! [ 6, 
#!   [ [ 22, 23 ], [ 21, 22 ], [ 27, 28 ], [ 26, 27 ], [ 32, 33 ], 
#!       [ 31, 32 ] ] ]
m93_times_m54 := UnderlyingMatrix( ApplyFunctor( F, tp_mor ) );
m93_times_m54 = KroneckerMat( UnderlyingMatrix( ApplyFunctor( F, m93 ) ),
                              UnderlyingMatrix( ApplyFunctor( F, m54 ) ) );
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

m95 := MorphismConstructor( ins_mat, o9, [ 2, [ [4,5], [5,7] ] ], o5 );;
m55 := MorphismConstructor( ins_mat, o5, [ 2, [ [2,3], [1,3] ] ], o5 );;

tp_mor := TensorProductOnMorphisms( m95, m55 );;
NrBlockColumnsAndListOfBlockColumns( tp_mor );
#! [ 6, 
#!   [ [ 22, 23 ], [ 21, 22 ], [ 27, 28 ], [ 26, 27 ], [ 32, 33 ], 
#!       [ 31, 32 ] ] ]
m95_times_m55 := UnderlyingMatrix( ApplyFunctor( F, tp_mor ) );
m95_times_m55 = KroneckerMat( UnderlyingMatrix( ApplyFunctor( F, m95 ) ),
                              UnderlyingMatrix( ApplyFunctor( F, m55 ) ) );
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

#! @EndExample
