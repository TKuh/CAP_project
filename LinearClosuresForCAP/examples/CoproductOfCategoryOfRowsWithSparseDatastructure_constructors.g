#! @BeginChunk CoproductCategoryOfRowsWithSparseDatastructure_constructors

#! @Example
LoadPackage( "RingsForHomalg", false );
#! true
LoadPackage( "LinearClosuresForCAP", false );
#! true

QQ := HomalgFieldOfRationals();;
rows := CategoryOfRows( QQ );;
coproduct := CoproductOfCategoryOfRowsWithSparseDatastructure( rows, 5 );;

obj := [ [2,2], [1,3], [1,5] ] / coproduct;
#! <An object in ⊕ ( CategoryOfRows( Q ), 5 )>
IsWellDefinedForObjects( obj );
#! true

source := [        [2,2], [1,3], [1,5] ] / coproduct;;
target := [ [3,1], [1,2], [2,3]        ] / coproduct;;

matrix_1 := HomalgMatrix( [ ], 0, 3, QQ );;
matrix_2 := HomalgMatrix( [ [ 4 ], [ 1 ] ], 2, 1, QQ );;
matrix_3 := HomalgMatrix( [ [ 5, 6 ] ], 1, 2, QQ );;
matrix_4 := HomalgMatrix( [ ], 0, 0, QQ );;
matrix_5 := HomalgMatrix( [ ], 1, 0, QQ );;
morphism_pairs := [ [ AsCategoryOfRowsMorphism( rows, matrix_1 ), 1 ],
                    [ AsCategoryOfRowsMorphism( rows, matrix_2 ), 2 ],
                    [ AsCategoryOfRowsMorphism( rows, matrix_3 ), 3 ],
                    [ AsCategoryOfRowsMorphism( rows, matrix_4 ), 4 ],
                    [ AsCategoryOfRowsMorphism( rows, matrix_5 ), 5 ] ];;

mor := MorphismConstructor( coproduct,
                            source,
                            [ morphism_pairs[1],
                              morphism_pairs[2],
                              morphism_pairs[3],
                              morphism_pairs[5] ],
                            target );
#! <A morphism in ⊕ ( CategoryOfRows( Q ), 5 )>

IsWellDefinedForMorphisms( mor );
#! true

matrices := [ matrix_1, matrix_2, matrix_3, matrix_4, matrix_5 ];;
mor_lift := matrices / coproduct;;

IsEqualForObjects( Source( mor ), Source( mor_lift ) );
#! false
IsEqualForObjects( Target( mor ), Target( mor_lift ) );
#! false
ListOfPairsOfMorphismAndIndex( mor ) = ListOfPairsOfMorphismAndIndex( mor_lift );
#! true

#! @EndExample

#! @EndChunk
