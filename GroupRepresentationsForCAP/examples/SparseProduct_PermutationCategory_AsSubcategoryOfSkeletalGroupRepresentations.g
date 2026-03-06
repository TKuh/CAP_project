#! @Chapter Skeletal Category of group representations
#! @Section Examples and Tests

#! @Example
LoadPackage( "GroupRepresentationsForCAP", false );
#! true

S4 := SymmetricGroup( 4 );;
character_table := CharacterTable( S4 );;
irreducible_characters := Irr( character_table );;

product_permcat := SparseProductOfPermutationCategoryAsSubcategoryOfSkeletalGroupRepresentations( irreducible_characters : no_precompiled_code := true );;

QQ := HomalgFieldOfRationalsInSingular();;
sgreps := SkeletalCategoryOfGroupRepresentations( S4, QQ : no_precompiled_code := true );;

o1 := ObjectConstructor( product_permcat, [ 4, [ 1, 2, 3, 5 ], [ 1, 4, 2, 1 ] ] );;
o2 := ObjectConstructor( product_permcat, [ 2, [ 1, 4 ], [ 3, 4 ] ] );;
# o1o2 := TensorProductOnObjects( o1, o2 );;
# o2o1 := TensorProductOnObjects( o2, o1 );;
# Display( o1o2 );
# [ 5, [ 1 .. 5 ], [ 19, 28, 22, 40, 3 ] ]
# Display( o2o1 );
# [ 5, [ 1 .. 5 ], [ 19, 28, 22, 40, 3 ] ]

morphism_1 := ();;
morphism_2 := (4,2,1,3);;
morphism_3 := (2,1);;
morphism_5 := ();;
triple := [ 4, [ 1, 2, 3, 5 ], [ morphism_1, morphism_2, morphism_3, morphism_5 ] ];;

mor := MorphismConstructor( product_permcat, o1, triple, o1 );;

id_o2 := IdentityMorphism( o2 );;

##############################################
## Functors
##############################################

o1_sgreps := ObjectConstructor( sgreps, [ 4, [ 1, 2, 3, 5 ], [ 1, 4, 2, 1 ] ] );;
o1_sgreps = EmbeddingProductCatOfPermutationCatIntoSGRepsOnObject( sgreps, o1 );
#! true

o2_sgreps := ObjectConstructor( sgreps, [ 2, [ 1, 4 ], [ 3, 4 ] ] );;
o2_sgreps = EmbeddingProductCatOfPermutationCatIntoSGRepsOnObject( sgreps, o2 );
#! true

matrix_1 := HomalgMatrix( PermutationMat( Inverse( morphism_1 ), 1 ), 1, 1, QQ );;
matrix_2 := HomalgMatrix( PermutationMat( Inverse( morphism_2 ), 4 ), 4, 4, QQ );;
matrix_3 := HomalgMatrix( PermutationMat( Inverse( morphism_3 ), 2 ), 2, 2, QQ );;
matrix_5 := HomalgMatrix( PermutationMat( Inverse( morphism_1 ), 1 ), 1, 1, QQ );;

triple := [ 4, [ 1, 2, 3, 5 ], [ matrix_1, matrix_2, matrix_3, matrix_5 ] ];;
mor_sgreps := MorphismConstructor( sgreps, o1_sgreps, triple, o1_sgreps );;
mor_sgreps = EmbeddingProductCatOfPermutationCatIntoSGRepsOnMorphism( sgreps, mor );
#! true

#! @EndExample
