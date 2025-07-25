#! @BeginChunk CoproductCategoryOfRows_constructors

#! @Example
LoadPackage( "RingsForHomalg", false );
#! true
LoadPackage( "LinearClosuresForCAP", false );
#! true

QQ := HomalgFieldOfRationals();;

coproduct := CoproductOfCategoryOfRows( QQ, 5 );;

obj := ObjectConstructor( coproduct, [ 4, [ 0, 2, 1, 0, 1 ] ] );;
IsWellDefinedForObjects( obj );
#! true

source := ObjectConstructor( coproduct, [ 4, [ 0, 2, 1, 0, 1 ] ] );;
target := ObjectConstructor( coproduct, [ 6, [ 3, 1, 2, 0, 0 ] ] );;

matrix_1 := HomalgMatrix( [ ], 0, 3, QQ );;
matrix_2 := HomalgMatrix( [ [ 4 ], [ 1 ] ], 2, 1, QQ );;
matrix_3 := HomalgMatrix( [ [ 5, 6 ] ], 1, 2, QQ );;
matrix_4 := HomalgMatrix( [ ], 0, 0, QQ );;
matrix_5 := HomalgMatrix( [ ], 1, 0, QQ );;
matrices := [ matrix_1,  matrix_2,  matrix_3,  matrix_4,  matrix_5 ];;

mor := MorphismConstructor( coproduct, source, matrices, target );;
IsWellDefinedForMorphisms( mor );
#! true
#! @EndExample

#! @EndChunk
