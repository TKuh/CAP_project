#! @BeginChunk CoproductCategoryOfRows_constructors

#! @Example
LoadPackage( "RingsForHomalg", false );
#! true
LoadPackage( "LinearClosuresForCAP", false );
#! true

QQ := HomalgFieldOfRationals();;

rows := CategoryOfRows( QQ );;

coproduct := CoproductOfCategoryOfRows( rows, 5 );;

obj := [ 0, 2, 1, 0, 1 ] / coproduct;
#! <An object in ⊕ ( CategoryOfRows( Q ), 5 )>
IsWellDefinedForObjects( obj );
#! true

source := [ 0, 2, 1, 0, 1 ] / coproduct;;
target := [ 3, 1, 2, 0, 0 ] / coproduct;;

matrix_1 := HomalgMatrix( [ ], 0, 3, QQ );;
matrix_2 := HomalgMatrix( [ [ 4 ], [ 1 ] ], 2, 1, QQ );;
matrix_3 := HomalgMatrix( [ [ 5, 6 ] ], 1, 2, QQ );;
matrix_4 := HomalgMatrix( [ ], 0, 0, QQ );;
matrix_5 := HomalgMatrix( [ ], 1, 0, QQ );;
matrices := [ matrix_1, matrix_2, matrix_3, matrix_4, matrix_5 ];;

mor := matrices / coproduct;
#! <A morphism in ⊕ ( CategoryOfRows( Q ), 5 )>

IsWellDefinedForMorphisms( mor );
#! true
#! @EndExample

#! @EndChunk
