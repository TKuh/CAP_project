#! @Chapter Coproducts of categories of rows
#! @Section Examples and Tests

#! @Example
LoadPackage( "RingsForHomalg", false );
#! true
LoadPackage( "LinearClosuresForCAP", false );
#! true

QQ := HomalgFieldOfRationals();;

coproduct := CoproductOfCategoryOfRows( QQ, 5 );;

Display( coproduct );
#! A CAP category with name ⊕ ( CategoryOfRows( Q ), 5 ):
#! 
#! 31 primitive operations were used to derive 237 operations for this category wh\
#! ich algorithmically
#! * IsLinearCategoryOverCommutativeRing
#! * IsAbelianCategory
#! and furthermore mathematically
#! * IsSkeletalCategory

#########################################
# Reinterpretation of objects
#########################################

obj := ObjectConstructor( coproduct, [ 4, [ 0, 2, 1, 0, 1 ] ] );;
IsWellDefinedForObjects( obj );
#! true

obj_model := ModelingObject( coproduct, obj );
#! <An object in AdditiveClosureOfObjectFiniteDisconnectedCategory( LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 5 ] ) ) ) defined by 4 underlying objects>

IsWellDefinedForObjects( obj_model );
#! true

obj_reinterp := ReinterpretationOfObject( coproduct, obj_model );;
obj = obj_reinterp;
#! true

obj_model := ModelingTowerObjectConstructor( coproduct, [ 4, [ 0, 2, 1, 0, 1 ] ] );;
obj := ReinterpretationOfObject( coproduct, obj_model );;
obj_model = ModelingObject( coproduct, obj );
#! true

#########################################
# Reinterpretation of Morphisms
#########################################

# Reinterpretation -> Model -> Reinterpretation

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

mor_model := ModelingMorphism( coproduct, mor );;
mor_reiterp := ReinterpretationOfMorphism( coproduct, source, mor_model, target );;
IsWellDefinedForMorphisms( mor_model );
#! true
IsWellDefinedForMorphisms( mor_reiterp );
#! true
mor = mor_reiterp;
#! true

# Model -> Reinterpretation -> Model

source_model := ModelingTowerObjectConstructor( coproduct, [ 4, [ 0, 2, 1, 0, 1 ] ] );;
target_model := ModelingTowerObjectConstructor( coproduct, [ 6, [ 3, 1, 2, 0, 0 ] ] );;
IsWellDefinedForObjects( ModelingCategory( coproduct ), source_model );;
IsWellDefinedForObjects( ModelingCategory( coproduct ), target_model );;

mor_model := ModelingTowerMorphismConstructor( coproduct, source_model, matrices, target_model );;
mor := ReinterpretationOfMorphism( coproduct, source, mor_model, target );;
IsWellDefinedForMorphisms( mor );
#! true
IsWellDefinedForMorphisms( mor_model );
#! true
mor_model = ModelingMorphism( coproduct, mor );
#! true

#########################################
# Primitive operations
#########################################

kernel_emb := KernelEmbedding( mor );;
kernel_obj := KernelObject( mor );;
kernel_emb = KernelEmbeddingWithGivenKernelObject( mor, kernel_obj );;
precomp := PreCompose( kernel_emb, mor );;
IsZeroForMorphisms( precomp );;

cokernel_proj := CokernelProjection( mor );;
cokernel_obj := CokernelObject( mor );;
cokernel_proj = CokernelProjectionWithGivenCokernelObject( mor, cokernel_obj );;
precomp := PreCompose( mor, cokernel_proj );;
IsZeroForMorphisms( precomp );;

id_target := IdentityMorphism( target );;
lift := Lift( mor, id_target );;
IsEqualForMorphisms( mor, PreCompose( lift, id_target ) );;

id_source := IdentityMorphism( source );;
colift := Colift( id_source, mor );;
IsEqualForMorphisms( mor, PreCompose( id_source, colift ) );;

#########################################
# Operations
#########################################

Display( source[2] );
#! 2
Display( mor[2] );
#! [ [  4 ],
#!   [  1 ] ]

#! @EndExample
