#! @Chapter Coproducts of CategoryOfRows with sparse datastructure
#! @Section Examples and Tests

#! @Example
LoadPackage( "RingsForHomalg", false );
#! true
LoadPackage( "LinearClosuresForCAP", false );
#! true

QQ := HomalgFieldOfRationals();;

rows := CategoryOfRows( QQ );;

coproduct := CoproductOfCategoryOfRowsWithSparseDatastructure( rows, 5 );;

Display( coproduct );
#! A CAP category with name ⊕ ( CategoryOfRows( Q ), 5 ):
#! 
#! 27 primitive operations were used to derive 151 operations for this category w\
#! hich algorithmically
#! * IsLinearCategoryOverCommutativeRing
#! * IsAdditiveCategory
#! and not yet algorithmically
#! * IsAbelianCategory
#! and furthermore mathematically
#! * IsSkeletalCategory

#########################################
# Reinterpretation of objects
#########################################

o2 := CategoryOfRowsObject( rows, 2 );;
o3 := CategoryOfRowsObject( rows, 3 );;
o5 := CategoryOfRowsObject( rows, 5 );;

obj := ObjectConstructor( coproduct, [ [o2,2], [o3,3], [o5,5] ] );
#! <An object in ⊕ ( CategoryOfRows( Q ), 5 )>
Display( obj );
#! [ [ A row module over Q of rank 2, 2 ], [ A row module over Q of rank 3, 3 ], [ A row module over Q of rank 5, 5 ] ]
IsWellDefinedForObjects( obj );
#! true

obj_model := ModelingObject( coproduct, obj );
#! <An object in AdditiveClosureOfObjectFiniteDisconnectedCategory( LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 5 ] ) ) ) defined by 10 underlying objects>

IsWellDefinedForObjects( obj_model );
#! true

obj_reinterp := ReinterpretationOfObject( coproduct, obj_model );;
obj = obj_reinterp;
#! true

obj_model := ModelingTowerObjectConstructor( coproduct, ListOfPairsOfObjectAndIndex( obj ) );;
obj := ReinterpretationOfObject( coproduct, obj_model );;
obj_model = ModelingObject( coproduct, obj );
#! true

#########################################
# Reinterpretation of Morphisms
#########################################

# Reinterpretation -> Model -> Reinterpretation

s2 := CategoryOfRowsObject( rows, 2 );;
s3 := CategoryOfRowsObject( rows, 1 );;
s5 := CategoryOfRowsObject( rows, 1 );;

source := ObjectConstructor( coproduct, [ [s2,2], [s3,3], [s5,5] ] );;

t1 := CategoryOfRowsObject( rows, 3 );;
t2 := CategoryOfRowsObject( rows, 1 );;
t3 := CategoryOfRowsObject( rows, 2 );;

target := ObjectConstructor( coproduct, [ [t1,1], [t2,2], [t3,3] ] );;

matrix_1 := HomalgMatrix( [ ], 0, 3, QQ );;
matrix_2 := HomalgMatrix( [ [ 4 ], [ 1 ] ], 2, 1, QQ );;
matrix_3 := HomalgMatrix( [ [ 5, 6 ] ], 1, 2, QQ );;
matrix_4 := HomalgMatrix( [ ], 0, 0, QQ );;
matrix_5 := HomalgMatrix( [ ], 1, 0, QQ );;
morphism_pairs := [ [ AsCategoryOfRowsMorphism( rows, matrix_2 ), 2 ],
                    [ AsCategoryOfRowsMorphism( rows, matrix_3 ), 3 ] ];;

mor := MorphismConstructor( coproduct, source, morphism_pairs, target );;
IsWellDefinedForMorphisms( mor );
#! true
Display( mor );
#! Index 2: a 2 x 1 morphism in Rows( Q )
#! 
#! [1,1]: 4
#! [2,1]: 1
#! 
#! Index 3: a 1 x 2 morphism in Rows( Q )
#! 
#! [1,1]: 5
#! [1,2]: 6
#! 

mor_model := ModelingMorphism( coproduct, mor );;
mor_reinterp := ReinterpretationOfMorphism( coproduct, source, mor_model, target );;
IsWellDefinedForMorphisms( mor_model );
#! true
IsWellDefinedForMorphisms( mor_reinterp );
#! true
mor = mor_reinterp;
#! true

# Model -> Reinterpretation -> Model

source_model := ModelingTowerObjectConstructor( coproduct, ListOfPairsOfObjectAndIndex( source ) );;
target_model := ModelingTowerObjectConstructor( coproduct, ListOfPairsOfObjectAndIndex( target ) );;
IsWellDefinedForObjects( ModelingCategory( coproduct ), source_model );
#! true
IsWellDefinedForObjects( ModelingCategory( coproduct ), target_model );
#! true

mor_model := ModelingTowerMorphismConstructor( coproduct, source_model, morphism_pairs, target_model );;
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

kernel_obj := KernelObject( mor );;
kernel_emb := KernelEmbeddingWithGivenKernelObject( mor, kernel_obj );;
precomp := PreCompose( kernel_emb, mor );;
IsZeroForMorphisms( precomp );
#! true

cokernel_obj := CokernelObject( mor );;
cokernel_proj := CokernelProjectionWithGivenCokernelObject( mor, cokernel_obj );;
precomp := PreCompose( mor, cokernel_proj );;
IsZeroForMorphisms( precomp );
#! true

#########################################
# Operations
#########################################

source[1];
#! <A row module over Q of rank 0>
source[2];
#! <A row module over Q of rank 2>
Display( mor[1] );
#! Source: 
#! A row module over Q of rank 0
#! 
#! Matrix: 
#! (an empty 0 x 3 matrix)
#! 
#! Range: 
#! A row module over Q of rank 3
#! 
#! A zero, split monomorphism in Rows( Q )
Display( mor[2] );
#! Source: 
#! A row module over Q of rank 2
#! 
#! Matrix: 
#! [ [  4 ],
#!   [  1 ] ]
#! 
#! Range: 
#! A row module over Q of rank 1
#! 
#! A morphism in Rows( Q )

#! @EndExample
