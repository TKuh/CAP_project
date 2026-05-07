#! @Chapter Skeletal Category of group representations
#! @Section Examples and Tests

#! @Example
LoadPackage( "GroupRepresentationsForCAP", false );
#! true

QQ := HomalgFieldOfRationalsInSingular();;
S4 := SymmetricGroup( 4 );;
SGReps := SkeletalCategoryOfGroupRepresentations( S4, QQ : no_precompiled_code := false );;
product_kron_comon := SubcategoryOfSparseProductOfKroneckerComonoids( SGReps );;

#########################################
# Functors on objects
#########################################

A := ObjectConstructor( SGReps, [ 2, [1,4], [1,2] ] );;
B := ObjectConstructor( SGReps, [ 2, [2,3], [1,3] ] );;
C := ObjectConstructor( SGReps, [ 3, [2,4,5], [2,3,5] ] );;

A_product_kron_comon := AsObjectInSubcategoryOfSparseProductOfKroneckerComonoids( product_kron_comon, A );;
IsWellDefined( A_product_kron_comon );
#! true

A := FunctorProdInsMatIntoSGRepsOnObject( SGReps, A_product_kron_comon );;
IsWellDefined( A );
#! true

Component( A, 1 );
#! 1
Component( A, 2 );
#! 0
Component( A, 3 );
#! 0
Component( A, 4 );
#! 2
Component( A, 5 );
#! 0

#########################################
# Functors on morphism
#########################################

source := ObjectConstructor( product_kron_comon, [ 4, [ 1, 2, 3, 5 ], [ 1, 4, 1, 1 ] ] );;
target := ObjectConstructor( product_kron_comon, [ 2, [    2, 3    ], [    5, 2     ] ] );;

morphism_1 := [ ];;
morphism_2 := [ [1,3], [3,4] ];;
morphism_3 := [ [1,1], [1,1] ];;
morphism_4 := [ ];;
morphism_5 := [ ];;
triple := [ 4, [ 1, 2, 3, 5 ], [ morphism_1, morphism_2, morphism_3, morphism_5 ] ];;

mor := MorphismConstructor( product_kron_comon, source, triple, target );;
IsWellDefinedForMorphisms( mor );
#! true

Component( mor, 1 );;
Component( mor, 2 );;
Component( mor, 3 );;
Component( mor, 4 );;
Component( mor, 5 );;

mor_embedded := FunctorProdInsMatIntoSGRepsUsingUnionOfCols( SGReps, mor );;
Display( mor_embedded );
#! Component: (1)
#! 
#! (an empty 1 x 0 matrix)
#! 
#! ------------------------
#! Component: (2)
#! 
#! 1,0,0,0,0,
#! 0,1,0,0,0,
#! 0,0,1,1,0,
#! 0,0,0,0,1 
#! 
#! ------------------------
#! Component: (3)
#! 
#! 1,1
#! 
#! ------------------------
#! Component: (5)
#! 
#! (an empty 1 x 0 matrix)
#! 
#! ------------------------

source := ObjectConstructor( product_kron_comon, [ 4, [ 1, 2, 3, 5 ], [ 1, 2, 1, 1 ] ] );;
target := ObjectConstructor( product_kron_comon, [ 2, [    2, 3    ], [    1, 2    ] ] );;

matrix_1 := [ ];;
matrix_2 := [ [ 1, 1 ] ];;
matrix_3 := [ [ 1, 1 ], [ 1, 1 ] ] ];;
matrix_4 := [ ];;
matrix_5 := [ ];;
matrices_triple := [ 4, [ 1, 2, 3, 5 ], [ matrix_1, matrix_2, matrix_3, matrix_5 ] ];;

mor := MorphismConstructor( product_kron_comon, source, matrices_triple, target );;
IsWellDefinedForMorphisms( mor );
#! true

mor_embedded := FunctorProdInsMatIntoSGRepsUsingUnionOfCols( SGReps, mor );;
Display( mor_embedded );
#! Component: (1)
#! 
#! (an empty 1 x 0 matrix)
#! 
#! ------------------------
#! Component: (2)
#! 
#! 1,
#! 0 
#! 
#! ------------------------
#! Component: (3)
#! 
#! 1,1
#! 
#! ------------------------
#! Component: (5)
#! 
#! (an empty 1 x 0 matrix)
#! 
#! ------------------------

#! @EndExample
