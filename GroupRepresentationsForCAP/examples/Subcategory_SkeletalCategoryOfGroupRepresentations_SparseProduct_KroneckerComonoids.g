#! @Chapter Skeletal Category of group representations
#! @Section Examples and Tests

#! @Example
LoadPackage( "GroupRepresentationsForCAP", false );
#! true

S4 := SymmetricGroup( 4 );;
character_table := CharacterTable( S4 );;
irreducible_characters := Irr( character_table );;
Q := HomalgFieldOfRationals();;
rows := CategoryOfRows( Q );;

sgreps := SkeletalCategoryOfGroupRepresentations( S4, Q : no_precompiled_code := true );;

product_kron_comon := SubcategoryOfSparseProductOfKroneckerComonoids( sgreps );;

modeling := ModelingCategory( product_kron_comon );;

kron_comon := UnderlyingCartesianCategory( modeling );;

product_permcat := UnderlyingProductCategoryOfPermutationCategory( product_kron_comon );;

F_product_perms := IsomorphismFromCoreToProductCategoryOfPermutationCategory( product_kron_comon );;

F_rows := EmbeddingOfKroneckerComonoidsIntoCategoryOfRows( kron_comon, rows );;

Display( product_kron_comon );
#! A CAP category with name 𝚷( 5, KroneckerComonoids ):
#! 
#! 18 primitive operations were used to derive 52 operations for this categor\
#! y which mathematically
#! * IsSkeletalCategory

terminal := ObjectConstructor( product_kron_comon, [ 0, [ ], [ ] ] );;
Display( terminal );
#! [ 0, [  ], [  ] ]

one := ObjectConstructor( product_kron_comon, [ 1, [ 1 ], [ 1 ] ] );;
Display( one );
#! [ 1, [ 1 ], [ 1 ] ]

#########################################
# Reinterpretation of objects
#########################################

source := ObjectConstructor( product_kron_comon, [ 2, [ 1, 3 ], [ 1, 5 ] ] );;
IsWellDefinedForObjects( source );
#! true
Display( source );
#! [ 2, [ 1, 3 ], [ 1, 5 ] ]

source_model := ModelingObject( product_kron_comon, source );;
IsWellDefinedForObjects( source_model );
#! true

source = ReinterpretationOfObject( product_kron_comon, source_model );
#! true

source_model := ModelingTowerObjectConstructor( product_kron_comon, [ 2, [ 1, 3 ], [ 1, 5 ] ] );;
IsWellDefinedForObjects( source_model );
#! true

source := ReinterpretationOfObject( product_kron_comon, source_model );;
IsWellDefinedForObjects( source );
#! true

source_model = ModelingObject( product_kron_comon, source );
#! true

#########################################
# Reinterpretation of Morphisms
#########################################

# Reinterpretation -> Model -> Reinterpretation

source := ObjectConstructor( product_kron_comon, [ 4, [ 1, 2, 3, 5 ], [ 1, 4, 1, 1 ] ] );;
target := ObjectConstructor( product_kron_comon, [ 2, [    2, 3    ], [    5, 2     ] ] );;

morphism_1 := [ 0, [] ];;
morphism_2 := [ 2, [ [1,3], [3,4] ] ];;
morphism_3 := [ 2, [ [1,1], [1,1] ] ];;
morphism_4 := [ 0, [] ];;
morphism_5 := [ 0, [] ];;
triple := [ 4, [ 1, 2, 3, 5 ], [ morphism_1, morphism_2, morphism_3, morphism_5 ] ];;

mor := MorphismConstructor( product_kron_comon, source, triple, target );;
IsWellDefinedForMorphisms( mor );
#! true

mor_model := ModelingMorphism( product_kron_comon, mor );;
mor_reiterp := ReinterpretationOfMorphism( product_kron_comon, source, mor_model, target );;
IsWellDefinedForMorphisms( mor_model );
#! true
IsWellDefinedForMorphisms( mor_reiterp );
#! true
mor = mor_reiterp;
#! true

# Model -> Reinterpretation -> Model

o1 := ObjectConstructor( kron_comon, 1 );;
o2 := ObjectConstructor( kron_comon, 2 );;
o3 := ObjectConstructor( kron_comon, 3 );;
o4 := ObjectConstructor( kron_comon, 4 );;
o5 := ObjectConstructor( kron_comon, 5 );;

source_model := ModelingTowerObjectConstructor( product_kron_comon, [ 4, [ 1, 2, 3, 5 ], [ 1, 4, 1, 1 ] ] );;
target_model := ModelingTowerObjectConstructor( product_kron_comon, [ 2, [    2, 3    ], [    5, 2     ] ] );;

IsWellDefinedForObjects( ModelingCategory( product_kron_comon ), source_model );
#! true
IsWellDefinedForObjects( ModelingCategory( product_kron_comon ), target_model );
#! true

mor_model := ModelingTowerMorphismConstructor( product_kron_comon, source_model, triple, target_model );;
mor_product_kron_comon := ReinterpretationOfMorphism( product_kron_comon, source, mor_model, target );;
IsWellDefinedForMorphisms( mor_product_kron_comon );
#! true
IsWellDefinedForMorphisms( mor_model );
#! true
mor_model = ModelingMorphism( product_kron_comon, mor_product_kron_comon );
#! true

#########################################
# IdentityMorphism
#########################################

object := ObjectConstructor( product_kron_comon, [ 2, [ 1, 3 ], [ 1, 5 ] ] );;
id_object := IdentityMorphism( object );;
Display( id_object );
#! Component: (1)
#! 
#! [ 1, [ [ 1, 1 ] ] ]
#! 
#! ------------------------
#! Component: (3)
#! 
#! [ 1, [ [ 1, 5 ] ] ]
#! 
#! ------------------------

#########################################
# TensorProductOnObjects
#########################################

tp := TensorProductOnObjects( source, target );;
Display( tp );
#! [ 5, [ 1 .. 5 ], [ 2, 38, 26, 38, 22 ] ]

#########################################
# TensorProductOnMorphisms
#########################################

source := ObjectConstructor( product_kron_comon, [ 4, [ 1, 2, 3, 5 ], [ 1, 2, 1, 1 ] ] );;
target := ObjectConstructor( product_kron_comon, [ 2, [    2, 3    ], [    1, 2    ] ] );;

matrix_1 := [ 0, [] ];;
matrix_2 := [ 1, [ [ 1, 1 ] ] ];;
matrix_3 := [ 2, [ [ 1, 1 ], [ 1, 1 ] ] ];;
matrix_4 := [ 0, [] ];;
matrix_5 := [ 0, [] ];;
matrices_triple := [ 4, [ 1, 2, 3, 5 ], [ matrix_1, matrix_2, matrix_3, matrix_5 ] ];;

mor := MorphismConstructor( product_kron_comon, source, matrices_triple, target );;
IsWellDefinedForMorphisms( mor );
#! true

# Display( ApplyFunctor( F_rows, ModelingMorphism( product_kron_comon, mor )[2] ) );
# Display( ApplyFunctor( F_rows, ModelingMorphism( product_kron_comon, mor )[3] ) );

tp_mor := TensorProductOnMorphisms( mor, mor );
Display( tp_mor );
#! Component: (1)
#! 
#! [ 4, [ [ 2, 2 ], [ 2, 2 ], [ 2, 2 ], [ 2, 2 ] ] ]
#! 
#! ------------------------
#! Component: (2)
#! 
#! [ 5, [ [ 1, 1 ], [ 5, 5 ], [ 5, 5 ], [ 9, 9 ], [ 9, 9 ] ] ]
#! 
#! ------------------------
#! Component: (3)
#! 
#! [ 5, [ [ 2, 2 ], [ 7, 7 ], [ 7, 7 ], [ 7, 7 ], [ 7, 7 ] ] ]
#! 
#! ------------------------
#! Component: (4)
#! 
#! [ 5, [ [ 5, 5 ], [ 9, 9 ], [ 9, 9 ], [ 11, 11 ], [ 11, 11 ] ] ]
#! 
#! ------------------------
#! Component: (5)
#! 
#! [ 5, [ [ 2, 2 ], [ 6, 6 ], [ 6, 6 ], [ 6, 6 ], [ 6, 6 ] ] ]
#! 
#! ------------------------

##############################################
## TensorProductOfMorphismWithIdentity
##############################################

source_tp := TensorProductOnObjects( source, object );;
target_tp := TensorProductOnObjects( target, object );;

mor_id_object := PRODUCT_OF_CATEGORY_OF_INSERTION_MATRICES_AS_SUBCAT_TensorProductOfMorphismWithIdentityWithGivenTensorProducts(
    product_kron_comon, source_tp, mor, id_object, target_tp );;

IsEqualForMorphisms( mor_id_object, TensorProductOnMorphisms( mor, id_object ) );
#! true

test_source := ObjectConstructor( product_kron_comon, [ 2, [ 3, 4 ], [ 3, 1 ] ] );
test_target := ObjectConstructor( product_kron_comon, [ 2, [ 3, 4 ], [ 3, 1 ] ] );
c := ObjectConstructor( product_kron_comon, [ 2, [ 1, 4 ], [ 1, 2 ] ] );;

test_morphism_1 := [ 0, [] ];;
test_morphism_2 := [ 0, [] ];;
test_morphism_3 := [ 3, [ [ 1, 1 ], [ 2, 2 ], [ 3, 3 ] ] ];;
test_morphism_4 := [ 1, [ [ 1, 1 ] ] ];;
test_morphism_5 := [ 0, [] ];;
triple := [ 2, [ 3, 4 ], [ test_morphism_3, test_morphism_4 ] ];;

test_morphism := MorphismConstructor( product_kron_comon, test_source, triple, test_target );;
id_c := IdentityMorphism( c );;

IsWellDefinedForMorphisms( test_morphism );
#! true
IsWellDefinedForMorphisms( id_c );
#! true

source_tp := ObjectConstructor( product_kron_comon, [ 4, [ 2, 3, 4, 5 ], [ 9, 5, 8, 2 ] ] );;
target_tp := ObjectConstructor( product_kron_comon, [ 4, [ 2, 3, 4, 5 ], [ 9, 5, 8, 2 ] ] );;

test_morphism_id_c := PRODUCT_OF_CATEGORY_OF_INSERTION_MATRICES_AS_SUBCAT_TensorProductOfMorphismWithIdentityWithGivenTensorProducts(
    product_kron_comon, source_tp, test_morphism, id_c, target_tp );;

IsEqualForMorphisms( test_morphism_id_c, TensorProductOnMorphisms( test_morphism, id_c ) );
#! true

##############################################
## TensorProductOfIdentityWithMorphism
##############################################

source_tp := TensorProductOnObjects( object, source );;
target_tp := TensorProductOnObjects( object, target );;

id_object_mor := PRODUCT_OF_CATEGORY_OF_INSERTION_MATRICES_AS_SUBCAT_TensorProductOfIdentityWithMorphismWithGivenTensorProducts(
    product_kron_comon, source_tp, id_object, mor, target_tp );;

IsEqualForMorphisms( id_object_mor, TensorProductOnMorphisms( id_object, mor ) );
#! true

test_source := ObjectConstructor( product_kron_comon, [ 2, [ 3, 4 ], [ 3, 1 ] ] );
test_target := ObjectConstructor( product_kron_comon, [ 2, [ 3, 4 ], [ 3, 1 ] ] );
c := ObjectConstructor( product_kron_comon, [ 2, [ 1, 4 ], [ 1, 2 ] ] );;

test_morphism_1 := [ 0, [] ];;
test_morphism_2 := [ 0, [] ];;
test_morphism_3 := [ 3, [ [ 1, 1 ], [ 2, 2 ], [ 3, 3 ] ] ];;
test_morphism_4 := [ 1, [ [ 1, 1 ] ] ];;
test_morphism_5 := [ 0, [] ];;
triple := [ 2, [ 3, 4 ], [ test_morphism_3, test_morphism_4 ] ];;

test_morphism := MorphismConstructor( product_kron_comon, test_source, triple, test_target );;
id_c := IdentityMorphism( c );;

IsWellDefinedForMorphisms( test_morphism );
#! true
IsWellDefinedForMorphisms( id_c );
#! true

source_tp := ObjectConstructor( product_kron_comon, [ 4, [ 2, 3, 4, 5 ], [ 9, 5, 8, 2 ] ] );;
target_tp := ObjectConstructor( product_kron_comon, [ 4, [ 2, 3, 4, 5 ], [ 9, 5, 8, 2 ] ] );;

id_c_test_morphism := PRODUCT_OF_CATEGORY_OF_INSERTION_MATRICES_AS_SUBCAT_TensorProductOfIdentityWithMorphismWithGivenTensorProducts(
    product_kron_comon, source_tp, id_c, test_morphism, target_tp );;

IsEqualForMorphisms( id_c_test_morphism, TensorProductOnMorphisms( id_c, test_morphism ) );
#! true

#################################################################
# LeftDistributivityExpandingWithGivenMultiplicitiesAndObjects
#################################################################

a := ObjectConstructor( product_kron_comon, [ 2, [1,4], [4,2] ] );;
b := ObjectConstructor( product_kron_comon, [ 3, [2,3,5], [6,2,10] ] );;
ab := TensorProductOnObjects( a, b );;
L := DecompositionIntoSimpleObjects( b );;

a_sgreps := ObjectConstructor( sgreps, ObjectDatum( a ) );;
L_sgreps := List( L, o -> ObjectConstructor( sgreps, ObjectDatum( o ) ) );;
SGREPS_LeftDistributivityExpandingPermutation( sgreps,
    a_sgreps,
    L_sgreps,
    TensorProductOnObjects( a_sgreps, DirectSum( L_sgreps ) ) );;
# time;
# 7

b1 := ObjectConstructor( product_kron_comon, [ 1, [2], [1] ] );;
b2 := ObjectConstructor( product_kron_comon, [ 1, [3], [1] ] );;
b3 := ObjectConstructor( product_kron_comon, [ 1, [5], [1] ] );;
left_expanding_with_mults := LeftDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_kron_comon, ab, a, [ b1, b2, b3 ], [ 6, 2, 10 ], ab );;
# time;
# 58
left_expanding_prod_perms := ApplyFunctor( F_product_perms, left_expanding_with_mults );;
# time
# 4

left_expanding := LeftDistributivityExpandingWithGivenObjects( ab, a, L, ab );;
# time;
# 392

# IsCongruentForMorphisms( left_expanding, left_expanding_with_mults );
# true

# a := ObjectConstructor( product_kron_comon, [ 4, [1,2,3,4], [30,40,90,50] ] );;
# b := ObjectConstructor( product_kron_comon, [ 3, [2,3,5], [30,10,50] ] );;
# c := ObjectConstructor( product_kron_comon, [ 3, [1,3,4], [24,83,29] ] );;
# d := ObjectConstructor( product_kron_comon, [ 4, [1,3,4,5], [26,37,50,103] ] );;
# e := ObjectConstructor( product_kron_comon, [ 4, [1,2,3,4], [20,76,25,13] ] );;
# f := ObjectConstructor( product_kron_comon, [ 4, [1,2,3,4], [45,61,25,35] ] );;
# L := [ 
#        b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, 
#        c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, 
#        d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d,
#        e, e, e, e, e, e, e, e, e, e, e, e, e, e, e, e, e, e, e, e,
#        f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f,
#        ];;

# a_sgreps := ObjectConstructor( sgreps, ObjectDatum( a ) );;
# L_sgreps := List( L, o -> ObjectConstructor( sgreps, ObjectDatum( o ) ) );;
# SGREPS_LeftDistributivityExpandingPermutation( sgreps,
#     a_sgreps,
#     L_sgreps,
#     TensorProductOnObjects( a_sgreps, DirectSum( L_sgreps ) ) );;
# time;
# 4112

# a_product_L := TensorProductOnObjects( a, DirectProduct( L ) );;
# left_expanding_with_mults := LeftDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_kron_comon,
#                                     a_product_L,
#                                     a,
#                                     [ b, c, d, e, f ],
#                                     [ 64, 24, 80, 20, 40 ],
#                                     a_product_L );;
# time;
# 1659
# left_expanding_prod_perms := ApplyFunctor( F_product_perms, left_expanding_with_mults );;
# time;
# 659

# left_expanding := LeftDistributivityExpandingWithGivenObjects( L_product_a, a, L, a_product_L );;
# time;
# 102833

# Takes too long
# IsCongruentForMorphisms( left_expanding, left_expanding_with_mults );
# true

#################################################################
# RightDistributivityExpandingWithGivenMultiplicitiesAndObjects
#################################################################

# Test multiplicities with simple objects.

a := ObjectConstructor( product_kron_comon, [ 2, [1,4], [4,2] ] );;
b := ObjectConstructor( product_kron_comon, [ 3, [2,3,5], [6,2,10] ] );;
ba := TensorProductOnObjects( b, a );;
L := DecompositionIntoSimpleObjects( b );;

a_sgreps := ObjectConstructor( sgreps, ObjectDatum( a ) );;
L_sgreps := List( L, o -> ObjectConstructor( sgreps, ObjectDatum( o ) ) );;
SGREPS_RightDistributivityExpandingPermutation( sgreps,
    L_sgreps,
    a_sgreps,
    TensorProductOnObjects( DirectSum( L_sgreps ), a_sgreps ) );;
# time;
# 6

b1 := ObjectConstructor( product_kron_comon, [ 1, [2], [1] ] );;
b2 := ObjectConstructor( product_kron_comon, [ 1, [3], [1] ] );;
b3 := ObjectConstructor( product_kron_comon, [ 1, [5], [1] ] );;
right_expanding_with_mults := RightDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_kron_comon, ba, [ b1, b2, b3 ], a, [ 6, 2, 10 ], ba );;
# time;
# 66

right_expanding := RightDistributivityExpandingWithGivenObjects( ba, L, a, ba );;
# time;
# 293

IsCongruentForMorphisms( right_expanding, right_expanding_with_mults );
#! true

a := ObjectConstructor( product_kron_comon, [ 3, [1,2,4], [40,25,30] ] );;
b := ObjectConstructor( product_kron_comon, [ 3, [2,3,5], [60,29,105] ] );;
ba := TensorProductOnObjects( b, a );;
L := DecompositionIntoSimpleObjects( b );;

a_sgreps := ObjectConstructor( sgreps, ObjectDatum( a ) );;
L_sgreps := List( L, o -> ObjectConstructor( sgreps, ObjectDatum( o ) ) );;
SGREPS_RightDistributivityExpandingPermutation( sgreps,
    L_sgreps,
    a_sgreps,
    TensorProductOnObjects( DirectSum( L_sgreps ), a_sgreps ) );;
# time;
# 236

b1 := ObjectConstructor( product_kron_comon, [ 1, [2], [1] ] );;
b2 := ObjectConstructor( product_kron_comon, [ 1, [3], [1] ] );;
b3 := ObjectConstructor( product_kron_comon, [ 1, [5], [1] ] );;
right_expanding_with_mults := RightDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_kron_comon, ba, [ b1, b2, b3 ], a, [ 60, 29, 105 ], ba );;
# time;
# 976

# right_expanding := RightDistributivityExpandingWithGivenObjects( ba, L, a, ba );;
# time;
# 21318

# IsCongruentForMorphisms( right_expanding, right_expanding_with_mults );
# true

# Test multiplicities with non-simple objects.

# a := ObjectConstructor( product_kron_comon, [ 4, [1,2,3,4], [30,40,90,50] ] );;
# b := ObjectConstructor( product_kron_comon, [ 3, [2,3,5], [30,10,50] ] );;
# c := ObjectConstructor( product_kron_comon, [ 3, [1,3,4], [24,83,29] ] );;
# d := ObjectConstructor( product_kron_comon, [ 4, [1,3,4,5], [26,37,50,103] ] );;
# e := ObjectConstructor( product_kron_comon, [ 4, [1,2,3,4], [20,76,25,13] ] );;
# f := ObjectConstructor( product_kron_comon, [ 4, [1,2,3,4], [45,61,25,35] ] );;
# L := [ 
#        b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, b, 
#        c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, c, 
#        d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d, d,
#        e, e, e, e, e, e, e, e, e, e, e, e, e, e, e, e, e, e, e, e,
#        f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f, f,
#        ];;

# a_sgreps := ObjectConstructor( sgreps, ObjectDatum( a ) );;
# L_sgreps := List( L, o -> ObjectConstructor( sgreps, ObjectDatum( o ) ) );;
# SGREPS_RightDistributivityExpandingPermutation( sgreps,
#     L_sgreps,
#     a_sgreps,
#     TensorProductOnObjects( DirectSum( L_sgreps ), a_sgreps ) );;
# time;
# 3148

# L_product_a := TensorProductOnObjects( DirectProduct( L ), a );;
# right_expanding_with_mults := RightDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_kron_comon,
#                                     L_product_a,
#                                     [ b, c, d, e, f ],
#                                     a,
#                                     [ 64, 24, 80, 20, 40 ],
#                                     L_product_a );;
# time;
# 1593
# right_expanding_prod_perms := ApplyFunctor( F_product_perms, right_expanding_with_mults );;
# time;
# 890

# right_expanding := RightDistributivityExpandingWithGivenObjects( L_product_a, L, a, L_product_a );;
# time;
# 102833

# Takes too long:
# IsCongruentForMorphisms( right_expanding, right_expanding_with_mults );
# true

#########################################
# Functors
#########################################

object := ObjectConstructor( product_kron_comon, [ 4, [ 1, 2, 3, 5 ], [ 1, 2, 4, 3 ] ] );;
object_perm := ApplyFunctor( F_product_perms, object );;
Display( object_perm );
#! [ 4, [ 1, 2, 3, 5 ], [ 1, 2, 4, 3 ] ]
ObjectDatum( object_perm ) = ObjectDatum( object );
#! true

matrix_1 := [ 1, [ [ 1, 1 ] ] ];;
matrix_2 := [ 1, [ [ 1, 2 ] ] ];;
matrix_3 := [ 3, [ [ 2, 3 ], [ 1, 1 ], [ 4, 4 ] ] ];;
matrix_4 := [ 0, [] ];;
matrix_5 := [ 2, [ [ 3,3 ],[ 1,2 ] ] ];;
matrices_triple := [ 4, [ 1, 2, 3, 5 ], [ matrix_1, matrix_2, matrix_3, matrix_5 ] ];;

mor := MorphismConstructor( product_kron_comon, object, matrices_triple, object );;
IsWellDefinedForMorphisms( mor );
#! true
mor_perm := ApplyFunctor( F_product_perms, mor );;
Display( mor_perm );
#! Component: (1)
#! 
#! 1 ⱶ()→ 1
#! ------------------------
#! Component: (2)
#! 
#! 2 ⱶ()→ 2
#! ------------------------
#! Component: (3)
#! 
#! 4 ⱶ(1,2,3)→ 4
#! ------------------------
#! Component: (5)
#! 
#! 3 ⱶ(1,3,2)→ 3
#! ------------------------

#! @EndExample
