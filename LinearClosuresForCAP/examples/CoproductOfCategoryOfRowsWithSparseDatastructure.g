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
#! 27 primitive operations were used to derive 237 operations for this catego\
#! ry w\
#! hich algorithmically
#! * IsLinearCategoryOverCommutativeRing
#! * IsAbelianCategory
#! and furthermore mathematically
#! * IsSkeletalCategory

#########################################
# Primitive operations
#########################################

s2 := CategoryOfRowsObject( rows, 2 );;
s3 := CategoryOfRowsObject( rows, 1 );;
s5 := CategoryOfRowsObject( rows, 1 );;

source := ObjectConstructor( coproduct, [ [s2,2], [s3,3], [s5,5] ] );;

t1 := CategoryOfRowsObject( rows, 3 );;
t2 := CategoryOfRowsObject( rows, 1 );;
t3 := CategoryOfRowsObject( rows, 2 );;

target := ObjectConstructor( coproduct, [ [t1,1], [t2,2], [t3,3] ] );;

matrix_mor1_1 := HomalgMatrix( [ ], 0, 3, QQ );;
matrix_mor1_2 := HomalgMatrix( [ [ 4 ], [ 1 ] ], 2, 1, QQ );;
matrix_mor1_3 := HomalgMatrix( [ [ 5, 6 ] ], 1, 2, QQ );;
matrix_mor1_4 := HomalgMatrix( [ ], 0, 0, QQ );;
matrix_mor1_5 := HomalgMatrix( [ ], 1, 0, QQ );;
morphism_pairs := [ [ AsCategoryOfRowsMorphism( rows, matrix_mor1_1 ), 1 ],
                    [ AsCategoryOfRowsMorphism( rows, matrix_mor1_2 ), 2 ],
                    [ AsCategoryOfRowsMorphism( rows, matrix_mor1_3 ), 3 ],
                    [ AsCategoryOfRowsMorphism( rows, matrix_mor1_5 ), 5 ] ];;

mor1 := MorphismConstructor( coproduct, source, morphism_pairs, target );;
IsWellDefinedForMorphisms( mor1 );
#! true
Display( mor1 );
#! Component 1: a 0 x 3 morphism in Rows( Q )
#! 
#! Component 2: a 2 x 1 morphism in Rows( Q )
#! 
#! [1,1]: 4
#! [2,1]: 1
#! 
#! Component 3: a 1 x 2 morphism in Rows( Q )
#! 
#! [1,1]: 5
#! [1,2]: 6
#! 
#! Component 5: a 1 x 0 morphism in Rows( Q )
#! 

ObjectDatum( coproduct, source );
#! [ [ <A row module over Q of rank 2>, 2 ], 
#!   [ <A row module over Q of rank 1>, 3 ], 
#!   [ <A row module over Q of rank 1>, 5 ] ]

MorphismDatum( coproduct, mor1 );
#! [ [ <A morphism in Rows( Q )>, 1 ], [ <A morphism in Rows( Q )>, 2 ], 
#!   [ <A morphism in Rows( Q )>, 3 ], [ <A morphism in Rows( Q )>, 5 ] ]

IsEqualForObjects( coproduct, source, source );
#! true
IsEqualForObjects( coproduct, target, target );
#! true
IsEqualForObjects( coproduct, source, target );
#! false
IsEqualForObjects( coproduct, target, source );
#! false

matrix_mor2_1 := HomalgMatrix( [ ], 0, 3, QQ );;
matrix_mor2_2 := HomalgMatrix( [ [ -5 ], [ -8 ] ], 2, 1, QQ );;
matrix_mor2_3 := HomalgMatrix( [ [ 20, 30 ] ], 1, 2, QQ );;
matrix_mor2_4 := HomalgMatrix( [ ], 0, 0, QQ );;
matrix_mor2_5 := HomalgMatrix( [ ], 1, 0, QQ );;
morphism_pairs := [ [ AsCategoryOfRowsMorphism( rows, matrix_mor2_1 ), 1 ],
                    [ AsCategoryOfRowsMorphism( rows, matrix_mor2_2 ), 2 ],
                    [ AsCategoryOfRowsMorphism( rows, matrix_mor2_3 ), 3 ],
                    [ AsCategoryOfRowsMorphism( rows, matrix_mor2_5 ), 5 ] ];;

mor2 := MorphismConstructor( coproduct, source, morphism_pairs, target );;

IsEqualForMorphisms( coproduct, mor1, mor1 );
#! true
IsEqualForMorphisms( coproduct, mor2, mor2 );
#! true
IsEqualForMorphisms( coproduct, mor1, mor2 );
#! false
IsEqualForMorphisms( coproduct, mor2, mor1 );
#! false

IsCongruentForMorphisms( coproduct, mor1, mor1 );
#! true
IsCongruentForMorphisms( coproduct, mor2, mor2 );
#! true
IsCongruentForMorphisms( coproduct, mor1, mor2 );
#! false
IsCongruentForMorphisms( coproduct, mor2, mor1 );
#! false

matrix_mor3_1 := HomalgMatrix( [ [], [], [] ], 3, 0, QQ );;
matrix_mor3_2 := HomalgMatrix( [ [ -5, -8 ] ], 1, 2, QQ );;
matrix_mor3_3 := HomalgMatrix( [ [ 20 ], [ 30 ] ], 2, 1, QQ );;
matrix_mor3_4 := HomalgMatrix( [ ], 0, 0, QQ );;
matrix_mor3_5 := HomalgMatrix( [ ], 0, 1, QQ );;
morphism_pairs := [ [ AsCategoryOfRowsMorphism( rows, matrix_mor3_1 ), 1 ],
                    [ AsCategoryOfRowsMorphism( rows, matrix_mor3_2 ), 2 ],
                    [ AsCategoryOfRowsMorphism( rows, matrix_mor3_3 ), 3 ],
                    [ AsCategoryOfRowsMorphism( rows, matrix_mor3_5 ), 5 ] ];;

mor3 := MorphismConstructor( coproduct, target, morphism_pairs, source );;

PreCompose( coproduct, mor1, mor3 );
#! <A morphism in ⊕ ( CategoryOfRows( Q ), 5 )>
PreCompose( coproduct, mor2, mor3 );
#! <A morphism in ⊕ ( CategoryOfRows( Q ), 5 )>
PreCompose( coproduct, mor3, mor1 );
#! <A morphism in ⊕ ( CategoryOfRows( Q ), 5 )>
PreCompose( coproduct, mor3, mor2 );
#! <A morphism in ⊕ ( CategoryOfRows( Q ), 5 )>

zero := ZeroObject( coproduct );;
id_source := IdentityMorphism( coproduct, source );;
id_target := IdentityMorphism( coproduct, target );;

id_source_mor1 := PreCompose( coproduct, id_source, mor1 );;
IsEqualForMorphisms( coproduct, id_source_mor1, mor1 );
#! true

id_target_mor1 := PreCompose( coproduct, mor1, id_target );;
IsEqualForMorphisms( coproduct, id_source_mor1, mor1 );
#! true

zero_mor_source_target := ZeroMorphism( coproduct, source, target );;
zero_mor_target_target := ZeroMorphism( coproduct, target, target );;
mor1_zero_mor_target_target := PreCompose( coproduct, mor1, zero_mor_target_target );;
IsEqualForMorphisms( coproduct, zero_mor_source_target, mor1_zero_mor_target_target );
#! true

#############################
# AdditionForMorphisms
#############################

add_mor1_mor1 := AdditionForMorphisms( coproduct, mor1, mor1 );;
Display( add_mor1_mor1 );
#! Component 1: a 0 x 3 morphism in Rows( Q )
#! 
#! Component 2: a 2 x 1 morphism in Rows( Q )
#! 
#! [1,1]: 8
#! [2,1]: 2
#! 
#! Component 3: a 1 x 2 morphism in Rows( Q )
#! 
#! [1,1]: 10
#! [1,2]: 12
#! 
#! Component 5: a 1 x 0 morphism in Rows( Q )

add_mor1_mor2 := AdditionForMorphisms( coproduct, mor1, mor2 );;
Display( add_mor1_mor2 );
#! Component 1: a 0 x 3 morphism in Rows( Q )
#! 
#! Component 2: a 2 x 1 morphism in Rows( Q )
#! 
#! [1,1]: -1
#! [2,1]: -7
#! 
#! Component 3: a 1 x 2 morphism in Rows( Q )
#! 
#! [1,1]: 25
#! [1,2]: 36
#! 
#! Component 5: a 1 x 0 morphism in Rows( Q )

add_id_source := AdditionForMorphisms( coproduct, id_source, id_source );;
Display( add_id_source );
#! Component 2: a 2 x 2 morphism in Rows( Q )
#! 
#! [1,1]: 2
#! [1,2]: 0
#! [2,1]: 0
#! [2,2]: 2
#! 
#! Component 3: a 1 x 1 morphism in Rows( Q )
#! 
#! [1,1]: 2
#! 
#! Component 5: a 1 x 1 morphism in Rows( Q )
#! 
#! [1,1]: 2

add_zero_mor := AdditionForMorphisms( coproduct, zero_mor_target_target, zero_mor_target_target );;
Display( add_zero_mor );
#! Component 1: a 3 x 3 morphism in Rows( Q )
#! 
#! [1,1]: 0
#! [1,2]: 0
#! [1,3]: 0
#! [2,1]: 0
#! [2,2]: 0
#! [2,3]: 0
#! [3,1]: 0
#! [3,2]: 0
#! [3,3]: 0
#! 
#! Component 2: a 1 x 1 morphism in Rows( Q )
#! 
#! [1,1]: 0
#! 
#! Component 3: a 2 x 2 morphism in Rows( Q )
#! 
#! [1,1]: 0
#! [1,2]: 0
#! [2,1]: 0
#! [2,2]: 0

#############################
# SumOfMorphisms
#############################

Display( SumOfMorphisms( coproduct, source, [ mor1, mor2, mor1 ], target ) );
#! Component 1: a 0 x 3 morphism in Rows( Q )
#! 
#! Component 2: a 2 x 1 morphism in Rows( Q )
#! 
#! [1,1]: 3
#! [2,1]: -6
#! 
#! Component 3: a 1 x 2 morphism in Rows( Q )
#! 
#! [1,1]: 30
#! [1,2]: 42
#! 
#! Component 5: a 1 x 0 morphism in Rows( Q )

Display( SumOfMorphisms( coproduct, source, [ mor1, zero_mor_source_target, mor1, zero_mor_source_target ], target ) );
#! Component 1: a 0 x 3 morphism in Rows( Q )
#! 
#! Component 2: a 2 x 1 morphism in Rows( Q )
#! 
#! [1,1]: 8
#! [2,1]: 2
#! 
#! Component 3: a 1 x 2 morphism in Rows( Q )
#! 
#! [1,1]: 10
#! [1,2]: 12
#! 
#! Component 5: a 1 x 0 morphism in Rows( Q )

#############################
# AdditiveInverseForMorphisms
#############################

id_source_inv := AdditiveInverseForMorphisms( coproduct, id_source );;
Display( id_source_inv );
#! Component 2: a 2 x 2 morphism in Rows( Q )
#! 
#! [1,1]: -1
#! [1,2]: 0
#! [2,1]: 0
#! [2,2]: -1
#! 
#! Component 3: a 1 x 1 morphism in Rows( Q )
#! 
#! [1,1]: -1
#! 
#! Component 5: a 1 x 1 morphism in Rows( Q )
#! 
#! [1,1]: -1

mor1_inv := AdditiveInverseForMorphisms( coproduct, mor1 );;
Display( mor1_inv );
#! Component 1: a 0 x 3 morphism in Rows( Q )
#! 
#! Component 2: a 2 x 1 morphism in Rows( Q )
#! 
#! [1,1]: -4
#! [2,1]: -1
#! 
#! Component 3: a 1 x 2 morphism in Rows( Q )
#! 
#! [1,1]: -5
#! [1,2]: -6
#! 
#! Component 5: a 1 x 0 morphism in Rows( Q )

zero_mor_source_target_inv := AdditiveInverseForMorphisms( coproduct, zero_mor_source_target );;
Display( zero_mor_source_target_inv );
#! Component 1: a 0 x 3 morphism in Rows( Q )
#! 
#! Component 2: a 2 x 1 morphism in Rows( Q )
#! 
#! [1,1]: 0
#! [2,1]: 0
#! 
#! Component 3: a 1 x 2 morphism in Rows( Q )
#! 
#! [1,1]: 0
#! [1,2]: 0
#! 
#! Component 5: a 1 x 0 morphism in Rows( Q )

id_zero_obj_inv := AdditiveInverseForMorphisms( coproduct, IdentityMorphism( zero ) );;
ListOfPairsOfMorphismAndIndex( id_zero_obj_inv );
#! [  ]

Display( DirectSum( coproduct, [ source, source, source ] ) );
#! [ [ A row module over Q of rank 6, 2 ], [ A row module over Q of rank 3, 3 ], [ A row module over Q of rank 3, 5 ] ]
Display( DirectSum( coproduct, [ source, target, source ] ) );
#! [ [ A row module over Q of rank 3, 1 ], [ A row module over Q of rank 5, 2 ], [ A row module over Q of rank 4, 3 ], [ A row module over Q of rank 2, 5 ] ]

####################################################
# DirectSumFunctorial
####################################################

sum := DirectSumFunctorial( coproduct, [ m1, m2, m3 ] );;
Display(sum);
#! Component 1: a 0 x 4 morphism in Rows( Q )
#! 
#! Component 2: a 6 x 0 morphism in Rows( Q )
#! 
#! Component 3: a 9 x 5 morphism in Rows( Q )
#! 
#! [1,1]: 0
#! [1,2]: 0
#! [1,3]: 0
#! [1,4]: 0
#! [1,5]: 0
#! [2,1]: 0
#! [2,2]: 0
#! [2,3]: 0
#! [2,4]: 0
#! [2,5]: 0
#! [3,1]: 0
#! [3,2]: 0
#! [3,3]: 0
#! [3,4]: 0
#! [3,5]: 0
#! [4,1]: 1
#! [4,2]: 2
#! [4,3]: 0
#! [4,4]: 0
#! [4,5]: 0
#! [5,1]: 3
#! [5,2]: 4
#! [5,3]: 0
#! [5,4]: 0
#! [5,5]: 0
#! [6,1]: 5
#! [6,2]: 6
#! [6,3]: 0
#! [6,4]: 0
#! [6,5]: 0
#! [7,1]: 0
#! [7,2]: 0
#! [7,3]: 1
#! [7,4]: 2
#! [7,5]: 3
#! [8,1]: 0
#! [8,2]: 0
#! [8,3]: 4
#! [8,4]: 5
#! [8,5]: 6
#! [9,1]: 0
#! [9,2]: 0
#! [9,3]: 7
#! [9,4]: 8
#! [9,5]: 9
#! 
#! Component 4: a 0 x 3 morphism in Rows( Q )
#! 

####################################################
# UniversalMorphismIntoDirectSumWithGivenDirectSum
####################################################

# Direct sum diagram
s1 := CategoryOfRowsObject( rows, 1 );;
s2 := CategoryOfRowsObject( rows, 2 );;
s3 := CategoryOfRowsObject( rows, 3 );;
s4 := CategoryOfRowsObject( rows, 4 );;

o1 := ObjectConstructor( coproduct, [ [s1,1], [s1,4] ] );;
o2 := ObjectConstructor( coproduct, [ [s2,3], [s2,4] ] );;
o3 := ObjectConstructor( coproduct, [ [s3,1], [s3,3] ] );;

o1o2o3 := DirectSum( coproduct, [ o1, o2, o3 ] );;

# Test object
t2 := CategoryOfRowsObject( rows, 2 );;
t3 := CategoryOfRowsObject( rows, 3 );;

test_object := ObjectConstructor( coproduct, [ [t2,2], [t3,3] ] );;

# Morphisms

# test_object -> o1
matrix_mor_t_o1_1 := HomalgMatrix( [ ], 0, RankOfObject( s1 ), QQ );;
matrix_mor_t_o1_2 := HomalgMatrix( [ ], RankOfObject( t2 ), 0, QQ );;
matrix_mor_t_o1_3 := HomalgMatrix( [ ], RankOfObject( t3 ), 0, QQ );;
matrix_mor_t_o1_4 := HomalgMatrix( [ ], 0, RankOfObject( s1 ), QQ );;

mor_t_o1_1 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o1_1 );;
mor_t_o1_2 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o1_2 );;
mor_t_o1_3 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o1_3 );;
mor_t_o1_4 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o1_4 );;

m1 := MorphismConstructor( coproduct,
                           test_object,
                           [ [ mor_t_o1_1, 1 ],
                             [ mor_t_o1_2, 2 ],
                             [ mor_t_o1_3, 3 ],
                             [ mor_t_o1_4, 4 ] ],
                           o1 );;

# test_object -> o2
matrix_mor_t_o2_2 := HomalgMatrix( [ ], RankOfObject( t2 ), 0, QQ );;
matrix_mor_t_o2_3 := HomalgMatrix( [ [1,2], [3,4], [5,6] ], RankOfObject( t3 ), RankOfObject( s2 ), QQ );;
matrix_mor_t_o2_4 := HomalgMatrix( [ ], 0, RankOfObject( s2 ), QQ );;

mor_t_o2_2 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o2_2 );;
mor_t_o2_3 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o2_3 );;
mor_t_o2_4 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o2_4 );;

m2 := MorphismConstructor( coproduct,
                           test_object,
                           [ [ mor_t_o2_2, 2 ],
                             [ mor_t_o2_3, 3 ],
                             [ mor_t_o2_4, 4 ] ],
                           o2 );;

# test_object -> o3
matrix_mor_t_o3_1 := HomalgMatrix( [ ], 0, RankOfObject( s3 ), QQ );;
matrix_mor_t_o3_2 := HomalgMatrix( [ ], RankOfObject( t2 ), 0, QQ );;
matrix_mor_t_o3_3 := HomalgMatrix( [ [1,2,3], [4,5,6], [7,8,9] ], RankOfObject( t3 ), RankOfObject( s3 ), QQ );;

mor_t_o3_1 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o3_1 );;
mor_t_o3_2 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o3_2 );;
mor_t_o3_3 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o3_3 );;

m3 := MorphismConstructor( coproduct,
                           test_object,
                           [ [ mor_t_o3_1, 1 ],
                             [ mor_t_o3_2, 2 ],
                             [ mor_t_o3_3, 3 ] ],
                           o3 );;

u := UniversalMorphismIntoDirectSumWithGivenDirectSum( coproduct, [o1,o2,o3], test_object, [m1,m2,m3], o1o2o3 );;

####################################################
# UniversalMorphismFromDirectSumWithGivenDirectSum
####################################################

# Direct sum diagram
s1 := CategoryOfRowsObject( rows, 1 );;
s2 := CategoryOfRowsObject( rows, 2 );;
s3 := CategoryOfRowsObject( rows, 3 );;
s4 := CategoryOfRowsObject( rows, 4 );;

o1 := ObjectConstructor( coproduct, [ [s1,1], [s1,4] ] );;
o2 := ObjectConstructor( coproduct, [ [s2,3], [s2,4] ] );;
o3 := ObjectConstructor( coproduct, [ [s3,1], [s3,3] ] );;

o1o2o3 := DirectSum( coproduct, [ o1, o2, o3 ] );;

# Test object
t2 := CategoryOfRowsObject( rows, 2 );;
t3 := CategoryOfRowsObject( rows, 3 );;

test_object := ObjectConstructor( coproduct, [ [t2,2], [t3,3] ] );;

# Morphisms

# 01 -> test_object
matrix_mor_t_o1_1 := HomalgMatrix( [ ], RankOfObject( s1 ), 0, QQ );;
matrix_mor_t_o1_2 := HomalgMatrix( [ ], 0, RankOfObject( t2 ), QQ );;
matrix_mor_t_o1_3 := HomalgMatrix( [ ], 0, RankOfObject( t3 ), QQ );;
matrix_mor_t_o1_4 := HomalgMatrix( [ ], RankOfObject( s1 ), 0, QQ );;

mor_t_o1_1 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o1_1 );;
mor_t_o1_2 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o1_2 );;
mor_t_o1_3 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o1_3 );;
mor_t_o1_4 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o1_4 );;

m1 := MorphismConstructor( coproduct,
                           o1,
                           [ [ mor_t_o1_1, 1 ],
                             [ mor_t_o1_2, 2 ],
                             [ mor_t_o1_3, 3 ],
                             [ mor_t_o1_4, 4 ] ],
                           test_object );;

# o2 -> test_object
matrix_mor_t_o2_2 := HomalgMatrix( [ ], 0, RankOfObject( t2 ), QQ );;
matrix_mor_t_o2_3 := HomalgMatrix( [ [1,2], [3,4], [5,6] ], RankOfObject( s2 ), RankOfObject( t3 ), QQ );;
matrix_mor_t_o2_4 := HomalgMatrix( [ ], RankOfObject( s2 ), 0, QQ );;

mor_t_o2_2 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o2_2 );;
mor_t_o2_3 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o2_3 );;
mor_t_o2_4 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o2_4 );;

m2 := MorphismConstructor( coproduct,
                           o2,
                           [ [ mor_t_o2_2, 2 ],
                             [ mor_t_o2_3, 3 ],
                             [ mor_t_o2_4, 4 ] ],
                           test_object );;

# o3 -> test_object 
matrix_mor_t_o3_1 := HomalgMatrix( [ ], RankOfObject( s3 ), 0, QQ );;
matrix_mor_t_o3_2 := HomalgMatrix( [ ], 0, RankOfObject( t2 ), QQ );;
matrix_mor_t_o3_3 := HomalgMatrix( [ [1,2,3], [4,5,6], [7,8,9] ], RankOfObject( s3 ), RankOfObject( t3 ), QQ );;

mor_t_o3_1 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o3_1 );;
mor_t_o3_2 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o3_2 );;
mor_t_o3_3 := AsCategoryOfRowsMorphism( rows, matrix_mor_t_o3_3 );;

m3 := MorphismConstructor( coproduct,
                           o3,
                           [ [ mor_t_o3_1, 1 ],
                             [ mor_t_o3_2, 2 ],
                             [ mor_t_o3_3, 3 ] ],
                           test_object );;

u := UniversalMorphismFromDirectSumWithGivenDirectSum( coproduct, [o1,o2,o3], test_object, [m1,m2,m3], o1o2o3 );;

####################################################
# ComponentOfMorphismIntoDirectSum
####################################################

# Direct sum diagram
s1 := CategoryOfRowsObject( rows, 1 );;
s2 := CategoryOfRowsObject( rows, 2 );;
s3 := CategoryOfRowsObject( rows, 3 );;
s4 := CategoryOfRowsObject( rows, 4 );;
s5 := CategoryOfRowsObject( rows, 5 );;

o1 := ObjectConstructor( coproduct, [ [s1,1], [s1,4] ] );;
o2 := ObjectConstructor( coproduct, [ [s2,3], [s2,4] ] );;
o3 := ObjectConstructor( coproduct, [ [s3,1], [s3,3] ] );;

o1o2o3 := DirectSum( coproduct, [ o1, o2, o3 ] );;

# A
a2 := CategoryOfRowsObject( rows, 2 );;
a3 := CategoryOfRowsObject( rows, 3 );;

A := ObjectConstructor( coproduct, [ [a2,2], [a3,3] ] );;

# A -> o1o2o3
matrix_mor_1 := HomalgMatrix( [ ], 0, RankOfObject( s4 ), QQ );;
matrix_mor_2 := HomalgMatrix( [ ], RankOfObject( a2 ), 0, QQ );;
matrix_mor_3 := HomalgMatrix( [ [1,2,3,4,5],
                                [1,2,3,4,5],
                                [1,2,3,4,5] ],
                              RankOfObject( a3 ),
                              RankOfObject( s5 ),
                              QQ );;

matrix_mor_4 := HomalgMatrix( [ ], 0, RankOfObject( s3 ), QQ );;

mor_1 := AsCategoryOfRowsMorphism( rows, matrix_mor_1 );;
mor_2 := AsCategoryOfRowsMorphism( rows, matrix_mor_2 );;
mor_3 := AsCategoryOfRowsMorphism( rows, matrix_mor_3 );;
mor_4 := AsCategoryOfRowsMorphism( rows, matrix_mor_4 );;

morphism := MorphismConstructor( coproduct,
                                 A,
                                 [ [ mor_1, 1 ],
                                   [ mor_2, 2 ],
                                   [ mor_3, 3 ],
                                   [ mor_4, 4 ] ],
                                 o1o2o3 );;

component1 := ComponentOfMorphismIntoDirectSum( coproduct, morphism, [ o1, o2, o3 ], 1 );;
Display( component1 );
#! Component 1: a 0 x 1 morphism in Rows( Q )
#! 
#! Component 2: a 2 x 0 morphism in Rows( Q )
#! 
#! Component 3: a 3 x 0 morphism in Rows( Q )
#! 
#! Component 4: a 0 x 1 morphism in Rows( Q )
#! 

component2 := ComponentOfMorphismIntoDirectSum( coproduct, morphism, [ o1, o2, o3 ], 2 );;
Display( component2 );
#! Component 1: a 0 x 0 morphism in Rows( Q )
#! 
#! Component 2: a 2 x 0 morphism in Rows( Q )
#! 
#! Component 3: a 3 x 2 morphism in Rows( Q )
#! 
#! [1,1]: 1
#! [1,2]: 2
#! [2,1]: 1
#! [2,2]: 2
#! [3,1]: 1
#! [3,2]: 2
#! 
#! Component 4: a 0 x 2 morphism in Rows( Q )
#! 

component3 := ComponentOfMorphismIntoDirectSum( coproduct, morphism, [ o1, o2, o3 ], 3 );;
Display( component3 );
#! Component 1: a 0 x 3 morphism in Rows( Q )
#! 
#! Component 2: a 2 x 0 morphism in Rows( Q )
#! 
#! Component 3: a 3 x 3 morphism in Rows( Q )
#! 
#! [1,1]: 3
#! [1,2]: 4
#! [1,3]: 5
#! [2,1]: 3
#! [2,2]: 4
#! [2,3]: 5
#! [3,1]: 3
#! [3,2]: 4
#! [3,3]: 5
#! 
#! Component 4: a 0 x 0 morphism in Rows( Q )
#! 

####################################################
# MultiplyWithElementOfCommutativeRingForMorphisms
####################################################

morphism_x_5 := MultiplyWithElementOfCommutativeRingForMorphisms( coproduct, 5, morphism );;
Display( morphism_x_5 );
#! Component 1: a 0 x 4 morphism in Rows( Q )
#! 
#! Component 2: a 2 x 0 morphism in Rows( Q )
#! 
#! Component 3: a 3 x 5 morphism in Rows( Q )
#! 
#! [1,1]: 5
#! [1,2]: 10
#! [1,3]: 15
#! [1,4]: 20
#! [1,5]: 25
#! [2,1]: 5
#! [2,2]: 10
#! [2,3]: 15
#! [2,4]: 20
#! [2,5]: 25
#! [3,1]: 5
#! [3,2]: 10
#! [3,3]: 15
#! [3,4]: 20
#! [3,5]: 25
#! 
#! Component 4: a 0 x 3 morphism in Rows( Q )
#! 

####################################
# Abelian structure
####################################

kernel_obj := KernelObject( morphism );;
kernel_emb := KernelEmbeddingWithGivenKernelObject( morphism, kernel_obj );;
precomp := PreCompose( kernel_emb, morphism );;
IsZeroForMorphisms( precomp );
#! true

cokernel_obj := CokernelObject( morphism );;
cokernel_proj := CokernelProjectionWithGivenCokernelObject( morphism, cokernel_obj );;
precomp := PreCompose( morphism, cokernel_proj );;
IsZeroForMorphisms( precomp );
#! true

id_target := IdentityMorphism( Target( morphism ) );;
lift := Lift( morphism, id_target );;
IsEqualForMorphisms( morphism, PreCompose( lift, id_target ) );
#! true

id_source := IdentityMorphism( Source( morphism ) );;
colift := Colift( id_source, morphism );;
IsEqualForMorphisms( morphism, PreCompose( id_source, colift ) );
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
#! A morphism in Rows( Q )
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
