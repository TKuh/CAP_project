#! @Chapter Skeletal Category of group representations
#! @Section Examples and Tests

#! @Example
LoadPackage( "GroupRepresentationsForCAP", false );
#! true

permcat := PermutationCategory( );;
prod_perms := SparseProductOfPermutationCategory( 5, permcat );;

Display( prod_perms );
#! A CAP category with name 𝚷( 5, PermutationCategory ):
#! 
#! 13 primitive operations were used to derive 25 operations for this categor\
#! y which mathematically
#! * IsSkeletalCategory

Q := HomalgFieldOfRationals();;
rows := CategoryOfRows( Q );;

F := FunctorPermutationCategoryToCategoryOfRows( permcat, rows );;
# PF := ExtendFunctorToSparseProduct( F, prod_perms );

zero := ObjectConstructor( permcat, 0 );;
o1 := ObjectConstructor( permcat, 1 );;
o2 := ObjectConstructor( permcat, 2 );;
o3 := ObjectConstructor( permcat, 3 );;
o4 := ObjectConstructor( permcat, 4 );;
o5 := ObjectConstructor( permcat, 5 );;

object := ObjectConstructor( prod_perms, [ 4, [ 1, 2, 3, 5 ], [ o1, o4, o2, o1 ] ] );;
object2 := ObjectConstructor( prod_perms, [ 4, [ 1, 2, 3, 5 ], [ o2, o3, o1, o5 ] ] );;

IsWellDefinedForObjects( object );
#! true
IsWellDefinedForObjects( object2 );
#! true

morphism_1 := MorphismConstructor( permcat, o1, (), o1 );;
morphism_2 := MorphismConstructor( permcat, o4, (4,2,1,3), o4 );;
morphism_3 := MorphismConstructor( permcat, o2, (2,1), o2 );;
morphism_4 := MorphismConstructor( permcat, zero, (), zero );;
morphism_5 := MorphismConstructor( permcat, o1, (), o1 );;
triple := [ 4, [ 1, 2, 3, 5 ], [ morphism_1, morphism_2, morphism_3, morphism_5 ] ];;

mor := MorphismConstructor( prod_perms, object, triple, object );;
IsWellDefinedForMorphisms( mor );
#! true

morphism2_1 := MorphismConstructor( permcat, o1, (), o1 );;
morphism2_2 := MorphismConstructor( permcat, o4, (1,3,4,2), o4 );;
morphism2_3 := MorphismConstructor( permcat, o2, (), o2 );;
morphism2_4 := MorphismConstructor( permcat, zero, (), zero );;
morphism2_5 := MorphismConstructor( permcat, o1, (), o1 );;
triple2 := [ 4, [ 1, 2, 3, 5 ], [ morphism2_1, morphism2_2, morphism2_3, morphism2_5 ] ];;

mor2 := MorphismConstructor( prod_perms, object, triple2, object );;
IsWellDefinedForMorphisms( mor2 );
#! true

ObjectDatum( object );
#! [ 4, [ 1, 2, 3, 5 ], 
#!   [ <An object in PermutationCategory>, 
#!       <An object in PermutationCategory>, 
#!       <An object in PermutationCategory>, 
#!       <An object in PermutationCategory> ] ]

MorphismDatum( mor );
#! [ 4, [ 1, 2, 3, 5 ], 
#!   [ <A morphism in PermutationCategory>, 
#!       <A morphism in PermutationCategory>, 
#!       <A morphism in PermutationCategory>, 
#!       <A morphism in PermutationCategory> ] ]

z := ObjectConstructor( prod_perms, [ 0, [ ], [ ] ] );;
Display( z );
#! [ 0, [  ], [  ] ]

u := ObjectConstructor( prod_perms, [ 1, [ 1 ], [ o1 ] ] );;
Display( u );
#! [ 1, [ 1 ], [ An object in PermutationCategory ] ]

#########################################
# IdentityMorphism
#########################################

id_object := IdentityMorphism( object );;
# Display( ApplyFunctor( SF, id_o1 ) );

IsWellDefinedForMorphisms( id_object );
#! true

Display( id_object );
#! Component: (1)
#! 
#! 1 ⱶ()→ 1
#! ------------------------
#! Component: (2)
#! 
#! 4 ⱶ()→ 4
#! ------------------------
#! Component: (3)
#! 
#! 2 ⱶ()→ 2
#! ------------------------
#! Component: (5)
#! 
#! 1 ⱶ()→ 1
#! ------------------------

#########################################
# IsEqualForObjects
#########################################

IsEqualForObjects( object, object );
#! true

IsEqualForObjects( object, object2 );
#! false

IsEqualForObjects( object2, object );
#! false

#########################################
# IsEqualForMorphisms
#########################################

IsEqualForMorphisms( mor, mor );
#! true

IsEqualForMorphisms( id_object, id_object );
#! true

IsEqualForMorphisms( id_object, mor );
#! false

IsEqualForMorphisms( mor, mor2 );
#! false

IsEqualForMorphisms( id_object, mor2 );
#! false

#########################################
# IsCongruentForMorphisms
#########################################

IsCongruentForMorphisms( mor, mor );
#! true

IsCongruentForMorphisms( id_object, id_object );
#! true

IsCongruentForMorphisms( id_object, mor );
#! false

IsCongruentForMorphisms( mor, mor2 );
#! false

IsCongruentForMorphisms( id_object, mor2 );
#! false

#########################################
# PreCompose
#########################################

id_object_mor := PreCompose( id_object, mor );;
IsEqualForMorphisms( id_object_mor, mor );
#! true

mor_id_object := PreCompose( mor, id_object );;
IsEqualForMorphisms( mor, mor_id_object );
#! true

mor2_mor := PreCompose( mor2, mor );

mor_mor := PreCompose( mor, mor );
IsEqualForMorphisms( id_object, mor_mor );
#! false
Display( mor_mor );
#! Component: (1)
#! 
#! 1 ⱶ()→ 1
#! ------------------------
#! Component: (2)
#! 
#! 4 ⱶ(1,4)(2,3)→ 4
#! ------------------------
#! Component: (3)
#! 
#! 2 ⱶ()→ 2
#! ------------------------
#! Component: (5)
#! 
#! 1 ⱶ()→ 1
#! ------------------------

mor_mor2 := PreCompose( mor, mor2 );
IsEqualForMorphisms( mor_mor2, mor2_mor );
#! true
Display( mor_mor2 );
#! Component: (1)
#! 
#! 1 ⱶ()→ 1
#! ------------------------
#! Component: (2)
#! 
#! 4 ⱶ(1,4)(2,3)→ 4
#! ------------------------
#! Component: (3)
#! 
#! 2 ⱶ(1,2)→ 2
#! ------------------------
#! Component: (5)
#! 
#! 1 ⱶ()→ 1
#! ------------------------
Display( mor2_mor );
#! Component: (1)
#! 
#! 1 ⱶ()→ 1
#! ------------------------
#! Component: (2)
#! 
#! 4 ⱶ(1,4)(2,3)→ 4
#! ------------------------
#! Component: (3)
#! 
#! 2 ⱶ(1,2)→ 2
#! ------------------------
#! Component: (5)
#! 
#! 1 ⱶ()→ 1
#! ------------------------

Display( ApplyFunctor( F, mor_mor2[1] ) );
#! Source: 
#! A row module over Q of rank 1
#! 
#! Matrix: 
#! [ [  1 ] ]
#! 
#! Range: 
#! A row module over Q of rank 1
#! 
#! A morphism in Rows( Q )

Display( ApplyFunctor( F, mor_mor2[2] ) );
#! Source: 
#! A row module over Q of rank 4
#! 
#! Matrix: 
#! [ [  0,  0,  0,  1 ],
#!   [  0,  0,  1,  0 ],
#!   [  0,  1,  0,  0 ],
#!   [  1,  0,  0,  0 ] ]
#! 
#! Range: 
#! A row module over Q of rank 4
#! 
#! A morphism in Rows( Q )

Display( ApplyFunctor( F, mor_mor2[3] ) );
#! Source: 
#! A row module over Q of rank 2
#! 
#! Matrix: 
#! [ [  0,  1 ],
#!   [  1,  0 ] ]
#! 
#! Range: 
#! A row module over Q of rank 2
#! 
#! A morphism in Rows( Q )

Display( ApplyFunctor( F, mor_mor2[4] ) );
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

Display( ApplyFunctor( F, mor_mor2[5] ) );
#! Source: 
#! A row module over Q of rank 1
#! 
#! Matrix: 
#! [ [  1 ] ]
#! 
#! Range: 
#! A row module over Q of rank 1
#! 
#! A morphism in Rows( Q )

#########################################
# InverseForMorphisms
#########################################

mor_inv := InverseForMorphisms( mor );
Display( mor_inv );
#! Component: (1)
#! 
#! 1 ⱶ()→ 1
#! ------------------------
#! Component: (2)
#! 
#! 4 ⱶ(1,2,4,3)→ 4
#! ------------------------
#! Component: (3)
#! 
#! 2 ⱶ(1,2)→ 2
#! ------------------------
#! Component: (5)
#! 
#! 1 ⱶ()→ 1
#! ------------------------

#########################################
# Coproduct
#########################################

product := Coproduct( [ object, object, object ] );;

Display( product[1] );
#! 3
Display( product[2] );
#! 12
Display( product[3] );
#! 6
Display( product[4] );
#! 0
Display( product[5] );
#! 3

product := Coproduct( [ object, object2, object ] );;

Display( product[1] );
#! 4
Display( product[2] );
#! 11
Display( product[3] );
#! 5
Display( product[4] );
#! 0
Display( product[5] );
#! 7

#########################################
# CoproductFunctorial
#########################################

product := CoproductFunctorial( [ mor, mor ] );

product_1_rows := ApplyFunctor( F, product[1] );;
product_2_rows := ApplyFunctor( F, product[2] );;
product_3_rows := ApplyFunctor( F, product[3] );;
product_4_rows := ApplyFunctor( F, product[4] );;
product_5_rows := ApplyFunctor( F, product[5] );;

product_1_rows =
    CoproductFunctorial( [
        ApplyFunctor( F, mor[1] ),
        ApplyFunctor( F, mor[1] ) ] );
#! true

product_2_rows =
    CoproductFunctorial( [
        ApplyFunctor( F, mor[2] ),
        ApplyFunctor( F, mor[2] ) ] );
#! true

product_3_rows =
    CoproductFunctorial( [
        ApplyFunctor( F, mor[3] ),
        ApplyFunctor( F, mor[3] ) ] );
#! true

product_4_rows =
    CoproductFunctorial( [
        ApplyFunctor( F, mor[4] ),
        ApplyFunctor( F, mor[4] ) ] );
#! true

product_5_rows =
    CoproductFunctorial( [
        ApplyFunctor( F, mor[5] ),
        ApplyFunctor( F, mor[5] ) ] );
#! true

#! @EndExample
