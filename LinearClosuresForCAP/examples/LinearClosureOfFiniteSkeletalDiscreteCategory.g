#! @Chapter Linear closure of a finite skeletal discrete category

#! @Section Examples and Tests

LoadPackage( "LinearClosuresForCAP" );;

#! @Example
D := FiniteSkeletalDiscreteCategory( [ 1 .. 5 ] );;
QQ := HomalgFieldOfRationals();;
LC := LinearClosure( QQ, D );;

one := ObjectConstructor( D, 1 );;
two := ObjectConstructor( D, 2 );;

one_lc := ObjectConstructor( LC, one );;
two_lc := ObjectConstructor( LC, two );;

id_one := IdentityMorphism( D, one );;
id_two := IdentityMorphism( D, two );;

id_one_lc := MorphismConstructor( LC, one_lc, 3, one_lc );;
id_two_lc := MorphismConstructor( LC, two_lc, 2, two_lc );;

ObjectDatum( one_lc );
#! <An object in FiniteSkeletalDiscreteCategory( [ 1 .. 5 ] )>

MorphismDatum( id_one_lc );
#! 3

IsWellDefinedForObjects( one_lc );
#! true

IsWellDefinedForMorphisms( id_one_lc );
#! true

IsEqualForObjects( one_lc, one_lc );
#! true
IsEqualForObjects( one_lc, two_lc );
#! false

IsEqualForMorphisms( id_one_lc, id_one_lc );
#! true
# IsEqualForMorphisms( LC, id_one_lc, id_two_lc );

PreCompose( id_one_lc, id_one_lc );
#! 9·<An identity morphism in FiniteSkeletalDiscreteCategory( [ 1 .. 5 ] )>

IdentityMorphism( two_lc );
#! 1·<An identity morphism in FiniteSkeletalDiscreteCategory( [ 1 .. 5 ] )>

zero_morphism_one_two := ZeroMorphism( LC, one_lc, two_lc );
#! 0
IsZeroForMorphisms( zero_morphism_one_two );
#! true
IsZeroForMorphisms( id_one_lc );
#! false

MultiplyWithElementOfCommutativeRingForMorphisms( 10, id_one_lc );
#! 30·<An identity morphism in FiniteSkeletalDiscreteCategory( [ 1 .. 5 ] )>

AdditionForMorphisms( id_one_lc, 10*id_one_lc );
#! 33·<An identity morphism in FiniteSkeletalDiscreteCategory( [ 1 .. 5 ] )>

SumOfMorphisms( one_lc, [ ZeroMorphism( LC, one_lc, one_lc ), id_one_lc, 10*id_one_lc ], one_lc  );
#! 33·<An identity morphism in FiniteSkeletalDiscreteCategory( [ 1 .. 5 ] )>

AdditiveInverseForMorphisms( id_one_lc );
#! -3·<An identity morphism in FiniteSkeletalDiscreteCategory( [ 1 .. 5 ] )>

SubtractionForMorphisms( 5*id_one_lc, id_one_lc );
#! 12·<An identity morphism in FiniteSkeletalDiscreteCategory( [ 1 .. 5 ] )>
IsZeroForMorphisms( SubtractionForMorphisms( id_one_lc, id_one_lc ) );
#! true

Length( SetOfObjectsOfCategory( LC ) );
#! 5

#! @EndExample
