#! @Chapter Linear closure of a finite skeletal discrete category

#! @Section Examples and Tests

LoadPackage( "LinearClosuresForCAP" );;

#! @Example
D := FiniteSkeletalDiscreteCategory( 5 );;

QQ := HomalgRingOfIntegers();;
# Zmod4 := HomalgRingOfIntegersInExternalGAP( ) / 2^2;
# Zmod4_constructor := RingElementConstructor( Zmod4 );

LC := LinearClosure( QQ, D );;
EnableFullInputSanityChecks( LC );;
EnableFullOutputSanityChecks( LC );;

one := ObjectConstructor( D, 1 );;
two := ObjectConstructor( D, 2 );;

one_lc := ObjectConstructor( LC, one );;
two_lc := ObjectConstructor( LC, two );;

id_one := IdentityMorphism( D, one );;
id_two := IdentityMorphism( D, two );;

id_one_lc := MorphismConstructor( LC, one_lc, [ [ 3 ], [ id_one ] ], one_lc );;
id_two_lc := MorphismConstructor( LC, two_lc, [ [ 2 ], [ id_two ] ], two_lc );;

zero_mor_11 := ZeroMorphism( LC, one_lc, one_lc );;
zero_mor_12 := ZeroMorphism( LC, one_lc, two_lc );;
zero_mor_21 := ZeroMorphism( LC, two_lc, one_lc );;
zero_mor_22 := ZeroMorphism( LC, two_lc, two_lc );;

IsZeroForMorphisms( zero_mor_11 );
#! true
IsZeroForMorphisms( zero_mor_12 );
#! true
IsZeroForMorphisms( zero_mor_21 );
#! true
IsZeroForMorphisms( zero_mor_22 );
#! true

ObjectDatum( one_lc );
#! <An object in FiniteSkeletalDiscreteCategory( 5 )>

MorphismDatum( id_one_lc );
#! [ [ <An identity morphism in FiniteSkeletalDiscreteCategory( 5 )> ], [ 3 ] ]

IsWellDefinedForObjects( one_lc );
#! true
IsWellDefinedForMorphisms( id_one_lc );
#! true
IsWellDefinedForMorphisms( 2*id_two_lc );
#! true
IsWellDefinedForMorphisms( zero_mor_11 );
#! true
IsWellDefinedForMorphisms( zero_mor_12 );
#! true
IsWellDefinedForMorphisms( zero_mor_22 );
#! true

IsEqualForObjects( one_lc, one_lc );
#! true
IsEqualForObjects( one_lc, two_lc );
#! false

IsEqualForMorphisms( id_one_lc, id_one_lc );
#! true
IsEqualForMorphisms( LC, id_one_lc, id_two_lc );
#! false
IsEqualForMorphisms( LC, zero_mor_22, id_two_lc );
#! false

PreCompose( id_one_lc, id_one_lc );
#! 9·<An identity morphism in FiniteSkeletalDiscreteCategory( 5 )>
PreCompose( id_two_lc, id_two_lc );
#! 4·<An identity morphism in FiniteSkeletalDiscreteCategory( 5 )>
PreCompose( id_one_lc, zero_mor_11 );
#! 0
PreCompose( id_one_lc, zero_mor_12 );
#! 0
PreCompose( id_two_lc, zero_mor_22 );
#! 0
PreCompose( id_two_lc, zero_mor_21 );
#! 0
PreCompose( zero_mor_11, zero_mor_11 );
#! 0
PreCompose( zero_mor_12, zero_mor_21 );
#! 0
PreCompose( [ zero_mor_12, id_two_lc, zero_mor_21 ] );
#! 0
PreCompose( [ id_one_lc, zero_mor_12, id_two_lc ] );
#! 0

IdentityMorphism( two_lc );
#! 1·<An identity morphism in FiniteSkeletalDiscreteCategory( 5 )>

MultiplyWithElementOfCommutativeRingForMorphisms( LC, 3, id_one_lc );
#! 9·<An identity morphism in FiniteSkeletalDiscreteCategory( 5 )>
MultiplyWithElementOfCommutativeRingForMorphisms( LC, 0, id_one_lc );
#! 0

AdditionForMorphisms( id_one_lc, 10*id_one_lc );
#! 33·<An identity morphism in FiniteSkeletalDiscreteCategory( 5 )>
AdditionForMorphisms( id_one_lc, -1*id_one_lc );
#! 0
AdditionForMorphisms( id_one_lc, zero_mor_11 );
#! 3·<An identity morphism in FiniteSkeletalDiscreteCategory( 5 )>
AdditionForMorphisms( zero_mor_11, id_one_lc );
#! 3·<An identity morphism in FiniteSkeletalDiscreteCategory( 5 )>
AdditionForMorphisms( zero_mor_11, zero_mor_11 );
#! 0
AdditionForMorphisms( zero_mor_12, -1*zero_mor_12 );
#! 0

SumOfMorphisms( one_lc, [ zero_mor_11, id_one_lc, 10*id_one_lc ], one_lc  );
#! 33·<An identity morphism in FiniteSkeletalDiscreteCategory( 5 )>
SumOfMorphisms( one_lc, [ id_one_lc, zero_mor_11, 10*id_one_lc ], one_lc  );
#! 33·<An identity morphism in FiniteSkeletalDiscreteCategory( 5 )>
SumOfMorphisms( one_lc, [ id_one_lc, 10*id_one_lc, zero_mor_11 ], one_lc  );
#! 33·<An identity morphism in FiniteSkeletalDiscreteCategory( 5 )>
SumOfMorphisms( one_lc, [ ZeroMorphism( LC, one_lc, two_lc ), ZeroMorphism( LC, one_lc, two_lc ), ZeroMorphism( LC, one_lc, two_lc )], two_lc  );
#! 0
SumOfMorphisms( one_lc, [ zero_mor_11, id_one_lc, -1*id_one_lc ], one_lc  );
#! 0
SumOfMorphisms( one_lc, [ id_one_lc, zero_mor_11, -1*id_one_lc ], one_lc  );
#! 0

AdditiveInverseForMorphisms( id_one_lc );
#! -3·<An identity morphism in FiniteSkeletalDiscreteCategory( 5 )>
AdditiveInverseForMorphisms( SubtractionForMorphisms( id_one_lc, id_one_lc ) );
#! 0
AdditiveInverseForMorphisms( zero_mor_12 );
#! 0
AdditiveInverseForMorphisms( zero_mor_22 );
#! 0

SubtractionForMorphisms( 5*id_one_lc, id_one_lc );
#! 12·<An identity morphism in FiniteSkeletalDiscreteCategory( 5 )>
SubtractionForMorphisms( id_one_lc, zero_mor_11 );
#! 3·<An identity morphism in FiniteSkeletalDiscreteCategory( 5 )>
SubtractionForMorphisms( zero_mor_22, id_two_lc );
#! -2·<An identity morphism in FiniteSkeletalDiscreteCategory( 5 )>
SubtractionForMorphisms( zero_mor_11, zero_mor_11 );
#! 0
IsZeroForMorphisms( SubtractionForMorphisms( id_one_lc, id_one_lc ) );
#! true
IsEqualForMorphisms( SubtractionForMorphisms( id_one_lc, id_one_lc ), zero_mor_11 );
#! true

sub := SubtractionForMorphisms( id_one_lc, id_one_lc );;
IsEqualForObjects( Source( sub ), Source( zero_mor_12 ) );
#! true
IsEqualForObjects( Target( sub ), Target( zero_mor_12 ) );
#! false
IsEqualForMorphisms( sub, zero_mor_12 );
#! false

Length( SetOfObjectsOfCategory( LC ) );
#! 5

#! @EndExample
