#! @BeginChunk AddClosureDisconnectedConstruction

#! @Example
LoadPackage( "LinearClosuresForCAP", false );
#! true
D := FiniteSkeletalDiscreteCategory( 4 );;
Q := HomalgFieldOfRationals( );;
L := LinearClosure( Q, D );;
A := AdditiveClosureOfObjectFiniteDisconnectedCategory( L );;
source := ObjectConstructor( A, [ 3, [ 2, 1, 0, 0 ] ] );;
Display( source );
#! A formal direct sum consisting of 3 objects:
#! 
#! 2 times: <An object in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 4 ] ) )>
#! 1 times: <An object in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 4 ] ) )>
#! 0 times: <An object in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 4 ] ) )>
#! 0 times: <An object in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 4 ] ) )>
target := ObjectConstructor( A, [ 2, [ 0, 1, 1, 0 ] ] );;
Display( target );
#! A formal direct sum consisting of 2 objects:
#! 
#! 0 times: <An object in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 4 ] ) )>
#! 1 times: <An object in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 4 ] ) )>
#! 1 times: <An object in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 4 ] ) )>
#! 0 times: <An object in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 4 ] ) )>
id_b := IdentityMorphism( D[2] ) / L;;
matrix := [ [ [], [] ], [ [ id_b ] ], [ ], [ ] ];;
matrix2 := [ [ ], [ [ id_b ] ], [ [] ], [ ] ];;
m := MorphismConstructor( A, source, matrix, target );;
m2 := MorphismConstructor( A, target, matrix2, source );;
PreCompose( A, m, m2 );;
PreCompose( A, m2, m );;
Display( m );
#! A 2 x 0 matrix with entries in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 4 ] ) )
#! 
#! A 1 x 1 matrix with entries in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 4 ] ) )
#! 
#! [1,1]: 1·<An identity morphism in FiniteSkeletalDiscreteCategory( [ 1 .. 4 ] )>
#! 
#! A 0 x 1 matrix with entries in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 4 ] ) )
#! 
#! A 0 x 0 matrix with entries in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 4 ] ) )
#! 
#! @EndExample
#! @EndChunk

