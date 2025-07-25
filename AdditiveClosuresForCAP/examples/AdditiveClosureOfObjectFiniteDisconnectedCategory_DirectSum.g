#! @BeginChunk AddClosureDisconnectedDirectSum

#! @Example
LoadPackage( "LinearClosuresForCAP", false );
#! true
D := FiniteSkeletalDiscreteCategory( 2 );;
Q := HomalgFieldOfRationals( );;
L := LinearClosure( Q, D );;
A := AdditiveClosureOfObjectFiniteDisconnectedCategory( L );;
a := ObjectConstructor( A, [1,[1,0]] );;
b := ObjectConstructor( A, [1,[0,1]] );;
diag := [ a, b, b ];;
pr1 := ProjectionInFactorOfDirectSum( diag, 1 );;
pr2 := ProjectionInFactorOfDirectSum( diag, 2 );;
pr3 := ProjectionInFactorOfDirectSum( diag, 3 );;
u := UniversalMorphismIntoDirectSum( [ pr1, pr2, pr3 ] );;
IsOne( u );
#! true
#! @EndExample
#! @EndChunk
