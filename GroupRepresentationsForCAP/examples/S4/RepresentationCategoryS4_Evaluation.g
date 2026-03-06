#! @Chapter Examples
LoadPackage( "GroupRepresentationsForCAP" );

#! @Example

RepG := RepresentationCategory( SymmetricGroup( 4 ) );;

Qmat := UnderlyingCategoryForSemisimpleCategory( RepG );;
QQ := UnderlyingRing( Qmat );;
G := UnderlyingGroupForRepresentationCategory( RepG );;

irr := Irr( G );;

x1 := RepresentationCategoryObject( irr[1], RepG );;
x2 := RepresentationCategoryObject( irr[2], RepG );;
x3 := RepresentationCategoryObject( irr[3], RepG );;
x4 := RepresentationCategoryObject( irr[4], RepG );;

#########################
# EvaluationForDual
#########################

TestZigZagIdentitiesForDual( RepG, x1 );
#! true
TestZigZagIdentitiesForDual( RepG, x2 );
#! true
TestZigZagIdentitiesForDual( RepG, x3 );
#! true
TestZigZagIdentitiesForDual( RepG, x4 );
#! true

Display( EvaluationForDual( x1 ) );
#! Component: (x_5)
#!
#! 1
#!
#! ------------------------
Display( EvaluationForDual( x2 ) );
#! Component: (x_5)
#!
#! 3
#!
#! ------------------------
Display( EvaluationForDual( x3 ) );
#! Component: (x_5)
#!
#! 2
#!
#! ------------------------
Display( EvaluationForDual( x4 ) );
#! Component: (x_5)
#!
#! 3
#!
#! ------------------------

x3_x4 := DirectSum( x3, x4 );;
x3x3x3 := DirectSum( [ x3, x3, x3 ] );;
x3x3x3_x4x4 := DirectSum( [ x3, x3, x3, x4, x4 ] );;
x1_x2_x1_x3x3_x4_x1 := DirectSum( [ x1, x2, x1, x3, x3, x4, x1 ] );;

unit := TensorUnit( RepG );;
A := DirectSum( [ x1, x4, x4 ] );;
AV := DualOnObjects( A );;
AVA := TensorProductOnObjects( A, AV );;
# Display( EvaluationForDualWithGivenTensorProduct( AVA, A, unit ) );

TestZigZagIdentitiesForDual( RepG, A );
#! true

# EvaluationForDual( A );
A_list := SemisimpleCategoryObjectListWithActualObjects( A );
CAP_INTERNAL_EvaluationForDualOnIrreduciblesAsString( A_list[1][2] );
CAP_INTERNAL_EvaluationForDualOnIrreduciblesAsString( A_list[2][2] );

Display( EvaluationForDual( x3x3x3 ) );
#! Component: (x_5)
#!
#! 2,
#! 0,
#! 0,
#! 0,
#! 2,
#! 0,
#! 0,
#! 0,
#! 2 
#!
#! ------------------------
Display( EvaluationForDual( x3_x4 ) );
#! Component: (x_5)
#!
#! 2,
#! 3 
#!
#! ------------------------
Display( EvaluationForDual( x3x3x3_x4x4 ) );
#! Component: (x_5)
#!
#! 2,
#! 0,
#! 0,
#! 0,
#! 2,
#! 0,
#! 0,
#! 0,
#! 2,
#! 3,
#! 0,
#! 0,
#! 3 
#!
#! ------------------------
Display( EvaluationForDual( x1_x2_x1_x3x3_x4_x1 ) );
#! Component: (x_5)
#!
#! 1,
#! 0,
#! 0,
#! 0,
#! 1,
#! 0,
#! 0,
#! 0,
#! 1,
#! 3,
#! 2,
#! 0,
#! 0,
#! 2,
#! 3 
#!
#! ------------------------

#! @EndExample
