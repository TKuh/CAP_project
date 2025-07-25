
gap> START_TEST("AdditiveClosureOfObjectFiniteDisconnectedCategoryTest");

gap> LoadPackage( "LinearClosuresForCAP", false );
true
gap> D := FiniteSkeletalDiscreteCategory( 3 );;
gap> Q := HomalgFieldOfRationals( );;
gap> L := LinearClosure( Q, D );;
gap> DAC := AdditiveClosureOfObjectFiniteDisconnectedCategory( L );;
gap> AC := ModelingCategory( DAC );;
gap> a := D[1] / L;;
gap> b := D[2] / L;;
gap> c := D[3] / L;;
gap> id_a := IdentityMorphism( L, a );;
gap> id_b := IdentityMorphism( L, b );;
gap> id_c := IdentityMorphism( L, c );;
gap> #########################################
> # Objects
> #########################################
> 
> a1_reinterp := ObjectConstructor( DAC, [ 5, [ 2, 2, 1 ] ] );
<An object in AdditiveClosureOfObjectFiniteDisconnectedCategory( LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 3 ] ) ) ) defined by 5 underlying objects>
gap> Display( a1_reinterp );
A formal direct sum consisting of 5 objects:

2 times: <An object in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 3 ] ) )>
2 times: <An object in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 3 ] ) )>
1 times: <An object in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 3 ] ) )>
gap> a2_reinterp := ObjectConstructor( DAC, [ 2, [ 1, 1, 0 ] ] );;
gap> Display( a2_reinterp );
A formal direct sum consisting of 2 objects:

1 times: <An object in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 3 ] ) )>
1 times: <An object in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 3 ] ) )>
0 times: <An object in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 3 ] ) )>
gap> a1_model := ModelingObject( DAC, a1_reinterp );;
gap> a2_model := ModelingObject( DAC, a2_reinterp );;
gap> a1_reinterp = ReinterpretationOfObject( DAC, a1_model );
true
gap> a2_reinterp = ReinterpretationOfObject( DAC, a2_model );
true
gap> a1_model := ObjectConstructor( AC, [ 5, [ 2, 2, 1 ] ] );;
gap> a2_model := ObjectConstructor( AC, [ 2, [ 1, 1, 0 ] ] );;
gap> a1_model = ModelingObject( DAC, a1_reinterp );
true
gap> a2_model = ModelingObject( DAC, a2_reinterp );
true
gap> #########################################
> # Morphisms
> #########################################
> 
> matrix_a := [ [ id_a ], [ id_a ] ];;
gap> matrix_b := [ [ id_b ], [ id_b ] ];;
gap> matrix_c := [ [] ];;
gap> matrix := [ matrix_a, matrix_b, matrix_c ];;
gap> mor_reinterp := MorphismConstructor( DAC, a1_reinterp, matrix, a2_reinterp );
<A morphism in AdditiveClosureOfObjectFiniteDisconnectedCategory( LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 3 ] ) ) ) defined by a list of 3 matrices of underlying morphisms>
gap> Display( mor_reinterp );
A 2 x 1 matrix with entries in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 3 ] ) )

[1,1]: 1·<An identity morphism in FiniteSkeletalDiscreteCategory( [ 1 .. 3 ] )>
[2,1]: 1·<An identity morphism in FiniteSkeletalDiscreteCategory( [ 1 .. 3 ] )>

A 2 x 1 matrix with entries in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 3 ] ) )

[1,1]: 1·<An identity morphism in FiniteSkeletalDiscreteCategory( [ 1 .. 3 ] )>
[2,1]: 1·<An identity morphism in FiniteSkeletalDiscreteCategory( [ 1 .. 3 ] )>

A 1 x 0 matrix with entries in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 3 ] ) )

gap> IsWellDefinedForMorphisms( mor_reinterp );
true
gap> mor_model := ModelingMorphism( DAC, mor_reinterp );;
gap> mor_reinterp = ReinterpretationOfMorphism( DAC, Source( mor_reinterp ), mor_model, Target( mor_reinterp ) );
true
gap> mor_model := ModelingTowerMorphismConstructor( DAC, a1_model, matrix, a2_model );;
gap> mor_reinterp := ReinterpretationOfMorphism( DAC, a1_reinterp, mor_model, a2_reinterp );;
gap> IsWellDefinedForMorphisms( mor_reinterp );
true
gap> mor_model = ModelingMorphism( DAC, mor_reinterp );
true
gap> IsWellDefinedForMorphisms( mor_model );
true
gap> ##################################################################################
> # Check some corner cases
> ##################################################################################
> 
> zero := ObjectConstructor( DAC, [0,[0,0,0]] );;
gap> list_of_matrices := [ [], [], [] ];;
gap> zero_mor := MorphismConstructor( DAC, zero, list_of_matrices, zero );;
gap> IsWellDefined( zero_mor );
true
gap> zero_mor_model := ModelingMorphism( DAC, zero_mor );;
gap> IsEmpty( MorphismMatrix( zero_mor_model ) );
true
gap> zero_mor = ZeroMorphism( DAC, zero, zero );
true
gap> zero_mor_reinterp := ReinterpretationOfMorphism( DAC, zero, zero_mor_model, zero );;
gap> list_of_matrices = ListOfMatrices( zero_mor_reinterp );
true
gap> source := ObjectConstructor( DAC, [2,[0,2,0]] );;
gap> list_of_matrices := [ [], [ [], [] ], [] ];;
gap> mor := MorphismConstructor( DAC, source, list_of_matrices, zero );;
gap> IsWellDefinedForMorphisms( mor );
true
gap> mor_model := ModelingMorphism( DAC, mor );;
gap> MorphismMatrix( mor_model ) = [ [], [] ];
true
gap> mor_reinterp := ReinterpretationOfMorphism( DAC, source, mor_model, zero );;
gap> list_of_matrices = ListOfMatrices( mor_reinterp );
true
gap> target := ObjectConstructor( DAC, [2,[0,2,0]] );;
gap> list_of_matrices := [ [], [], [] ];;
gap> mor := MorphismConstructor( DAC, zero, list_of_matrices, target );;
gap> IsWellDefinedForMorphisms( mor );
true
gap> mor_model := ModelingMorphism( DAC, mor );;
gap> MorphismMatrix( mor_model ) = [ ];
true
gap> mor_reinterp := ReinterpretationOfMorphism( DAC, zero, mor_model, target );;
gap> list_of_matrices = ListOfMatrices( mor_reinterp );
true
gap> source := ObjectConstructor( DAC, [1,[0,1,0]] );;
gap> target := ObjectConstructor( DAC, [2,[1,1,0]] );;
gap> list_of_matrices := [ [], [ [ id_b ] ], [] ];;
gap> mor := MorphismConstructor( DAC, source, list_of_matrices, target );;
gap> IsWellDefinedForMorphisms( mor );
true
gap> mor_model := ModelingMorphism( DAC, mor );;
gap> zero_mor := ZeroMorphism( L, b, a );;
gap> MorphismMatrix( mor_model ) = [ [ zero_mor, id_b ] ];
true
gap> mor_reinterp := ReinterpretationOfMorphism( DAC, source, mor_model, target );;
gap> list_of_matrices = ListOfMatrices( mor_reinterp );
true
gap> source := ObjectConstructor( DAC, [2,[1,1,0]] );;
gap> target := ObjectConstructor( DAC, [2,[0,2,0]] );;
gap> list_of_matrices := [ [ [] ], [ [ id_b, id_b ] ], [] ];;
gap> mor := MorphismConstructor( DAC, source, list_of_matrices, target );;
gap> IsWellDefinedForMorphisms( mor );
true
gap> mor_model := ModelingMorphism( DAC, mor );;
gap> zero_mor := ZeroMorphism( L, a, b );;
gap> MorphismMatrix( mor_model ) = [ [ zero_mor, zero_mor ], [ id_b, id_b ] ];
true
gap> mor_reinterp := ReinterpretationOfMorphism( DAC, source, mor_model, target );;
gap> list_of_matrices = ListOfMatrices( mor_reinterp );
true
gap> source := ObjectConstructor( DAC, [1,[0,1,0]] );;
gap> target := ObjectConstructor( DAC, [1,[1,0,0]] );;
gap> list_of_matrices := [ [], [ [] ], [] ];;
gap> mor := MorphismConstructor( DAC, source, list_of_matrices, target );;
gap> IsWellDefinedForMorphisms( mor );
true
gap> mor_model := ModelingMorphism( DAC, mor );;
gap> zero_mor := ZeroMorphism( L, b, a );;
gap> MorphismMatrix( mor_model ) = [ [ zero_mor] ];
true
gap> mor_reinterp := ReinterpretationOfMorphism( DAC, source, mor_model, target );;
gap> list_of_matrices = ListOfMatrices( mor_reinterp );
true
gap> #########################################
> # Attributes and Operators
> #########################################
> 
> Length( UnderlyingObjectList( a1_reinterp ) ) = 5;
true
gap> a1_reinterp[4];
<An object in LinearClosure( FiniteSkeletalDiscreteCategory( [ 1 .. 3 ] ) )>
gap> mor_reinterp[2];
[ [ ] ]
gap> D[1] / L / DAC;;
gap> id_a / DAC;;
gap> [ D[1] / L, D[2] / L, D[1] / L ] / DAC;;
gap> [ matrix_a, matrix_b, matrix_c ] / DAC;;

#
gap> STOP_TEST("AdditiveClosureOfObjectFiniteDisconnectedCategoryTest", 1);
