# @Chapter Skeletal Category of group representations
# @Section Examples and Tests

# @Example
LoadPackage( "GroupRepresentationsForCAP", false );
# true

# homalgIOMode( "debug" );

S4 := SymmetricGroup( 4 );;
irr := Irr( S4 );;
RepG := RepresentationCategory( S4 );;
QQ := UnderlyingFieldForHomalgForSemisimpleCategory( RepG );;

sgreps := SkeletalCategoryOfGroupRepresentations( S4,
                                                  QQ
                                                  : no_precompiled_code := true );;

product_insmat := UnderlyingProductCategoryOfInsertionMatrices( sgreps );;

product_perms := UnderlyingProductCategoryOfPermutationCategory( product_insmat );;
F_product_permcat := IsomorphismFromCoreToProductCategoryOfPermutationCategory( product_insmat );;

S1 := ObjectConstructor( product_insmat, [ 1, [1], [1] ] );;
S2 := ObjectConstructor( product_insmat, [ 1, [2], [1] ] );;
S3 := ObjectConstructor( product_insmat, [ 1, [3], [1] ] );;
S4 := ObjectConstructor( product_insmat, [ 1, [4], [1] ] );;
S5 := ObjectConstructor( product_insmat, [ 1, [5], [1] ] );;
S2S3 := TensorProductOnObjects( S2, S3 );;
S4S5 := TensorProductOnObjects( S4, S5 );;

A := ObjectConstructor( product_insmat, [ 4, [1,2,3,4], [30,40,90,50] ] );;
B := ObjectConstructor( product_insmat, [ 3, [2,3,5], [30,10,50] ] );;
C := ObjectConstructor( product_insmat, [ 3, [1,3,4], [24,83,29] ] );;
D := ObjectConstructor( product_insmat, [ 4, [1,3,4,5], [26,37,50,103] ] );;
F := ObjectConstructor( product_insmat, [ 4, [1,2,3,4], [45,61,25,35] ] );;
G := ObjectConstructor( product_insmat, [ 4, [1,2,3,4], [20,76,25,13] ] );;
AB := TensorProductOnObjects( A, B );;
AC := TensorProductOnObjects( A, C );;
BA := TensorProductOnObjects( B, A );;
BC := TensorProductOnObjects( B, C );;
CB := TensorProductOnObjects( C, B );;
CC := TensorProductOnObjects( C, C );;
ACC := TensorProductOnObjects( A, CC );;
CBA := TensorProductOnObjects( CB, A );;

ConvertObjectToSGReps :=
  function( object )
    local nr_support, support, components, l;
    
    return ObjectConstructor( sgreps, ObjectDatum( object ) );
    
end;;

ConvertObjectToRepG :=
  function( object )
    local nr_support, support, components, l;
    
    nr_support := NrSupport( object );
    support := Support( object );
    components := Components( object );
    
    l := List( [ 1 .. nr_support ], i -> [ components[i], irr[ support[i] ] ] );
    
    return RepresentationCategoryObject( l, RepG );
    
end;;

SGRepsMorphismToListOfPermutations :=
  function( mor_sgreps )
    local morphism_list_sgreps;
    
    morphism_list_sgreps := Components( mor_sgreps );
    
    morphism_list_sgreps := 
        List( morphism_list_sgreps, mor ->
            EntriesOfHomalgMatrixAsListList( mor ) );
    
    return List( morphism_list_sgreps, l ->
        PermList( List( l, row -> Position( row, 1 ) ) ) );
    
end;;

RepGMorphismToListOfPermutations :=
  function( mor_repg )
    local morphism_list_repg;
    
    morphism_list_repg := SemisimpleCategoryMorphismList( mor_repg );
    
    morphism_list_repg := 
        List( morphism_list_repg, pair ->
            EntriesOfHomalgMatrixAsListList(
                UnderlyingMatrix( pair[1] ) ) );
    
    return List( morphism_list_repg, l ->
        Inverse( PermList( List( l, row -> Position( row, 1 ) ) ) ) );
    
end;;

CheckEqualityAll :=
  function( mor_mults_sgreps, mor_sgreps, mor_functional_sgreps, mor_repg )
    local nr_support, components_mor_mults, components_mor_sgreps, components_mor_sgreps_functional, morphism_list_repg, entries, components_mor_repg, equal, equal2, equal3;
    
    # Convert all the different morphism data to a list of components.
    
    nr_support := NrSupport( mor_mults_sgreps );
    components_mor_mults := Components( mor_mults_sgreps );
    components_mor_sgreps := Components( mor_sgreps );
    components_mor_sgreps_functional := Components( mor_functional_sgreps );
    components_mor_repg :=
        List( SemisimpleCategoryMorphismList( mor_repg ), pair ->
            UnderlyingMatrix( pair[1] ) );
    
    equal := ForAll( [ 1 .. nr_support ], i ->
        components_mor_mults[i] = components_mor_sgreps[i] );
    
    equal2 := ForAll( [ 1 .. nr_support ], i ->
        components_mor_mults[i] = components_mor_sgreps_functional[i] );
    
    equal3 := ForAll( [ 1 .. nr_support ], i ->
        components_mor_mults[i] = components_mor_repg[i] );
    
    # Error( "\033[31m[CheckEqualityAll]\033[0m" );
    
    return equal and equal2 and equal3;
    
end;;

CompareLeftDistributivityExpandings :=
  function( factor, L, multiplicities )
    local check_equality, L_expanded_with_multiplicities, source, target, mor_mults_sgreps, L_sgreps, factor_sgreps, source_sgreps, target_sgreps, mor_sgreps, mor_functional_sgreps, L_repg, factor_repg, source_repg, target_repg, mor_repg;
    
    check_equality := ValueOption( "check_equality" );
    
    L_expanded_with_multiplicities :=
        Concatenation( List( [ 1 .. Length( multiplicities ) ], i ->
            ListWithIdenticalEntries( multiplicities[i], L[i] ) ) );
    
    source := TensorProduct( DirectProduct( L_expanded_with_multiplicities ), factor );
    target := source;
    
    factor_sgreps := ConvertObjectToSGReps( factor );
    source_sgreps := ConvertObjectToSGReps( source );
    target_sgreps := ConvertObjectToSGReps( target );
    
    factor_repg := ConvertObjectToRepG( factor );
    source_repg := ConvertObjectToRepG( source );
    target_repg := ConvertObjectToRepG( target );
    
    L_sgreps := List( L, ConvertObjectToSGReps );
    L_sgreps := Concatenation( List( [ 1 .. Length( multiplicities ) ], i ->
        ListWithIdenticalEntries( multiplicities[i], L_sgreps[i] ) ) );
    
    L_repg := List( L, ConvertObjectToRepG );
    L_repg := Concatenation( List( [ 1 .. Length( multiplicities ) ], i ->
        ListWithIdenticalEntries( multiplicities[i], L_repg[i] ) ) );
    
    StartTimer( "LeftDistExpandingWithMultiplicities" );
    
    mor_mults_sgreps := LeftDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_insmat, source, factor, L, multiplicities, target );
    
    # Display( "Applying functor" );
    
    # Option 1:
    mor_mults_sgreps := FunctorProdInsMatIntoSGRepsUsingCertainCols( sgreps, mor_mults_sgreps );
    
    # Option 2:
    # mor_mults_product_permcat := ApplyFunctor( F_product_permcat, mor_mults_sgreps );
    # Display( "Inverting" );
    # mor_mults_product_permcat := InverseForMorphisms( mor_mults_product_permcat );
    # Display( "Turning permutations into matrices" );
    # mor_mults_sgreps := EmbeddingProductCatOfPermutationCatIntoSGRepsOnMorphism( sgreps, mor_mults_product_permcat );
    
    StopTimer( "LeftDistExpandingWithMultiplicities" );
    DisplayTimer( "LeftDistExpandingWithMultiplicities" );
    ResetTimer( "LeftDistExpandingWithMultiplicities" );
    Print( "\n" );
    
    StartTimer( "SGReps_LeftDistExpanding" );
    mor_sgreps := LeftDistributivityExpandingWithGivenObjects( sgreps, source_sgreps, factor_sgreps, L_sgreps, target_sgreps );
    StopTimer( "SGReps_LeftDistExpanding" );
    DisplayTimer( "SGReps_LeftDistExpanding" );
    ResetTimer( "SGReps_LeftDistExpanding" );
    Print( "\n" );
    
    StartTimer( "SGReps_functional_LeftDistExpanding" );
    mor_functional_sgreps := SGREPS_LeftDistributivityExpandingPermutation( sgreps, factor_sgreps, L_sgreps, target_sgreps );
    mor_functional_sgreps := SGREPS_FunctorFromMorphismPermutationsToMorphismMatrices( sgreps, source_sgreps, mor_functional_sgreps, target_sgreps );
    StopTimer( "SGReps_functional_LeftDistExpanding" );
    DisplayTimer( "SGReps_functional_LeftDistExpanding" );
    ResetTimer( "SGReps_functional_LeftDistExpanding" );
    Print( "\n" );
    
    StartTimer( "RepG_LeftDistExpanding" );
    mor_repg := LeftDistributivityExpandingWithGivenObjects( source_repg, factor_repg, L_repg, target_repg );
    StopTimer( "RepG_LeftDistExpanding" );
    DisplayTimer( "RepG_LeftDistExpanding" );
    ResetTimer( "RepG_LeftDistExpanding" );
    Print( "\n" );
    
    # Error( "\033[31m[182]\033[0m" );
    
    if check_equality then
        
        return CheckEqualityAll( mor_mults_sgreps, mor_sgreps, mor_functional_sgreps, mor_repg );
        
    fi;
    
end;;

CompareMultiplicityToNonMultiplicity :=
  function( factor, L, multiplicities )
    local check_equality, L_expanded_with_multiplicities, source, target, mor_mults_sgreps, L_sgreps, factor_sgreps, source_sgreps, target_sgreps, mor_sgreps, mor_functional_sgreps, nr_support, components_mor_mults_sgreps, components_mor_functional_sgreps, equal;
    
    L_expanded_with_multiplicities :=
        Concatenation( List( [ 1 .. Length( multiplicities ) ], i ->
            ListWithIdenticalEntries( multiplicities[i], L[i] ) ) );
    
    source := TensorProduct( DirectProduct( L_expanded_with_multiplicities ), factor );
    target := source;
    
    factor_sgreps := ConvertObjectToSGReps( factor );
    source_sgreps := ConvertObjectToSGReps( source );
    target_sgreps := ConvertObjectToSGReps( target );
    
    L_sgreps := List( L, ConvertObjectToSGReps );
    L_sgreps := Concatenation( List( [ 1 .. Length( multiplicities ) ], i ->
        ListWithIdenticalEntries( multiplicities[i], L_sgreps[i] ) ) );
    
    StartTimer( "LeftDistExpandingWithMultiplicities" );
    mor_mults_sgreps := LeftDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_insmat, source, factor, L, multiplicities, target );
    # Display( "Applying functor" );
    # mor_mults_product_permcat := ApplyFunctor( F_product_permcat, mor_mults_sgreps );
    StopTimer( "LeftDistExpandingWithMultiplicities" );
    DisplayTimer( "LeftDistExpandingWithMultiplicities" );
    ResetTimer( "LeftDistExpandingWithMultiplicities" );
    Print( "\n" );
    
    StartTimer( "SGReps_functional_LeftDistExpanding" );
    mor_functional_sgreps := SGREPS_LeftDistributivityExpandingPermutation( sgreps, factor_sgreps, L_sgreps, target_sgreps );
    StopTimer( "SGReps_functional_LeftDistExpanding" );
    DisplayTimer( "SGReps_functional_LeftDistExpanding" );
    ResetTimer( "SGReps_functional_LeftDistExpanding" );
    Print( "\n" );
    
    # Error( "\033[31m[CompareMultiplicityToNonMultiplicity]\033[0m" );
    
    nr_support := NrSupport( mor_mults_sgreps );
    components_mor_mults_sgreps := Components( mor_mults_sgreps );
    components_mor_functional_sgreps := mor_functional_sgreps[3];
    
    # Error( "\033[31m[CheckEqualityAll]\033[0m" );
    
end;;

#################################################
# Compare only multiplicity to non-mulitiplicity
#################################################

L := [ S2, S3 ];;
multiplicities := [ 1, 1 ];;
factor := S3;;
CompareMultiplicityToNonMultiplicity( factor, L, multiplicities );;

L := [ S2, S3, S5 ];;
multiplicities := [ 60, 29, 105 ];;
factor := S4;;
CompareMultiplicityToNonMultiplicity( factor, L, multiplicities );;

L := [ S2S3, S4S5, S5 ];;
multiplicities := [ 6, 2, 10 ];;
factor := S2S3;;
CompareMultiplicityToNonMultiplicity( factor, L, multiplicities );;

L := [ B, C ];;
multiplicities := [ 4, 5 ];;
factor := A;;
CompareMultiplicityToNonMultiplicity( factor, L, multiplicities );;

L := [ B, C, F, D ];;
multiplicities := [ 40, 50, 4, 78 ];;
factor := A;;
CompareMultiplicityToNonMultiplicity( factor, L, multiplicities );;

L := [ B, C, D, F, G ];;
multiplicities := [ 64, 24, 80, 40, 20 ];;
factor := A;;
CompareMultiplicityToNonMultiplicity( factor, L, multiplicities );;

L := [ B, C, D, F, G, A, C, D ];;
multiplicities := [ 64, 24, 80, 40, 20, 56, 94, 78 ];;
factor := A;;
CompareMultiplicityToNonMultiplicity( factor, L, multiplicities );;

#################################################
# Compare all
#################################################

L := [ S2, S3 ];;
multiplicities := [ 1, 1 ];;
factor := S3;;
CompareLeftDistributivityExpandings( factor, L, multiplicities : check_equality := true );
#! true

L := [ S2, S3, S5 ];;
multiplicities := [ 6, 2, 10 ];;
factor := S1;;
CompareLeftDistributivityExpandings( factor, L, multiplicities : check_equality := true );
#! true

L := [ S2S3, S4S5, S5 ];;
multiplicities := [ 6, 2, 10 ];;
factor := S2S3;;
CompareLeftDistributivityExpandings( factor, L, multiplicities : check_equality := true );
#! true

L := [ S2, S3, S5 ];;
multiplicities := [ 60, 29, 105 ];;
factor := S4;;
CompareLeftDistributivityExpandings( factor, L, multiplicities : check_equality := true );
#! true

L := [ B ];;
multiplicities := [ 1 ];;
factor := A;;
CompareLeftDistributivityExpandings( factor, L, multiplicities : check_equality := true );
#! true

L := [ B, C ];;
multiplicities := [ 1, 1 ];;
factor := A;;
CompareLeftDistributivityExpandings( factor, L, multiplicities : check_equality := false );;

L := [ B, C ];;
multiplicities := [ 4, 5 ];;
factor := A;;
CompareLeftDistributivityExpandings( factor, L, multiplicities : check_equality := false );;
# Timer LeftDistExpandingWithMultiplicities (stopped): started 
# 1 times with a total runtime of 44380 ms ( = 44380000 μs per run)
# 
# Timer SGReps_LeftDistExpanding (stopped): started 
# 1 times with a total runtime of 44907 ms ( = 44907000 μs per run)
# 
# Timer SGReps_functional_LeftDistExpanding (stopped): started 
# 1 times with a total runtime of 44283 ms ( = 44283000 μs per run)
# 
# Timer RepG_LeftDistExpanding (stopped): started 
# 1 times with a total runtime of 44274 ms ( = 44274000 μs per run)


L := [ B, C, B, A, C ];;
multiplicities := [ 1, 1, 1, 1, 1 ];;
factor := C;;
CompareLeftDistributivityExpandings( factor, L, multiplicities : check_equality := false );;
# Timer LeftDistExpandingWithMultiplicities (stopped): started 
# 1 times with a total runtime of 44336 ms ( = 44336000 μs per run)
# 
# Timer SGReps_LeftDistExpanding (stopped): started 
# 1 times with a total runtime of 46088 ms ( = 46088000 μs per run)
# 
# Timer SGReps_functional_LeftDistExpanding (stopped): started 
# 1 times with a total runtime of 44316 ms ( = 44316000 μs per run)
# 
# Timer RepG_LeftDistExpanding (stopped): started 
# 1 times with a total runtime of 45054 ms ( = 45054000 μs per run)


# Turning the permutations into matrices takes too long in
# the following examples.
# The permutations itself are still fast to compute.
#
# L := [ B, C, CBA, CBA, B, ACC, A, C, BC, BA, C ];;
# multiplicities := [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ];;
# factor := BC;;
# CompareLeftDistributivityExpandings( factor, L, multiplicities : check_equality := false );;
#
# L := [ B, C, D, F, G ];;
# multiplicities := [ 64, 24, 80, 40, 20 ];;
# factor := A;;
# CompareLeftDistributivityExpandings( factor, L, multiplicities : check_equality := false );;

# @EndExample
