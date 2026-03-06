# @Chapter Skeletal Category of group representations
# @Section Examples and Tests

# @Example
LoadPackage( "GroupRepresentationsForCAP", false );
#! true

S4 := SymmetricGroup( 4 );;
RepG := RepresentationCategory( S4 );;
underlying_category := UnderlyingCategoryForSemisimpleCategory( RepG );;
field := underlying_category!.field_for_matrix_category;;
sgreps := SkeletalCategoryOfGroupRepresentations( S4, field : no_precompiled_code := true );;
product_insmat := UnderlyingProductCategoryOfInsertionMatrices( sgreps );

irr := Irr( S4 );;

# A := ObjectConstructor( product_insmat, [ 2, [1,4], [1,2] ] );;
# B := ObjectConstructor( product_insmat, [ 2, [2,3], [1,3] ] );;
# C := ObjectConstructor( product_insmat, [ 3, [2,4,5], [2,3,5] ] );;

A := ObjectConstructor( product_insmat, [ 4, [1,2,4,5], [7,8,7,4] ] );;
B := ObjectConstructor( product_insmat, [ 4, [2,3,4,5], [3,2,7,4] ] );;
C := ObjectConstructor( product_insmat, [ 3, [2,4,5], [3,5,3] ] );;

# A := ObjectConstructor( product_insmat, [ 4, [1,2,4,5], [17,8,7,14] ] );;
# B := ObjectConstructor( product_insmat, [ 4, [2,3,4,5], [3,20,17,24] ] );;
# C := ObjectConstructor( product_insmat, [ 3, [2,4,5], [3,15,13] ] );;

AC := TensorProductOnObjects( A, C);;
BC := TensorProductOnObjects( B, C);;
BA := TensorProductOnObjects( B, A);;
ABC := TensorProductOnObjects( TensorProductOnObjects( A, B ), C);;
BAC := TensorProductOnObjects( TensorProductOnObjects( B, A ), C);;
BCBAC := TensorProductOnObjects( BC, BAC );;

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

RepGMorphismToListOfPermutations :=
  function( mor_repg )
    local morphism_list_repg, i, permlist;
    
    morphism_list_repg := SemisimpleCategoryMorphismList( mor_repg );
    
    Display( "Converting matrices to listlist's" );
    i := 1;
    morphism_list_repg := 
        List( morphism_list_repg, function( pair )
            Display( i );
            i := i+1;
            # Takes too long
            return EntriesOfHomalgMatrixAsListList(
                UnderlyingMatrix( pair[1] ) );
        end );
    
    Display( "Converting listlist's into permutations" );
    i := 1;
    permlist := List( morphism_list_repg, function( l )
        Display( i );
        i := i+1;
        # Takes too long
        return Inverse( PermList( List( l, row -> Position( row, 1 ) ) ) );
    end );
    
    return permlist;
    
end;;

CompareAssociatorMorphisms :=
  function( A, B, C )
    local timing_statistics, check_equality, ABC, permutations_product_permcat, permutations_sgreps, use_factoring, permutations_repg, nr_support, components, permutations_mor_sgreps, equal, equal2;
    
    timing_statistics := ValueOption( "timing_statistics" );
    check_equality := ValueOption( "check_equality" );
    
    ABC := TensorProductOnObjects( A, TensorProductOnObjects( B, C ) );
    
    if timing_statistics then
        StartTimer( "SGREPS_Associator_567_Morphism_multiplicity" );
    fi;
    
    permutations_product_permcat := SGREPS_Associator_567_Morphism_multiplicity( product_insmat, A, B, C, ABC );
    
    if timing_statistics then
        StopTimer( "SGREPS_Associator_567_Morphism_multiplicity" );
        DisplayTimer( "SGREPS_Associator_567_Morphism_multiplicity" );
        ResetTimer( "SGREPS_Associator_567_Morphism_multiplicity" );
        Print( "\n" );
        StartTimer( "SGREPS_Associator_567_Morphism" );
    fi;
    
    permutations_sgreps := SGREPS_Associator_567_Morphism( sgreps,
                                                           ConvertObjectToSGReps( A ),
                                                           ConvertObjectToSGReps( B ),
                                                           ConvertObjectToSGReps( C ),
                                                           ConvertObjectToSGReps( ABC ) );
    
    if timing_statistics then
        StopTimer( "SGREPS_Associator_567_Morphism" );
        DisplayTimer( "SGREPS_Associator_567_Morphism" );
        ResetTimer( "SGREPS_Associator_567_Morphism" );
        Print( "\n" );
        StartTimer( "SEMISIMPLECATEGORY_Associator_567_Morphism" );
    fi;
    
    use_factoring := false;;
    permutations_repg := SEMISIMPLECATEGORY_Associator_567_Morphism( ConvertObjectToRepG( A ),
                                                                     ConvertObjectToRepG( B ),
                                                                     ConvertObjectToRepG( C ),
                                                                     ConvertObjectToRepG( ABC ),
                                                                     ConvertObjectToRepG( ABC ),
                                                                     use_factoring );
    
    if timing_statistics then
        StopTimer( "SEMISIMPLECATEGORY_Associator_567_Morphism" );
        DisplayTimer( "SEMISIMPLECATEGORY_Associator_567_Morphism" );
        ResetTimer( "SEMISIMPLECATEGORY_Associator_567_Morphism" );
        Print( "\n" );
    fi;
    
    # Checking equality takes too long for larger inputs because of
    # the conversion from matrices to permutations.
    if check_equality then
        
        nr_support := NrSupport( permutations_product_permcat );
        components := Components( permutations_product_permcat );
        
        StartTimer( "RepGMorphismToListOfPermutations" );
        
        permutations_repg := RepGMorphismToListOfPermutations( permutations_repg );
        
        StopTimer( "RepGMorphismToListOfPermutations" );
        DisplayTimer( "RepGMorphismToListOfPermutations" );
        DisplayTimer( "\n" );
        ResetTimer( "RepGMorphismToListOfPermutations" );
        
        equal := ForAll( [ 1 .. nr_support ], i ->
            components[i] = PermList( permutations_sgreps[3][i] ) );
        
        equal2 := ForAll( [ 1 .. nr_support ], i ->
                                components[i] = permutations_repg[i] );
        
        # Error( "\033[31m[Check equality]\033[0m" );
        
        return equal and equal2;
        
    fi;
    
end;

CompareAssociatorMorphisms( A, B, C : timing_statistics := true, check_equality := true );
# 1 times with a total runtime of 799 ms ( = 799000 μs per run)
#
# Timer SGREPS_Associator_567_Morphism (stopped): started 
# 1 times with a total runtime of 62 ms ( = 62000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_567_Morphism (stopped): started 
# 1 times with a total runtime of 28 ms ( = 28000 μs per run)
#
# Timer RepGMorphismToListOfPermutations (stopped): started 
# 1 times with a total runtime of 15795 ms ( = 15795000 μs per run)
#
# true

CompareAssociatorMorphisms( A, A, C : timing_statistics := true, check_equality := true );
# Timer SGREPS_Associator_567_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 791 ms ( = 791000 μs per run)
#
# Timer SGREPS_Associator_567_Morphism (stopped): started 
# 1 times with a total runtime of 64 ms ( = 64000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_567_Morphism (stopped): started 
# 1 times with a total runtime of 27 ms ( = 27000 μs per run)
#
# Timer RepGMorphismToListOfPermutations (stopped): started 
# 1 times with a total runtime of 9125 ms ( = 9125000 μs per run)
#
# true

CompareAssociatorMorphisms( B, A, C : timing_statistics := true, check_equality := false );
# Timer SGREPS_Associator_567_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 6151 ms ( = 6151000 μs per run)
#
# Timer SGREPS_Associator_567_Morphism (stopped): started 
# 1 times with a total runtime of 549 ms ( = 549000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_567_Morphism (stopped): started 
# 1 times with a total runtime of 345 ms ( = 345000 μs per run)

CompareAssociatorMorphisms( B, A, AC : timing_statistics := true, check_equality := false );
# Timer SGREPS_Associator_567_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 15739 ms ( = 15739000 μs per run)
#
# SEMISIMPLECATEGORY_Associator_567_Morphism reached CertainRows after ~1 minute

CompareAssociatorMorphisms( BC, B, A : timing_statistics := true, check_equality := false );
# Timer SGREPS_Associator_567_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 17528 ms ( = 17528000 μs per run)
#
# Timer SGREPS_Associator_567_Morphism (stopped): started 
# 1 times with a total runtime of 3876 ms ( = 3876000 μs per run)
#
# SEMISIMPLECATEGORY_Associator_567_Morphism reached CertainRows after ~3 seconds

CompareAssociatorMorphisms( BC, BA, C : timing_statistics := true, check_equality := false );

CompareAssociatorMorphisms( BC, B, AC : timing_statistics := true, check_equality := false );
# Timer SGREPS_Associator_567_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 38185 ms ( = 38185000 μs per run)
#
# SEMISIMPLECATEGORY_Associator_567_Morphism reached CertainRows after ~1.10 minutes

CompareAssociatorMorphisms( AC, BA, C : timing_statistics := true, check_equality := false );

# @EndExample
