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

A := ObjectConstructor( product_insmat, [ 2, [1,4], [1,2] ] );;
B := ObjectConstructor( product_insmat, [ 2, [2,3], [1,3] ] );;
C := ObjectConstructor( product_insmat, [ 3, [2,4,5], [2,3,5] ] );;

# A := ObjectConstructor( product_insmat, [ 4, [1,2,4,5], [7,8,7,4] ] );;
# B := ObjectConstructor( product_insmat, [ 4, [2,3,4,5], [3,2,7,4] ] );;
# C := ObjectConstructor( product_insmat, [ 3, [2,4,5], [3,5,3] ] );;

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
    local timing_statistics, check_equality, ABC, permutations_product_permcat, permutations_sgreps, permutations_repg, nr_support, components, permutations_mor_sgreps, equal, equal2;
    
    timing_statistics := ValueOption( "timing_statistics" );
    check_equality := ValueOption( "check_equality" );
    
    ABC := TensorProductOnObjects( A, TensorProductOnObjects( B, C ) );
    
    if timing_statistics then
        StartTimer( "SGREPS_Associator_123_Morphism_multiplicity" );
    fi;
    
    permutations_product_permcat := SGREPS_Associator_123_Morphism_multiplicity( product_insmat, A, B, C, ABC );
    
    if timing_statistics then
        StopTimer( "SGREPS_Associator_123_Morphism_multiplicity" );
        DisplayTimer( "SGREPS_Associator_123_Morphism_multiplicity" );
        ResetTimer( "SGREPS_Associator_123_Morphism_multiplicity" );
        Print( "\n" );
        StartTimer( "SGREPS_Associator_123_Morphism" );
    fi;
    
    permutations_sgreps := SGREPS_Associator_123_Morphism( sgreps,
                                                         ConvertObjectToSGReps( A ),
                                                         ConvertObjectToSGReps( B ),
                                                         ConvertObjectToSGReps( C ),
                                                         ConvertObjectToSGReps( ABC ) );
    
    if timing_statistics then
        StopTimer( "SGREPS_Associator_123_Morphism" );
        DisplayTimer( "SGREPS_Associator_123_Morphism" );
        ResetTimer( "SGREPS_Associator_123_Morphism" );
        Print( "\n" );
        StartTimer( "SEMISIMPLECATEGORY_Associator_123_Morphism" );
    fi;
    
    permutations_repg := SEMISIMPLECATEGORY_Associator_123_Morphism( ConvertObjectToRepG( A ),
                                                                   ConvertObjectToRepG( B ),
                                                                   ConvertObjectToRepG( C ),
                                                                   ConvertObjectToRepG( ABC ),
                                                                   ConvertObjectToRepG( ABC ) );
    
    if timing_statistics then
        StopTimer( "SEMISIMPLECATEGORY_Associator_123_Morphism" );
        DisplayTimer( "SEMISIMPLECATEGORY_Associator_123_Morphism" );
        ResetTimer( "SEMISIMPLECATEGORY_Associator_123_Morphism" );
        Print( "\n" );
    fi;
    
    # Checking equality takes too long for larger inputs because of
    # the conversion from matrices to permutations.
    if check_equality then
        
        nr_support := NrSupport( permutations_product_permcat );
        components := Components( permutations_product_permcat );
        
        permutations_repg := RepGMorphismToListOfPermutations( permutations_repg );
        
        equal := ForAll( [ 1 .. nr_support ], i ->
            components[i] = PermList( permutations_sgreps[3][i] ) );
        
        equal2 := ForAll( [ 1 .. nr_support ], i ->
                                components[i] = permutations_repg[i] );
        
        # Error( "\033[31m[Check equality]\033[0m" );
        
        return equal and equal2;
        
    fi;
    
end;

CompareAssociatorMorphisms( A, B, C : timing_statistics := true, check_equality := true );
# Timer SGREPS_Associator_123_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 806 ms ( = 806000 μs per run)
#
# Timer SGREPS_Associator_123_Morphism (stopped): started 
# 1 times with a total runtime of 47 ms ( = 47000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_123_Morphism (stopped): started 
# 1 times with a total runtime of 31 ms ( = 31000 μs per run)
#
# true

CompareAssociatorMorphisms( B, A, C : timing_statistics := true, check_equality := true );
# Timer SGREPS_Associator_123_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 845 ms ( = 845000 μs per run)
#
# Timer SGREPS_Associator_123_Morphism (stopped): started 
# 1 times with a total runtime of 47 ms ( = 47000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_123_Morphism (stopped): started 
#k1 times with a total runtime of 30 ms ( = 30000 μs per run)
#
# true

CompareAssociatorMorphisms( B, A, AC : timing_statistics := true, check_equality := true );
# Timer SGREPS_Associator_123_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 2337 ms ( = 2337000 μs per run)
#
# Timer SGREPS_Associator_123_Morphism (stopped): started 
# 1 times with a total runtime of 326 ms ( = 326000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_123_Morphism (stopped): started 
# 1 times with a total runtime of 333 ms ( = 333000 μs per run)

CompareAssociatorMorphisms( BC, B, A : timing_statistics := true, check_equality := false );
# Timer SGREPS_Associator_123_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 2397 ms ( = 2397000 μs per run)
#
# Timer SGREPS_Associator_123_Morphism (stopped): started 
# 1 times with a total runtime of 309 ms ( = 309000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_123_Morphism (stopped): started 
# 1 times with a total runtime of 163 ms ( = 163000 μs per run)

CompareAssociatorMorphisms( BC, BA, C : timing_statistics := true, check_equality := false );
# Timer SGREPS_Associator_123_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 7779 ms ( = 7779000 μs per run)
#
# Timer SGREPS_Associator_123_Morphism (stopped): started 
# 1 times with a total runtime of 869 ms ( = 869000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_123_Morphism (stopped): started 
# 1 times with a total runtime of 2696 ms ( = 2696000 μs per run)
#

CompareAssociatorMorphisms( BC, B, AC : timing_statistics := true, check_equality := false );
# Timer SGREPS_Associator_123_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 8669 ms ( = 8669000 μs per run)
#
# Timer SGREPS_Associator_123_Morphism (stopped): started 
# 1 times with a total runtime of 1201 ms ( = 1201000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_123_Morphism (stopped): started 
# 1 times with a total runtime of 3155 ms ( = 3155000 μs per run)

CompareAssociatorMorphisms( AC, BA, C : timing_statistics := true, check_equality := false );
# Timer SGREPS_Associator_123_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 13731 ms ( = 13731000 μs per run)
#
# Timer SGREPS_Associator_123_Morphism (stopped): started 
# 1 times with a total runtime of 1063 ms ( = 1063000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_123_Morphism (stopped): started 
# 1 times with a total runtime of 1747 ms ( = 1747000 μs per run)

# @EndExample
