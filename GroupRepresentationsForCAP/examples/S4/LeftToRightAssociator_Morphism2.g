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

CompareAssociatorMorphisms :=
  function( A, B, C )
    local timing_statistics, check_equality, ABC, permutations_product_permcat, permutations_sgreps, permutations_repg, nr_support, components, permutations_mor_sgreps, equal, equal2;
    
    timing_statistics := ValueOption( "timing_statistics" );
    check_equality := ValueOption( "check_equality" );
    
    ABC := TensorProductOnObjects( A, TensorProductOnObjects( B, C ) );
    
    if timing_statistics then
        StartTimer( "SGREPS_Associator_2_Morphism_multiplicity" );
    fi;
    
    permutations_product_permcat := SGREPS_Associator_2_Morphism_multiplicity( product_insmat, A, B, C, ABC );
    
    if timing_statistics then
        StopTimer( "SGREPS_Associator_2_Morphism_multiplicity" );
        DisplayTimer( "SGREPS_Associator_2_Morphism_multiplicity" );
        ResetTimer( "SGREPS_Associator_2_Morphism_multiplicity" );
        Print( "\n" );
        StartTimer( "SGREPS_Associator_2_Morphism" );
    fi;
    
    permutations_sgreps := SGREPS_Associator_2_Morphism( sgreps,
                                                         ConvertObjectToSGReps( A ),
                                                         ConvertObjectToSGReps( B ),
                                                         ConvertObjectToSGReps( C ),
                                                         ConvertObjectToSGReps( ABC ) );
    
    if timing_statistics then
        StopTimer( "SGREPS_Associator_2_Morphism" );
        DisplayTimer( "SGREPS_Associator_2_Morphism" );
        ResetTimer( "SGREPS_Associator_2_Morphism" );
        Print( "\n" );
        StartTimer( "SEMISIMPLECATEGORY_Associator_2_Morphism" );
    fi;
    
    permutations_repg := SEMISIMPLECATEGORY_Associator_2_Morphism( ConvertObjectToRepG( A ),
                                                                   ConvertObjectToRepG( B ),
                                                                   ConvertObjectToRepG( C ),
                                                                   ConvertObjectToRepG( ABC ) );
    
    if timing_statistics then
        StopTimer( "SEMISIMPLECATEGORY_Associator_2_Morphism" );
        DisplayTimer( "SEMISIMPLECATEGORY_Associator_2_Morphism" );
        ResetTimer( "SEMISIMPLECATEGORY_Associator_2_Morphism" );
        Print( "\n" );
    fi;
    
    # Checking equality takes too long for larger inputs because of
    # the conversion from matrices to permutations.
    if check_equality then
        
        nr_support := NrSupport( permutations_product_permcat );
        components := Components( permutations_product_permcat );
        
        equal := ForAll( [ 1 .. nr_support ], i ->
            components[i] = PermList( permutations_sgreps[3][i] ) );
        
        equal2 := ForAll( [ 1 .. nr_support ], i ->
            components[i] = PermList( permutations_repg[i][1] ) );
        
        return equal and equal2;
        
    fi;
    
end;

CompareAssociatorMorphisms( A, B, C : timing_statistics := true, check_equality := true );
# Timer SGREPS_Associator_2_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 2840 ms ( = 2840000 μs per run)
#
# Timer SGREPS_Associator_2_Morphism (stopped): started 
# 1 times with a total runtime of 760 ms ( = 760000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_2_Morphism (stopped): started 
# 1 times with a total runtime of 434 ms ( = 434000 μs per run)
# true

CompareAssociatorMorphisms( B, A, C : timing_statistics := true, check_equality := true );
# Timer SGREPS_Associator_2_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 4246 ms ( = 4246000 μs per run)
#
# Timer SGREPS_Associator_2_Morphism (stopped): started 
# 1 times with a total runtime of 948 ms ( = 948000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_2_Morphism (stopped): started 
# 1 times with a total runtime of 265 ms ( = 265000 μs per run)
# true

CompareAssociatorMorphisms( B, A, AC : timing_statistics := true, check_equality := true );
# Timer SGREPS_Associator_2_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 10169 ms ( = 10169000 μs per run)
#
# Timer SGREPS_Associator_2_Morphism (stopped): started 
# 1 times with a total runtime of 3769 ms ( = 3769000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_2_Morphism (stopped): started 
# 1 times with a total runtime of 2832 ms ( = 2832000 μs per run)
# true

CompareAssociatorMorphisms( BC, B, A : timing_statistics := true, check_equality := true );
# Timer SGREPS_Associator_2_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 10258 ms ( = 10258000 μs per run)
# 
# Timer SGREPS_Associator_2_Morphism (stopped): started 
# 1 times with a total runtime of 3855 ms ( = 3855000 μs per run)
# 
# Timer SEMISIMPLECATEGORY_Associator_2_Morphism (stopped): started 
# 1 times with a total runtime of 3168 ms ( = 3168000 μs per run)
# true

CompareAssociatorMorphisms( BC, BA, C : timing_statistics := true, check_equality := true );

CompareAssociatorMorphisms( BC, B, AC : timing_statistics := true, check_equality := true );
# Timer SGREPS_Associator_2_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 377509 ms ( = 377509000 μs per run)

CompareAssociatorMorphisms( AC, BA, C : timing_statistics := true, check_equality := true );

# @EndExample
