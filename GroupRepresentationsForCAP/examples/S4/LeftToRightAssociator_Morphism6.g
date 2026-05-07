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
product_kron_comon := SubcategoryOfSparseProductOfKroneckerComonoids( sgreps );;

irr := Irr( S4 );;

# A := ObjectConstructor( product_kron_comon, [ 2, [1,4], [1,2] ] );;
# B := ObjectConstructor( product_kron_comon, [ 2, [2,3], [1,3] ] );;
# C := ObjectConstructor( product_kron_comon, [ 3, [2,4,5], [2,3,5] ] );;

A := ObjectConstructor( product_kron_comon, [ 4, [1,2,4,5], [7,8,7,4] ] );;
B := ObjectConstructor( product_kron_comon, [ 4, [2,3,4,5], [3,2,7,4] ] );;
C := ObjectConstructor( product_kron_comon, [ 3, [2,4,5], [3,5,3] ] );;

# A := ObjectConstructor( product_kron_comon, [ 4, [1,2,4,5], [17,8,7,14] ] );;
# B := ObjectConstructor( product_kron_comon, [ 4, [2,3,4,5], [3,20,17,24] ] );;
# C := ObjectConstructor( product_kron_comon, [ 3, [2,4,5], [3,15,13] ] );;

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
        StartTimer( "SGREPS_Associator_6_Morphism_multiplicity" );
    fi;
    
    permutations_product_permcat := SGREPS_Associator_6_Morphism_multiplicity( product_kron_comon, A, B, C, ABC );
    
    if timing_statistics then
        StopTimer( "SGREPS_Associator_6_Morphism_multiplicity" );
        DisplayTimer( "SGREPS_Associator_6_Morphism_multiplicity" );
        ResetTimer( "SGREPS_Associator_6_Morphism_multiplicity" );
        Print( "\n" );
        StartTimer( "SGREPS_Associator_6_Morphism" );
    fi;
    
    permutations_sgreps := SGREPS_Associator_6_Morphism( sgreps,
                                                         ConvertObjectToSGReps( A ),
                                                         ConvertObjectToSGReps( B ),
                                                         ConvertObjectToSGReps( C ),
                                                         ConvertObjectToSGReps( ABC ) );
    
    if timing_statistics then
        StopTimer( "SGREPS_Associator_6_Morphism" );
        DisplayTimer( "SGREPS_Associator_6_Morphism" );
        ResetTimer( "SGREPS_Associator_6_Morphism" );
        Print( "\n" );
        StartTimer( "SEMISIMPLECATEGORY_Associator_6_Morphism" );
    fi;
    
    permutations_repg := SEMISIMPLECATEGORY_Associator_6_Morphism( ConvertObjectToRepG( A ),
                                                                   ConvertObjectToRepG( B ),
                                                                   ConvertObjectToRepG( C ),
                                                                   ConvertObjectToRepG( ABC ) );
    
    if timing_statistics then
        StopTimer( "SEMISIMPLECATEGORY_Associator_6_Morphism" );
        DisplayTimer( "SEMISIMPLECATEGORY_Associator_6_Morphism" );
        ResetTimer( "SEMISIMPLECATEGORY_Associator_6_Morphism" );
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
        
        # Error( "\033[31m[Check equality]\033[0m" );
        
        return equal and equal2;
        
    fi;
    
end;

CompareAssociatorMorphisms( A, B, C : timing_statistics := true, check_equality := true );
# Timer SGREPS_Associator_6_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 1195 ms ( = 1195000 μs per run)
#
# Timer SGREPS_Associator_6_Morphism (stopped): started 
# 1 times with a total runtime of 66 ms ( = 66000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_6_Morphism (stopped): started 
# 1 times with a total runtime of 47 ms ( = 47000 μs per run)
#
# true

CompareAssociatorMorphisms( B, A, C : timing_statistics := true, check_equality := true );
# Timer SGREPS_Associator_6_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 1860 ms ( = 1860000 μs per run)
#
# Timer SGREPS_Associator_6_Morphism (stopped): started 
# 1 times with a total runtime of 120 ms ( = 120000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_6_Morphism (stopped): started 
# 1 times with a total runtime of 181 ms ( = 181000 μs per run)
#
# true

CompareAssociatorMorphisms( B, A, AC : timing_statistics := true, check_equality := true );
# Timer SGREPS_Associator_6_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 288 ms ( = 288000 μs per run)
#
# Timer SGREPS_Associator_6_Morphism (stopped): started 
# 1 times with a total runtime of 195 ms ( = 195000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_6_Morphism (stopped): started 
# 1 times with a total runtime of 211 ms ( = 211000 μs per run)
#
# true

CompareAssociatorMorphisms( BC, B, A : timing_statistics := true, check_equality := true );
# Timer SGREPS_Associator_6_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 6644 ms ( = 6644000 μs per run)
#
# Timer SGREPS_Associator_6_Morphism (stopped): started 
# 1 times with a total runtime of 1534 ms ( = 1534000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_6_Morphism (stopped): started 
# 1 times with a total runtime of 1592 ms ( = 1592000 μs per run)
#
# true

CompareAssociatorMorphisms( BC, BA, C : timing_statistics := true, check_equality := true );
# Timer SGREPS_Associator_6_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 4031 ms ( = 4031000 μs per run)
#
# Timer SGREPS_Associator_6_Morphism (stopped): started 
# 1 times with a total runtime of 4071 ms ( = 4071000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_6_Morphism (stopped): started 
# 1 times with a total runtime of 4231 ms ( = 4231000 μs per run)
#
# true

CompareAssociatorMorphisms( BC, B, AC : timing_statistics := true, check_equality := true );
# Timer SGREPS_Associator_6_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 10895 ms ( = 10895000 μs per run)
#
# Timer SGREPS_Associator_6_Morphism (stopped): started 
# 1 times with a total runtime of 3748 ms ( = 3748000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_6_Morphism (stopped): started 
# 1 times with a total runtime of 4281 ms ( = 4281000 μs per run)
#
# true

CompareAssociatorMorphisms( AC, BA, C : timing_statistics := true, check_equality := true );
# Timer SGREPS_Associator_6_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 22238 ms ( = 22238000 μs per run)
#
# Timer SGREPS_Associator_6_Morphism (stopped): started 
# 1 times with a total runtime of 6509 ms ( = 6509000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_6_Morphism (stopped): started 
# 1 times with a total runtime of 7226 ms ( = 7226000 μs per run)
#
# true

# @EndExample
