# @Chapter Skeletal Category of group representations
# @Section Examples and Tests

# @Example
LoadPackage( "GroupRepresentationsForCAP", false );
#! true

S4 := SymmetricGroup( 4 );;

RepG := RepresentationCategory( S4 );;
is_complete_data := IsCompleteData( RepG );;
associator_data := AssociatorData( RepG );;
underlying_category := UnderlyingCategoryForSemisimpleCategory( RepG );;
field := underlying_category!.field_for_matrix_category;;
is_magma_ring := IsHomalgExternalRingInMAGMARep( field );;

sgreps := SkeletalCategoryOfGroupRepresentations( S4, field : no_precompiled_code := true );;

irr := Irr( S4 );;

A := ObjectConstructor( sgreps, [ 2, [1,4], [1,2] ] );;
B := ObjectConstructor( sgreps, [ 2, [2,3], [1,3] ] );;
C := ObjectConstructor( sgreps, [ 3, [2,4,5], [2,3,5] ] );;

# A := ObjectConstructor( sgreps, [ 4, [1,2,4,5], [7,8,7,4] ] );;
# B := ObjectConstructor( sgreps, [ 4, [2,3,4,5], [3,2,7,4] ] );;
# C := ObjectConstructor( sgreps, [ 3, [2,4,5], [3,5,3] ] );;

# A := ObjectConstructor( sgreps, [ 4, [1,2,4,5], [17,8,7,14] ] );;
# B := ObjectConstructor( sgreps, [ 4, [2,3,4,5], [3,20,17,24] ] );;
# C := ObjectConstructor( sgreps, [ 3, [2,4,5], [3,15,13] ] );;

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
    local timing_statistics, check_equality, ABC, matrices_sgreps, matrices_repg, nr_support, components, permutations_mor_sgreps, equal;
    
    timing_statistics := ValueOption( "timing_statistics" );
    check_equality := ValueOption( "check_equality" );
    
    ABC := TensorProductOnObjects( A, TensorProductOnObjects( B, C ) );
    
    if timing_statistics then
        StartTimer( "SGREPS_Associator_4_Morphism_multiplicity" );
    fi;
    
    matrices_sgreps := SGREPS_Associator_4_Morphism_multiplicity( sgreps, A, B, C, ABC );
    
    if timing_statistics then
        StopTimer( "SGREPS_Associator_4_Morphism_multiplicity" );
        DisplayTimer( "SGREPS_Associator_4_Morphism_multiplicity" );
        ResetTimer( "SGREPS_Associator_4_Morphism_multiplicity" );
        Print( "\n" );
        StartTimer( "SEMISIMPLECATEGORY_Associator_4_Morphism" );
    fi;
    
    matrices_repg := SEMISIMPLECATEGORY_Associator_4_Morphism( ConvertObjectToRepG( A ),
                                                               ConvertObjectToRepG( B ),
                                                               ConvertObjectToRepG( C ),
                                                               ConvertObjectToRepG( ABC ),
                                                               associator_data,
                                                               is_magma_ring,
                                                               is_complete_data );
    
    if timing_statistics then
        StopTimer( "SEMISIMPLECATEGORY_Associator_4_Morphism" );
        DisplayTimer( "SEMISIMPLECATEGORY_Associator_4_Morphism" );
        ResetTimer( "SEMISIMPLECATEGORY_Associator_4_Morphism" );
        Print( "\n" );
    fi;
    
    # Checking equality takes too long for larger inputs because of
    # the conversion from matrices to permutations.
    if check_equality then
        
        nr_support := NrSupport( matrices_sgreps );
        components := Components( matrices_sgreps );
        
        matrices_repg := SemisimpleCategoryMorphismList( matrices_repg );
        
        equal := ForAll( [ 1 .. nr_support ], i ->
                    components[i] = UnderlyingMatrix( matrices_repg[i][1] ) );
        
        return equal;
        
    fi;
    
end;

CompareAssociatorMorphisms( A, B, C : timing_statistics := true, check_equality := true );
# Timer SGREPS_Associator_4_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 179 ms ( = 179000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_4_Morphism (stopped): started 
# 1 times with a total runtime of 18 ms ( = 18000 μs per run)
#
# true

CompareAssociatorMorphisms( B, A, C : timing_statistics := true, check_equality := true );
# Timer SGREPS_Associator_4_Morphism_multiplicity (stopped): started 
# 1 times with a total runtime of 158 ms ( = 158000 μs per run)
#
# Timer SEMISIMPLECATEGORY_Associator_4_Morphism (stopped): started 
# 1 times with a total runtime of 18 ms ( = 18000 μs per run)
#
# true

CompareAssociatorMorphisms( B, A, AC : timing_statistics := true, check_equality := true );

# The following did not finish after 30m.
CompareAssociatorMorphisms( BC, BA, C : timing_statistics := true, check_equality := true );

CompareAssociatorMorphisms( BC, B, A : timing_statistics := true, check_equality := true );

CompareAssociatorMorphisms( BC, B, AC : timing_statistics := true, check_equality := true );

CompareAssociatorMorphisms( AC, BA, C : timing_statistics := true, check_equality := true );

# @EndExample
