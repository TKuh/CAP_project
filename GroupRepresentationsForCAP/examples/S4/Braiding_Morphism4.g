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

A := ObjectConstructor( product_kron_comon, [ 2, [1,4], [1,2] ] );;
B := ObjectConstructor( product_kron_comon, [ 2, [2,3], [1,3] ] );;
C := ObjectConstructor( product_kron_comon, [ 3, [2,4,5], [2,3,5] ] );;

# A := ObjectConstructor( product_kron_comon, [ 4, [1,2,4,5], [7,8,7,4] ] );;
# B := ObjectConstructor( product_kron_comon, [ 4, [2,3,4,5], [3,2,7,4] ] );;
# C := ObjectConstructor( product_kron_comon, [ 3, [2,4,5], [3,5,3] ] );;

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
    local nr_support, support, permutations, l;
    
    return ObjectConstructor( sgreps, ObjectDatum( object ) );
    
end;;

ConvertObjectToRepG :=
  function( object )
    local nr_support, support, permutations, l;
    
    nr_support := NrSupport( object );
    support := Support( object );
    permutations := Components( object );
    
    l := List( [ 1 .. nr_support ], i -> [ permutations[i], irr[ support[i] ] ] );
    
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

CompareBraidingMorphisms :=
  function( A, B )
    local timing_statistics, check_equality, AB, morphism_multiplicity, morphism, morphism_repg, permutations_repg, nr_support, permutations, permutations_multiplicity, permutations_mor_sgreps, equal, equal2;
    
    timing_statistics := ValueOption( "timing_statistics" );
    check_equality := ValueOption( "check_equality" );
    
    AB := TensorProductOnObjects( A, B );
    
    if timing_statistics then
        StartTimer( "SGREPS_Braiding_4_Morphism_multiplicity" );
    fi;
    
    morphism_multiplicity := SGREPS_Braiding_4_Morphism_multiplicity( product_kron_comon, A, B, AB );
    
    if timing_statistics then
        StopTimer( "SGREPS_Braiding_4_Morphism_multiplicity" );
        DisplayTimer( "SGREPS_Braiding_4_Morphism_multiplicity" );
        ResetTimer( "SGREPS_Braiding_4_Morphism_multiplicity" );
        Print( "\n" );
        StartTimer( "SGREPS_Braiding_4_Morphism" );
    fi;
    
    morphism := SGREPS_Braiding_4_Morphism( sgreps,
                                            ConvertObjectToSGReps( A ),
                                            ConvertObjectToSGReps( B ),
                                            ConvertObjectToSGReps( AB ) );
    
    if timing_statistics then
        StopTimer( "SGREPS_Braiding_4_Morphism" );
        DisplayTimer( "SGREPS_Braiding_4_Morphism" );
        ResetTimer( "SGREPS_Braiding_4_Morphism" );
        Print( "\n" );
        StartTimer( "SEMISIMPLECATEGORY_Braiding_4_Morphism" );
    fi;
    
    morphism_repg := SEMISIMPLECATEGORY_Braiding_4_Morphism( ConvertObjectToRepG( A ),
                                                             ConvertObjectToRepG( B ) );
    
    if timing_statistics then
        StopTimer( "SEMISIMPLECATEGORY_Braiding_4_Morphism" );
        DisplayTimer( "SEMISIMPLECATEGORY_Braiding_4_Morphism" );
        ResetTimer( "SEMISIMPLECATEGORY_Braiding_4_Morphism" );
        Print( "\n" );
    fi;
    
    # Checking equality takes too long for larger inputs because of
    # the conversion from matrices to permutations.
    if check_equality then
        
        nr_support := NrSupport( morphism_multiplicity );
        
        permutations_multiplicity := Components( morphism_multiplicity );
        permutations := List( morphism[3], PermList );
        permutations_repg := RepGMorphismToListOfPermutations( morphism_repg );
        
        equal := ForAll( [ 1 .. nr_support ], i ->
            permutations_multiplicity[i] = permutations[i] );
        
        equal2 := ForAll( [ 1 .. nr_support ], i ->
            permutations_multiplicity[i] = permutations_repg[i] );
        
        # Error( "\033[31m[Check equality]\033[0m" );
        
        return equal and equal2;
        
    fi;
    
end;

CompareBraidingMorphisms( A, B : timing_statistics := true, check_equality := true );

CompareBraidingMorphisms( B, A : timing_statistics := true, check_equality := true );

CompareBraidingMorphisms( B, C : timing_statistics := true, check_equality := true );

CompareBraidingMorphisms( BC, B : timing_statistics := true, check_equality := false );

CompareBraidingMorphisms( BC, BA : timing_statistics := true, check_equality := false );

CompareBraidingMorphisms( BC, BC : timing_statistics := true, check_equality := false );

CompareBraidingMorphisms( AC, BA : timing_statistics := true, check_equality := false );

# @EndExample
