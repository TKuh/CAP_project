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

ConvertObjectToRepG :=
  function( object )
    local nr_support, support, components, l;
    
    nr_support := NrSupport( object );
    support := Support( object );
    components := Components( object );
    
    l := List( [ 1 .. nr_support ], i -> [ components[i], irr[ support[i] ] ] );
    
    return RepresentationCategoryObject( l, RepG );
    
end;;

CompareBraidingMorphisms :=
  function( A, B )
    local timing_statistics, AB, morphism_sgreps_multiplicity, morphism_sgreps, matrices_repg, nr_support, components, components_multiplicity, permutations_mor_sgreps, equal, equal2;
    
    timing_statistics := ValueOption( "timing_statistics" );
    
    AB := TensorProductOnObjects( A, B );
    
    if timing_statistics then
        StartTimer( "SGREPS_Braiding_3_Morphism_multiplicity" );
    fi;
    
    morphism_sgreps_multiplicity := SGREPS_Braiding_3_Morphism_multiplicity( sgreps, A, B, AB );
    
    if timing_statistics then
        StopTimer( "SGREPS_Braiding_3_Morphism_multiplicity" );
        DisplayTimer( "SGREPS_Braiding_3_Morphism_multiplicity" );
        ResetTimer( "SGREPS_Braiding_3_Morphism_multiplicity" );
        Print( "\n" );
        StartTimer( "SGREPS_Braiding_3_Morphism" );
    fi;
    
    morphism_sgreps := SGREPS_Braiding_3_Morphism( sgreps, A, B, AB );
    
    if timing_statistics then
        StopTimer( "SGREPS_Braiding_3_Morphism" );
        DisplayTimer( "SGREPS_Braiding_3_Morphism" );
        ResetTimer( "SGREPS_Braiding_3_Morphism" );
        Print( "\n" );
        StartTimer( "SEMISIMPLECATEGORY_Braiding_3_Morphism" );
    fi;
    
    matrices_repg := SEMISIMPLECATEGORY_Braiding_3_Morphism( ConvertObjectToRepG( A ),
                                                             ConvertObjectToRepG( B ) );
    
    if timing_statistics then
        StopTimer( "SEMISIMPLECATEGORY_Braiding_3_Morphism" );
        DisplayTimer( "SEMISIMPLECATEGORY_Braiding_3_Morphism" );
        ResetTimer( "SEMISIMPLECATEGORY_Braiding_3_Morphism" );
        Print( "\n" );
    fi;
    
    nr_support := NrSupport( morphism_sgreps_multiplicity );
    components_multiplicity := Components( morphism_sgreps_multiplicity );
    components := Components( morphism_sgreps );
    matrices_repg := SemisimpleCategoryMorphismList( matrices_repg );
    
    equal := ForAll( [ 1 .. nr_support ], i ->
        components_multiplicity[i] = components[i] );
    
    equal2 := ForAll( [ 1 .. nr_support ], i ->
        components_multiplicity[i] = UnderlyingMatrix( matrices_repg[i][1] ) );
    
    # Error( "\033[31m[Check equality]\033[0m" );
    
    return equal and equal2;
    
end;

CompareBraidingMorphisms( A, B : timing_statistics := true );

CompareBraidingMorphisms( B, A : timing_statistics := true );

CompareBraidingMorphisms( B, C : timing_statistics := true );

CompareBraidingMorphisms( BC, B : timing_statistics := true );

CompareBraidingMorphisms( BC, BA : timing_statistics := true );

CompareBraidingMorphisms( BC, BC : timing_statistics := true );

CompareBraidingMorphisms( AC, BA : timing_statistics := true );

# @EndExample
