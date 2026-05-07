# @Chapter Skeletal Category of group representations
# @Section Examples and Tests

# @Example
LoadPackage( "GroupRepresentationsForCAP", false );
#! true

G := AlternatingGroup( 4 );;
RepG := RepresentationCategory( G );;
underlying_category := UnderlyingCategoryForSemisimpleCategory( RepG );;
field := underlying_category!.field_for_matrix_category;;
sgreps := SkeletalCategoryOfGroupRepresentations( G, field : no_precompiled_code := true );;
product_kron_comon := SubcategoryOfSparseProductOfKroneckerComonoids( sgreps );;

irr := Irr( G );;

A := ObjectConstructor( sgreps, [ 2, [1,4], [1,2] ] );;
B := ObjectConstructor( sgreps, [ 2, [2,3], [1,3] ] );;
C := ObjectConstructor( sgreps, [ 2, [3,4], [3,5] ] );;

# A := ObjectConstructor( sgreps, [ 3, [1,2,4], [7,8,7] ] );;
# B := ObjectConstructor( sgreps, [ 3, [2,3,4], [3,2,7] ] );;
# C := ObjectConstructor( sgreps, [ 2, [3,4], [5,3] ] );;

# A := ObjectConstructor( sgreps, [ 3, [1,2,4], [17,8,7] ] );;
# B := ObjectConstructor( sgreps, [ 3, [2,3,4], [3,20,17] ] );;
# C := ObjectConstructor( sgreps, [ 2, [3,4], [3,15] ] );;

AC := TensorProductOnObjects( A, C);;
BC := TensorProductOnObjects( B, C);;
BA := TensorProductOnObjects( B, A);;
ABC := TensorProductOnObjects( TensorProductOnObjects( A, B ), C);;
BAC := TensorProductOnObjects( TensorProductOnObjects( B, A ), C);;
BCBAC := TensorProductOnObjects( BC, BAC );;

ConvertObjectToProductKronComon :=
  function( object )
    local nr_support, support, matrices, l;
    
    return ObjectConstructor( product_kron_comon, ObjectDatum( object ) );
    
end;;

ConvertObjectToSGReps :=
  function( object )
    local nr_support, support, matrices, l;
    
    return ObjectConstructor( sgreps, ObjectDatum( object ) );
    
end;;

ConvertObjectToRepG :=
  function( object )
    local nr_support, support, matrices, l;
    
    nr_support := NrSupport( object );
    support := Support( object );
    matrices := Components( object );
    
    l := List( [ 1 .. nr_support ], i -> [ matrices[i], irr[ support[i] ] ] );
    
    return RepresentationCategoryObject( l, RepG );
    
end;;

CompareCoevalutionMorphisms :=
  function( A )
    local timing_statistics, check_equality, unit, AV, AAV, morphism_1_multiplicity, morphism_23_multiplicity, morphism_multiplicity, morphism_1, morphism_23, morphism, morphism_repg, matrices_repg, nr_support, matrices, matrices_multiplicity, permutations_mor_sgreps, equal, equal2;
    
    timing_statistics := ValueOption( "timing_statistics" );
    check_equality := ValueOption( "check_equality" );
    
    unit := TensorUnit( sgreps );
    AV := DualOnObjects( A );
    AAV := TensorProductOnObjects( A, AV );
    
    if timing_statistics then
        StartTimer( "SGREPS_Coevaluation_multiplicity" );
    fi;
    
    morphism_1_multiplicity := SGREPS_CoevaluationForDual_1_Morphism_multiplicity( sgreps, unit, A, AAV );
    morphism_23_multiplicity := SGREPS_CoevaluationForDual_23_Morphism_multiplicity( product_kron_comon,
                                    ConvertObjectToProductKronComon( A ),
                                    ConvertObjectToProductKronComon( AV ),
                                    ConvertObjectToProductKronComon( AAV ) );
    morphism_23_multiplicity := EmbeddingProductCatOfPermutationCatIntoSGRepsOnMorphism( sgreps, morphism_23_multiplicity );
    morphism_multiplicity := PreCompose(  morphism_1_multiplicity, morphism_23_multiplicity );
    
    if timing_statistics then
        StopTimer( "SGREPS_Coevaluation_multiplicity" );
        DisplayTimer( "SGREPS_Coevaluation_multiplicity" );
        ResetTimer( "SGREPS_Coevaluation_multiplicity" );
        Print( "\n" );
        StartTimer( "SGREPS_Coevaluation" );
    fi;
    
    morphism_1 := SGREPS_CoevaluationForDual_1_Morphism( sgreps, unit, A, AAV );
    morphism_23 := SGREPS_CoevaluationForDual_23_Morphism( sgreps, A, AAV );
    morphism := PreCompose( morphism_1, morphism_23 );
    
    if timing_statistics then
        StopTimer( "SGREPS_Coevaluation" );
        DisplayTimer( "SGREPS_Coevaluation" );
        ResetTimer( "SGREPS_Coevaluation" );
        Print( "\n" );
        StartTimer( "SEMISIMPLECATEGORY_Coevaluation" );
    fi;
    
    morphism_repg := CoevaluationForDualWithGivenTensorProduct(
                        ConvertObjectToRepG( unit ),
                        ConvertObjectToRepG( A ),
                        ConvertObjectToRepG( AAV ) );
    
    if timing_statistics then
        StopTimer( "SEMISIMPLECATEGORY_Coevaluation" );
        DisplayTimer( "SEMISIMPLECATEGORY_Coevaluation" );
        ResetTimer( "SEMISIMPLECATEGORY_Coevaluation" );
        Print( "\n" );
    fi;
    
    # Checking equality takes too long for larger inputs because of
    # the conversion from permutations to matrices.
    if check_equality then
        
        nr_support := NrSupport( morphism_multiplicity );
        
        matrices_multiplicity := Components( morphism_multiplicity );
        matrices := Components( morphism );
        matrices_repg := SemisimpleCategoryMorphismList( morphism_repg );
        
        equal := ForAll( [ 1 .. nr_support ], i ->
            matrices_multiplicity[i] = matrices[i] );
        
        equal2 := ForAll( [ 1 .. nr_support ], i ->
            matrices_multiplicity[i] = UnderlyingMatrix( matrices_repg[i][1] ) );
        
        # Error( "\033[31m[Check equality]\033[0m" );
        
        return equal and equal2;
        
    fi;
    
end;

CompareCoevalutionMorphisms( A : timing_statistics := true, check_equality := true );

CompareCoevalutionMorphisms( B : timing_statistics := true, check_equality := true );

CompareCoevalutionMorphisms( BC : timing_statistics := true, check_equality := true );

CompareCoevalutionMorphisms( BC : timing_statistics := true, check_equality := false );

CompareCoevalutionMorphisms( AC : timing_statistics := true, check_equality := false );

# @EndExample
