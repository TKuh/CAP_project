# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Implementations
#

#! @Chapter Semisimple Categories

ReadPackage(
    "GroupRepresentationsForCAP",
    "gap/precompiled_categories/SparseProduct_CategoryOfPermutations_AsSubcategoryOfSkeletalGroupRepresentations_S4_precompiled.gi" );

####################################
##
## Constructors
##
####################################

##
InstallMethod( SparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations,
               [ IsList ],
               
  FunctionWithNamedArguments(
  [
    [ "no_precompiled_code", false ],
    [ "cat_of_perms_no_precompiled_code", false ],
    [ "FinalizeCategory", true ],
  ],
  function( CAP_NAMED_ARGUMENTS, irreducible_characters )
    local name, category_filter, category_object_filter, category_morphism_filter, nr_irreducible_characters, cat_of_perms, product_cat_of_perms, object_datum_type, object_datum, object_constructor, morphism_datum_type, morphism_datum, morphism_constructor, modeling_tower_object_datum, modeling_tower_object_constructor, modeling_tower_morphism_datum, modeling_tower_morphism_constructor, subcat;
    
    ##
    name := Concatenation( "Reinterp( 𝚷( ", String( Length( irreducible_characters ) ), ", CategoryOfPermutations ) )" );
    
    ##
    category_filter := IsSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations;
    category_object_filter := IsObjectInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations;
    category_morphism_filter := IsMorphismInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations;
    
    ##
    object_datum_type :=
        CapJitDataTypeOfNTupleOf( 3,
            IsBigInt,
            CapJitDataTypeOfListOf( IsBigInt ),
            CapJitDataTypeOfListOf( IsBigInt ) );
    
    ##
    object_constructor :=
      function( subcat, triple )
        local length, support, cardinalities;
        
        length := triple[1];
        support := triple[2];
        cardinalities := triple[3];
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, 0 <= length and length <= NrIrreducibleCharacters( subcat ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( support ) = length );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( cardinalities ) = length );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( [ 1 .. length ], i ->
            1 <= support[i] and support[i] <= NrIrreducibleCharacters( subcat ) ) );
        
        # The supporting integers must be strictly increasing.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( [ 1 .. length - 1 ], i ->
            support[i] < support[i+1] ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( cardinalities, cardinality -> not cardinality = 0 ) );
        
        return CreateCapCategoryObjectWithAttributes( subcat,
                       TripleOfNrSupportListOfSupportListOfCardinalitites, triple );
        
    end;
    
    ##
    object_datum := { subcat, obj } -> TripleOfNrSupportListOfSupportListOfCardinalitites( obj );
    
    ##
    morphism_datum_type :=
        CapJitDataTypeOfNTupleOf( 3,
            IsBigInt,
            CapJitDataTypeOfListOf( IsBigInt ),
            CapJitDataTypeOfListOf( IsPerm ) );
    
    ##
    morphism_constructor :=
      function( subcat, S, triple, T )
        local length, support, permutations, matrix, length_source, support_source, ranks_source, length_target, support_target, ranks_target, i, current_support, source, target, s, t;
        
        length := triple[1];
        support := triple[2];
        permutations := triple[3];
        
        length_source := NrSupport( S );
        support_source := Support( S );
        ranks_source := Components( S );
        
        length_target := NrSupport( T );
        support_target := Support( T );
        ranks_target := Components( T );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, 0 <= length and length <= NrIrreducibleCharacters( subcat ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( support ) = length );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( permutations ) = length );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, length = length_source and length = length_target );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( [ 1 .. length ], i ->
            1 <= support[i] and support[i] <= NrIrreducibleCharacters( subcat ) ) );
        
        # The supporting integers must be strictly increasing.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( [ 1 .. length - 1 ], i ->
            support[i] < support[i+1] ) );
        
        return CreateCapCategoryMorphismWithAttributes( subcat,
                    S,
                    T,
                    TripleOfNrSupportListOfSupportListOfPermutations, triple );
                    
    end;
    
    ##
    morphism_datum :=
        { subcat, phi } -> TripleOfNrSupportListOfSupportListOfPermutations( phi );
        
    ####################################
    # Modeling
    ####################################
    
    ## building the categorical tower:
    
    nr_irreducible_characters := Length( irreducible_characters );
    
    cat_of_perms :=
        CategoryOfPermutations(
            : no_precompiled_code := CAP_NAMED_ARGUMENTS.cat_of_perms_no_precompiled_code,
              FinalizeCategory := true );
    
    product_cat_of_perms :=
        SparseProductOfCategoryOfPermutations(
            nr_irreducible_characters,
            cat_of_perms
            : FinalizeCategory := true );
    
    ## From the raw object data to the object in the modeling category.
    modeling_tower_object_constructor :=
      function( subcat, triple )
        local product_cat_of_perms, cat_of_perms, nr_support, support, cardinalities, components;
        
        product_cat_of_perms := ModelingCategory( subcat );
        
        cat_of_perms := UnderlyingCategoryOfPermutations( product_cat_of_perms );
        
        nr_support := triple[1];
        support := triple[2];
        cardinalities := triple[3];
        
        components :=
            List( [ 1 .. nr_support ], n ->
                ObjectConstructor( cat_of_perms, cardinalities[n] ) );
        
        return ObjectConstructor( product_cat_of_perms, NTuple( 3, nr_support, support, components ) );
        
    end;
    
    ## From the object in the modeling category to the raw object data.
    modeling_tower_object_datum :=
      function( subcat, object )
        local nr_support, support, components, cardinalities;
        
        nr_support := NrSupport( object );
        support := Support( object );
        components := Components( object );
        
        cardinalities :=
            List( [ 1 .. nr_support ], n ->
                Cardinality( components[n] ) );
                
        return NTuple( 3, nr_support, support, cardinalities );
        
    end;
    
    ## From the raw morphism data to the morphism in the modeling category.
    modeling_tower_morphism_constructor :=
      function( subcat, source, triple, target )
        local product_cat_of_perms, cat_of_perms, nr_support, support, permutations, cardinalities, morphisms;
        
        product_cat_of_perms := ModelingCategory( subcat );
        
        cat_of_perms := UnderlyingCategoryOfPermutations( product_cat_of_perms );
        
        nr_support := triple[1];
        support := triple[2];
        permutations := triple[3];
        
        cardinalities := Components( source );
        
        morphisms :=
            List( [ 1 .. nr_support ], n ->
                MorphismConstructor( cat_of_perms,
                    cardinalities[n],
                    permutations[n],
                    cardinalities[n] ) );
        
        return MorphismConstructor( product_cat_of_perms,
                    source,
                    NTuple( 3, nr_support, support, morphisms ),
                    target );
        
    end;
    
    ## From the morphism in the modeling category to the raw morphism data
    modeling_tower_morphism_datum :=
      function( subcat, morphism )
        local nr_support, support, morphisms, permutations;
        
        nr_support := NrSupport( morphism );
        support := Support( morphism );
        morphisms := Components( morphism );
        
        permutations :=
            List( [ 1 .. nr_support ], n ->
                UnderlyingPermutation( morphisms[n] ) );
        
        return NTuple( 3, nr_support, support, permutations );
        
    end;
    
    subcat :=
        ReinterpretationOfCategory( product_cat_of_perms,
            rec( name := name,
                 category_filter := category_filter,
                 category_object_filter := category_object_filter,
                 category_morphism_filter := category_morphism_filter,
                 object_constructor := object_constructor,
                 object_datum := object_datum,
                 object_datum_type := object_datum_type,
                 morphism_constructor := morphism_constructor,
                 morphism_datum := morphism_datum,
                 morphism_datum_type := morphism_datum_type,
                 modeling_tower_object_constructor := modeling_tower_object_constructor,
                 modeling_tower_object_datum := modeling_tower_object_datum,
                 modeling_tower_morphism_constructor := modeling_tower_morphism_constructor,
                 modeling_tower_morphism_datum := modeling_tower_morphism_datum,
                 only_primitive_operations := true, )
            : FinalizeCategory := false );
            
    # DeactivateCachingOfCategory( subcat );
    
    # CapCategorySwitchLogicOff( subcat );
    
    SetNrIrreducibleCharacters( subcat, nr_irreducible_characters );
    
    SetUnderlyingIrreducibleCharacters( subcat, irreducible_characters );
    
    Append( subcat!.compiler_hints.category_attribute_names,
        [ "NrIrreducibleCharacters",
          "UnderlyingIrreducibleCharacters" ] );
    
    ## See AddTensorProductOnObjects in
    ## SkeletalCategoryOfGroupRepresentations.gi
    ##
    ## DirectSum -> DirectProduct
    AddTensorProductOnObjects( subcat,
      function( subcat, object_1, object_2 )
        local product_cat_of_perms, cat_of_perms, model_1, model_2, nr_support_1, nr_support_2, support_1, support_2, components_1, components_2, product;
        
        product_cat_of_perms := ModelingCategory( subcat );
        
        cat_of_perms := UnderlyingCategoryOfPermutations( product_cat_of_perms );
        
        model_1 := ModelingObject( subcat, object_1 );
        model_2 := ModelingObject( subcat, object_2 );
        
        nr_support_1 := NrSupport( model_1 );
        nr_support_2 := NrSupport( model_2 );
        
        support_1 := Support( model_1 );
        support_2 := Support( model_2 );
        
        components_1 := Components( model_1 );
        components_2 := Components( model_2 );
        
        product :=
            DirectProduct( subcat, List( [ 1 .. nr_support_1 ], i ->
                DirectProduct( subcat, List( [ 1 .. nr_support_2 ], function( j )
                    local multiplicity_of_product, decomposition, decomposition_nr_support, decomposition_support, decomposition_components, result;
                    
                    multiplicity_of_product :=
                        TensorProductOnObjects( cat_of_perms, components_1[i], components_2[j] );
                    
                    decomposition := ProductOfCharactersAsObjectInModelingProductCategory( subcat, support_1[i], support_2[j] );
                    
                    decomposition_nr_support := NrSupport( decomposition );
                    
                    decomposition_support := Support( decomposition );
                    
                    decomposition_components := Components( decomposition );
                    
                    decomposition_components :=
                        List( [ 1 .. decomposition_nr_support ], n ->
                            TensorProductOnObjects( cat_of_perms, decomposition_components[n], multiplicity_of_product ) );
                            
                    result :=
                        ObjectConstructor( product_cat_of_perms,
                            NTuple( 3,
                                decomposition_nr_support,
                                decomposition_support,
                                decomposition_components ) );
                                
                    return ReinterpretationOfObject( subcat, result );
                    
                end ) ) ) );
                
        return product;
        
    end );
    
    if CAP_NAMED_ARGUMENTS.no_precompiled_code <> true then
        
        ADD_FUNCTIONS_FOR_SparseProduct_CategoryOfPermutations_AsSubcategoryOfSkeletalGroupRepresentations_S4_precompiled( subcat );
        
    fi;
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        
        Finalize( subcat );
        
    fi;
    
    return subcat;
    
end ) );

####################################
##
## Attributes
##
####################################

InstallMethodForCompilerForCAP( NrSupport,
                                [ IsObjectInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations ],
                                
  function( object )
    
    return TripleOfNrSupportListOfSupportListOfCardinalitites( object )[1];
    
end );

InstallMethodForCompilerForCAP( NrSupport,
                                [ IsMorphismInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations ],
                                
  function( morphism )
    
    return TripleOfNrSupportListOfSupportListOfPermutations( morphism )[1];
    
end );

InstallMethodForCompilerForCAP( Support,
                                [ IsObjectInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations ],
                                
  function( object )
    
    return TripleOfNrSupportListOfSupportListOfCardinalitites( object )[2];
    
end );

InstallMethodForCompilerForCAP( Support,
                                [ IsMorphismInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations ],
                                
  function( morphism )
    
    return TripleOfNrSupportListOfSupportListOfPermutations( morphism )[2];
    
end );

InstallMethodForCompilerForCAP( Components,
                                [ IsObjectInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations ],
                                
  function( object )
    
    return TripleOfNrSupportListOfSupportListOfCardinalitites( object )[3];
    
end );

InstallMethodForCompilerForCAP( Components,
                                [ IsMorphismInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations ],
                                
  function( morphism )
    
    return TripleOfNrSupportListOfSupportListOfPermutations( morphism )[3];
    
end );

####################################
##
## Operations
##
####################################

InstallMethodForCompilerForCAP( Component,
                                [ IsObjectInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations,
                                  IsBigInt ],
                                
  function( object, i )
    local support, components;
    
    #% CAP_JIT_DROP_NEXT_STATEMENT
    Assert( 0, 1 <= i and i <= NrIrreducibleCharacters( CapCategory( object ) ) );
    
    support := Support( object );
    
    components := Components( object );
    
    return [ [ BigInt( 0 ) ], components{ Positions( support, i ) } ][ 1 + BooleanToInteger( i in support ) ][1];
    
end );

InstallMethodForCompilerForCAP( Component,
                                [ IsMorphismInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations,
                                  IsBigInt ],
                                
  function( morphism, i )
    local support, permutations;
    
    #% CAP_JIT_DROP_NEXT_STATEMENT
    Assert( 0, 1 <= i and i <= NrIrreducibleCharacters( CapCategory( morphism ) ) );
    
    support := Support( morphism );
    
    permutations := Components( morphism );
    
    # TODO: CapJitTypedExpression
    return [ [ ( ) ], permutations{ Positions( support, i ) } ][ 1 + BooleanToInteger( i in support ) ][1];
    
end );

####################################
##
## Global functions
##
####################################

InstallGlobalFunction( PRODUCT_OF_CATEGORY_OF_PERMUTATIONS_AS_SUBCAT_TensorProductProductOfMorphismWithIdentityWithGivenTensorProducts,
  function( subcat, source, morphism, identity, target )
    local product_cat_of_perms, cat_of_perms, irreducible_characters, morphism_model, morphism_nr_support, morphism_support, morphism_components, identity_model, identity_nr_support, identity_support, identity_components, source_model, source_nr_support, source_support, source_components, components, permutations;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    product_cat_of_perms := ModelingCategory( subcat );
    cat_of_perms := UnderlyingCategoryOfPermutations( product_cat_of_perms );
    
    irreducible_characters := UnderlyingIrreducibleCharacters( subcat );
    
    morphism_model := ModelingMorphism( subcat, morphism );
    morphism_nr_support := NrSupport( morphism_model );
    morphism_support := Support( morphism_model );
    morphism_components := Components( morphism_model );
    
    identity_model := ModelingMorphism( subcat, identity );
    identity_nr_support := NrSupport( identity_model );
    identity_support := Support( identity_model );
    identity_components := Components( identity_model );
    
    source_model := ModelingObject( subcat, source );
    source_nr_support := NrSupport( source_model );
    source_support := Support( source_model );
    source_components := Components( source_model );
    
    components := List( [ 1 .. source_nr_support ], function( k )
        local morphisms, cardinality_diagram, cardinality;
        
        # TODO: document with math symbols.
        morphisms :=
            Concatenation( List( [ 1 .. morphism_nr_support ], function( i )
                local morphism_i, source_morphism_i;
                
                morphism_i := morphism_components[i];
                
                source_morphism_i := Source( morphism_i );
                
                return List( [ 1 .. identity_nr_support ], function( j )
                    local n_ijk, identity_j, source_identity_j_times_n_ijk, cardinality;
                    
                    n_ijk := SGREPS_ScalarProduct( irreducible_characters,
                                                   source_support[k],
                                                   morphism_support[i],
                                                   identity_support[j] );
                    
                    # if n_ijk > 0 then
                    
                    n_ijk := ObjectConstructor( cat_of_perms, n_ijk );
                    
                    identity_j := identity_components[j];
                    
                    source_identity_j_times_n_ijk := TensorProductOnObjects( cat_of_perms, Source( identity_j ), n_ijk );
                    
                    cardinality := TensorProductOnObjects( cat_of_perms, source_morphism_i, source_identity_j_times_n_ijk );
                    
                    return CATEGORY_OF_PERMUTATIONS_TensorProductProductOfMorphismWithIdentityWithGivenTensorProducts( cat_of_perms,
                                cardinality,
                                morphism_i,
                                IdentityMorphism( cat_of_perms, source_identity_j_times_n_ijk ),
                                cardinality );
                    
                    # fi;
                    
                end );
                
            end ) );
                
        cardinality_diagram := List( morphisms, Source );
        cardinality := source_components[k];
        
        return DirectProductFunctorialWithGivenDirectProducts( cat_of_perms,
                    cardinality,
                    cardinality_diagram,
                    morphisms,
                    cardinality_diagram,
                    cardinality );
        
    end );
    
    permutations := List( components, UnderlyingPermutation );
    
    return MorphismConstructor( subcat,
                source,
                NTuple( 3, source_nr_support, source_support, permutations ),
                source );
    
end );

InstallGlobalFunction( PRODUCT_OF_CATEGORY_OF_PERMUTATIONS_AS_SUBCAT_TensorProductProductOfIdentityWithMorphismWithGivenProducts,
  function( subcat, source, identity, morphism, target )
    local product_cat_of_perms, cat_of_perms, irreducible_characters, morphism_model, morphism_nr_support, morphism_support, morphism_components, identity_model, identity_nr_support, identity_support, identity_components, source_model, source_nr_support, source_support, source_components, components, permutations;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    product_cat_of_perms := ModelingCategory( subcat );
    cat_of_perms := UnderlyingCategoryOfPermutations( product_cat_of_perms );
    
    irreducible_characters := UnderlyingIrreducibleCharacters( subcat );
    
    morphism_model := ModelingMorphism( subcat, morphism );
    morphism_nr_support := NrSupport( morphism_model );
    morphism_support := Support( morphism_model );
    morphism_components := Components( morphism_model );
    
    identity_model := ModelingMorphism( subcat, identity );
    identity_nr_support := NrSupport( identity_model );
    identity_support := Support( identity_model );
    identity_components := Components( identity_model );
    
    source_model := ModelingObject( subcat, source );
    source_nr_support := NrSupport( source_model );
    source_support := Support( source_model );
    source_components := Components( source_model );
    
    components := List( [ 1 .. source_nr_support ], function( k )
        local morphisms, cardinality_diagram, cardinality;
        
        # TODO: document with math symbols.
        morphisms :=
            Concatenation( List( [ 1 .. identity_nr_support ], function( i )
                local identity_i, source_identity_i;
                
                identity_i := identity_components[i];
                
                source_identity_i := Source( identity_i );
                
                return List( [ 1 .. morphism_nr_support ], function( j )
                    local n_ijk, morphism_j, cardinality_right, morphism_j_times_id_nijk, cardinality;
                    
                    n_ijk := SGREPS_ScalarProduct( irreducible_characters,
                                                   source_support[k],
                                                   identity_support[i],
                                                   morphism_support[j] );
                    
                    # if n_ijk > 0 then
                    
                    n_ijk := ObjectConstructor( cat_of_perms, n_ijk );
                    
                    morphism_j := morphism_components[j];
                    
                    cardinality_right := TensorProductOnObjects( cat_of_perms, Source( morphism_j ), n_ijk );
                    
                    morphism_j_times_id_nijk := CATEGORY_OF_PERMUTATIONS_TensorProductProductOfMorphismWithIdentityWithGivenTensorProducts( cat_of_perms,
                                            cardinality_right,
                                            morphism_j,
                                            IdentityMorphism( cat_of_perms, n_ijk ),
                                            cardinality_right );
                    
                    cardinality := TensorProductOnObjects( cat_of_perms, source_identity_i, Source( morphism_j_times_id_nijk ) );
                    
                    return CATEGORY_OF_PERMUTATIONS_TensorProductProductOfIdentityWithMorphismWithGivenTensorProducts( cat_of_perms,
                                cardinality,
                                identity_i,
                                morphism_j_times_id_nijk,
                                cardinality );
                    
                    # fi;
                    
                end );
                
            end ) );
                
        cardinality_diagram := List( morphisms, Source );
        cardinality := source_components[k];
        
        return DirectProductFunctorialWithGivenDirectProducts( cat_of_perms,
                    cardinality,
                    cardinality_diagram,
                    morphisms,
                    cardinality_diagram,
                    cardinality );
        
    end );
    
    permutations := List( components, UnderlyingPermutation );
    
    return MorphismConstructor( subcat,
                source,
                NTuple( 3, source_nr_support, source_support, permutations ),
                source );
    
end );

InstallMethodForCompilerForCAP( ProductOfCharactersAsObjectInModelingProductCategory,
                                [ IsSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations, IsBigInt, IsBigInt ],
                                
  function( subcat, i, j )
    local product_cat_of_perms, cat_of_perms, irreducible_characters, scalar_product, support, components;
    
    product_cat_of_perms := ModelingCategory( subcat );
    cat_of_perms := UnderlyingCategoryOfPermutations( product_cat_of_perms );
    
    irreducible_characters := UnderlyingIrreducibleCharacters( subcat );
    
    scalar_product := List( [ 1 .. NrIrreducibleCharacters( subcat ) ], k ->
        SGREPS_ScalarProduct( irreducible_characters, k, i, j ) );
        
    support := Filtered( [ 1 .. Length( irreducible_characters ) ], i ->
        not IsZero( scalar_product[i] ) );
        
    components :=
        List( scalar_product{ support }, character ->
            ObjectConstructor( cat_of_perms, character ) );
            
    return ObjectConstructor( product_cat_of_perms, NTuple( 3, Length( support ), support, components ) );
    
end );

####################################
##
## View & Display
##
####################################

##
InstallMethod( DisplayString,
               [ IsObjectInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations ],
               
  object -> String( TripleOfNrSupportListOfSupportListOfCardinalitites( object ) )
  
);

##
InstallMethod( Display,
               [ IsMorphismInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations ],
               
  function( morphism )
    local length, support, permutations, components_source, i;
    
    length := NrSupport( morphism );
    support := Support( morphism );
    permutations := Components( morphism );
    
    components_source := Components( Source( morphism ) );
    
    for i in [ 1 .. length ] do
        
        Print( Concatenation( "Component: (", String( support[i] ), ")\n" ) );
        
        Print( "\n" );
        
        Print( components_source[i], " ⱶ", String( permutations[i] ), "→ ", components_source[i] );
        
        Print( "\n------------------------\n" );
        
    od;
    
end );

