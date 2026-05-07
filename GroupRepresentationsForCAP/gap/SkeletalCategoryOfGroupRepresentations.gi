# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Implementations
#

#! @Chapter Semisimple Categories

ReadPackage( "GroupRepresentationsForCAP", "gap/precompiled_categories/SkeletalCategoryOfGroupRepresentations_S4_Q_precompiled.gi" );

####################################
##
## Constructors
##
####################################

##
InstallMethod( SkeletalCategoryOfGroupRepresentations,
               [ IsGroup, IsFieldForHomalg ],
               
  FunctionWithNamedArguments(
  [
    [ "no_precompiled_code", false ],
    [ "FinalizeCategory", true ],
  ],
  function( CAP_NAMED_ARGUMENTS, G, splitting_field )
    local name, category_filter, category_object_filter, category_morphism_filter, character_table, irreducible_characters, nr_irreducible_characters, category_of_rows, direct_sum_category, decompose_product_of_characters, object_datum_type, object_datum, object_constructor, morphism_datum_type, morphism_datum, morphism_constructor, modeling_tower_object_datum, modeling_tower_object_constructor, modeling_tower_morphism_datum, modeling_tower_morphism_constructor, product_kron_comon, embedding_product_kron_comon, product_permcat, embedding_product_permcat, sgreps;
    
    Assert( 0, HasCharacteristic( splitting_field ) and Characteristic( splitting_field ) = 0 );
    
    ##
    name :=
        Concatenation( "SkeletalGroupRepresentations( ",
                       String( G ),
                       ", ",
                       String( splitting_field ),
                       " )" );
                       
    ##
    category_filter := IsSkeletalCategoryOfGroupRepresentations;
    category_object_filter := IsObjectInSkeletalCategoryOfGroupRepresentations;
    category_morphism_filter := IsMorphismInSkeletalCategoryOfGroupRepresentations;
    
    ##
    object_datum_type :=
        CapJitDataTypeOfNTupleOf( 3,
            IsBigInt,
            CapJitDataTypeOfListOf( IsBigInt ),
            CapJitDataTypeOfListOf( IsBigInt ) );
            
    ##
    object_constructor :=
      function( sgreps, triple )
        local length, support, ranks;
        
        length := triple[1];
        support := triple[2];
        ranks := triple[3];
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, 0 <= length and length <= NrIrreducibleCharacters( sgreps ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( support ) = length );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( ranks ) = length );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( [ 1 .. length ], i ->
            1 <= support[i] and support[i] <= NrIrreducibleCharacters( sgreps ) ) );
        
        # The supporting integers must be strictly increasing.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( [ 1 .. length - 1 ], i ->
            support[i] < support[i+1] ) );
        
        # Assert( 0, ForAll( ranks, rank -> not 0 = rank ) );
        
        return CreateCapCategoryObjectWithAttributes( sgreps,
                       TripleOfNrSupportListOfSupportListOfRanks, triple );
                       
    end;
    
    ##
    object_datum := { sgreps, obj } -> TripleOfNrSupportListOfSupportListOfRanks( obj );
    
    ##
    morphism_datum_type :=
        CapJitDataTypeOfNTupleOf( 3,
            IsBigInt,
            CapJitDataTypeOfListOf( IsBigInt ),
            CapJitDataTypeOfListOf( rec( filter := IsHomalgMatrix, ring := splitting_field ) ) );
            
    ##
    morphism_constructor :=
      function( sgreps, S, triple, T )
        local splitting_field, length, support, matrices, matrix, length_source, support_source, ranks_source, length_target, support_target, ranks_target, i, current_support, source, target, s, t;
        
        splitting_field := UnderlyingSplittingField( sgreps );
        
        length := triple[1];
        support := triple[2];
        matrices := triple[3];
        
        length_source := NrSupport( S );
        support_source := Support( S );
        ranks_source := Components( S );
        
        length_target := NrSupport( T );
        support_target := Support( T );
        ranks_target := Components( T );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, 0 <= length and length <= NrIrreducibleCharacters( sgreps ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( support ) = length );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( matrices ) = length );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( [ 1 .. length ], i ->
            1 <= support[i] and support[i] <= NrIrreducibleCharacters( sgreps ) ) );
            
        # The supporting integers must be strictly increasing.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( [ 1 .. length - 1 ], i ->
            support[i] < support[i+1] ) );
        
        # Assert( 0, ForAll( matrices, matrix ->
        #   ( not 0 = NrRows( matrix ) ) and ( not 0 = NrCols( matrix ) ) ) );
        
        # For all matrices in 'matrices',
        # the source and target at a support must be equal to the objects
        # in 'S' and 'T' at the same support.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        for i in [ 1.. length ] do
            
            current_support := support[i];
            
            matrix := matrices[i];
            
            source := NrRows( matrix );
            target := NrCols( matrix );
            
            Assert( 0, source = Component( S, current_support ) and
                       target = Component( T, current_support ) );
                       
        od;
        
        # For any object s in 'S' there must be a morphism m
        # at the same support with Source( m ) = s.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        for i in [ 1.. length_source ] do
            
            current_support := support_source[i];
            
            s := ranks_source[i];
            
            # Get the matrix at support i or a 0x0 matrix.
            matrix := [ [ HomalgZeroMatrix( 0, 0, splitting_field ) ], matrices{ Positions( support, current_support ) } ][ 1 + BooleanToInteger( current_support in support ) ][1];
            
            source := NrRows( matrix );
            
            Assert( 0, s = source );
            
        od;
        
        # For any object t in 'T' there must be a morphism m
        # at the same support with Target( m ) = t.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        for i in [ 1.. length_target ] do
            
            current_support := support_target[i];
            
            t := ranks_target[i];
            
            # Get the morphism at support i or a 0x0 morphism.
            matrix := [ [ HomalgZeroMatrix( 0, 0, splitting_field ) ], matrices{ Positions( support, current_support ) } ][ 1 + BooleanToInteger( current_support in support ) ][1];
            
            target := NrCols( matrix );
            
            Assert( 0, t = target );
            
        od;
        
        return CreateCapCategoryMorphismWithAttributes( sgreps,
                    S,
                    T,
                    TripleOfNrSupportListOfSupportListOfMatrices, triple );
                    
    end;
    
    ##
    morphism_datum := { sgreps, phi } -> TripleOfNrSupportListOfSupportListOfMatrices( phi );
    
    ####################################
    # Modeling
    ####################################
    
    character_table := CharacterTable( G );
    
    irreducible_characters := Irr( character_table );
    
    nr_irreducible_characters := Length( irreducible_characters );
    
    ## building the categorical tower:
    
    category_of_rows :=
        CategoryOfRows(
            splitting_field
            : no_precompiled_code := false,
              FinalizeCategory := true );
              
    direct_sum_category :=
        DirectSumOfAdditiveCategory(
            nr_irreducible_characters,
            category_of_rows
            : no_precompiled_code := false,
              FinalizeCategory := true );
              
    ## From the raw object data to the object in the modeling category.
    modeling_tower_object_constructor :=
      function( sgreps, triple )
        local direct_sum_category, category_of_rows, nr_support, support, ranks, objects_rows;
        
        direct_sum_category := ModelingCategory( sgreps );
        
        category_of_rows := UnderlyingAdditiveCategory( direct_sum_category );
        
        nr_support := triple[1];
        support := triple[2];
        ranks := triple[3];
        
        # Turn the integer ranks into objects of category_of_rows.
        objects_rows :=
            List( [ 1 .. nr_support ], n ->
                ObjectConstructor( category_of_rows, ranks[n] ) );
                
        return ObjectConstructor( direct_sum_category, NTuple( 3, nr_support, support, objects_rows ) );
        
    end;
    
    ## From the object in the modeling category to the raw object data.
    modeling_tower_object_datum :=
      function( sgreps, object )
        local nr_support, support, objects_rows, ranks;
        
        nr_support := NrSupport( object );
        support := Support( object );
        objects_rows := Components( object );
        
        # Turn the objects of category_of_rows into integers.
        ranks :=
            List( [ 1 .. nr_support ], n ->
                RankOfObject( objects_rows[n] ) );
                
        return NTuple( 3, nr_support, support, ranks );
        
    end;
    
    ## From the raw morphism data to the morphism in the modeling category.
    modeling_tower_morphism_constructor :=
      function( sgreps, source, triple, target )
        local direct_sum_category, category_of_rows, nr_support, support, matrices, morphisms_rows;
        
        direct_sum_category := ModelingCategory( sgreps );
        
        category_of_rows := UnderlyingAdditiveCategory( direct_sum_category );
        
        nr_support := triple[1];
        support := triple[2];
        matrices := triple[3];
        
        # Turn the Homalg matrices into morphisms of category_of_rows.
        morphisms_rows :=
            List( [ 1 .. nr_support ], n ->
                AsCategoryOfRowsMorphism( category_of_rows, matrices[n] ) );
                
        return MorphismConstructor(
                    direct_sum_category,
                    source,
                    NTuple( 3, nr_support, support, morphisms_rows ),
                    target );
                    
    end;
    
    ## From the morphism in the modeling category to the raw morphism data
    modeling_tower_morphism_datum :=
      function( sgreps, morphism )
        local nr_support, support, morphisms_rows, matrices;
        
        nr_support := NrSupport( morphism );
        support := Support( morphism );
        morphisms_rows := Components( morphism );
        
        # Turn the morphisms of category_of_rows into Homalg matrices.
        matrices :=
            List( [ 1 .. nr_support ], n ->
                UnderlyingMatrix( morphisms_rows[n] ) );
                
        return NTuple( 3, nr_support, support, matrices );
        
    end;
    
    sgreps :=
        ReinterpretationOfCategory( direct_sum_category,
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
    
    product_kron_comon :=
        SubcategoryOfSkeletalCategoryOfGroupRepresentationsOfSparseProductOfKroneckerComonoids(
            irreducible_characters
            : no_precompiled_code := CAP_NAMED_ARGUMENTS.no_precompiled_code,
              FinalizeCategory := true );
    
    embedding_product_kron_comon := CapFunctor( Concatenation( "Embedding of ",
                                              Name( product_kron_comon ),
                                              " ) into ",
                                              Name( sgreps ) ),
                                     product_kron_comon,
                                     sgreps );
    
    # TODO: the object and morphism functions of a functor need to have the
    #       source and target categories of the functor as arguments.
    #       Right now, the following can't compile, because we need to
    #       pull `sgreps` from the global variable.
    #       It instead needs to be passed as an argument.
    AddObjectFunction( embedding_product_kron_comon,
      # function( source_cat, object, target_cat )
      function( object )
        
        # return ObjectConstructor( target_cat,
        return ObjectConstructor( sgreps,
                                  TripleOfNrSupportListOfSupportListOfNumberElements( object ) );
        
    end );
    
    # AddMorphismFunction( embedding_product_kron_comon,
    #   function( source_cat, source, morphism, target, target_cat )
    #
    #     # TODO: either `FunctorProdInsMatIntoSGRepsUsingUnionOfCols` or
    #     #              `FunctorProdInsMatIntoSGRepsUsingCertainCols`.
    #
    # end );
    
    product_permcat := UnderlyingProductCategoryOfPermutationCategory( product_kron_comon );
    
    embedding_product_permcat := CapFunctor( Concatenation( "Embedding of ",
                                                            Name( product_permcat ),
                                                            " ) into ",
                                                            Name( sgreps ) ),
                                             product_permcat,
                                             sgreps );
    
    # TODO: the object and morphism functions of a functor need to have the
    #       source and target categories of the functor as arguments.
    #       Right now, the following can't compile, because we need to
    #       pull `sgreps` from the global variable.
    #       It instead needs to be passed as an argument.
    # AddObjectFunction( embedding_product_permcat,
    #   function( source_cat, object, target_cat )
    #
    #     return ObjectConstructor( target_cat,
    #                               TripleOfNrSupportListOfSupportListOfCardinalitites( object ) );
    #
    # end );
    
    # AddMorphismFunction( embedding_product_permcat,
    #   function( source_cat, source, morphism, target, target_cat )
    #
    #     # TODO
    #
    # end );
    
    # DeactivateCachingOfCategory( sgreps );
    
    # CapCategorySwitchLogicOff( sgreps );
    
    SetIsRigidSymmetricClosedMonoidalCategory( sgreps, true );
    
    SetUnderlyingGroup( sgreps, G );
    
    SetUnderlyingSplittingField( sgreps, splitting_field );
    
    SetNrIrreducibleCharacters( sgreps, nr_irreducible_characters );
    
    SetUnderlyingIrreducibleCharacters( sgreps, irreducible_characters );
    
    SetUnderlyingCharacterTable( sgreps, character_table );
    
    SetIndexOfTrivialCharacterInListOfIrreducibleCharacters( sgreps, SGREPS_IndexOfTrivialCharacter( sgreps ) );
    
    SetAssociatorData( sgreps, AssociatorsOnIrreduciblesFromDatabase( G ) );
    
    SetSubcategoryOfSparseProductOfKroneckerComonoids( sgreps, product_kron_comon );
    
    SetEmbeddingOfSparseProductOfKroneckerComonoids( sgreps, embedding_product_kron_comon );
    
    SetEmbeddingOfProductCategoryOfPermutationCategory( sgreps, embedding_product_permcat );
    
    Append( sgreps!.compiler_hints.category_attribute_names,
        [ "UnderlyingSplittingField",
          "UnderlyingGroup",
          "UnderlyingCharacterTable",
          "UnderlyingIrreducibleCharacters",
          "IndexOfTrivialCharacterInListOfIrreducibleCharacters",
          "NrIrreducibleCharacters",
          "SubcategoryOfSparseProductOfKroneckerComonoids",
          "EmbeddingOfSparseProductOfKroneckerComonoids",
          "EmbeddingOfProductCategoryOfPermutationCategory" ] );
    
    INSTALL_FUNCTIONS_FOR_SKELETAL_CATEGORY_OF_GROUP_REPRESENTATIONS(
        sgreps, irreducible_characters, nr_irreducible_characters );
    
    if CAP_NAMED_ARGUMENTS.no_precompiled_code <> true then
        
        # Using the S₄ with ℚ is general enough for many operations including TensorProduct.
        ADD_FUNCTIONS_FOR_SkeletalCategoryOfGroupRepresentations_S4_Q_precompiled( sgreps );
        
    fi;
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        
        Finalize( sgreps );
        
    fi;
    
    return sgreps;
    
end ) );

####################################
##
## Basic operations
##
####################################

InstallGlobalFunction( INSTALL_FUNCTIONS_FOR_SKELETAL_CATEGORY_OF_GROUP_REPRESENTATIONS,
  
  function( sgreps, irreducible_characters, nr_irreducible_characters )
    local decompose_product_of_characters, left_distributivity_expanding_permutation, right_distributivity_expanding_permutation, right_distributivity_function, left_distributivity_function, KroneckerProductOfPermutationWithIdentityFromRight, KroneckerProductOfPermutationWithIdentityFromLeft, TensorProductOfMorphismPermutationsWithIdentityMorphismFromRight, TensorProductOfMorphismPermutationsWithIdentityMorphismFromLeft, DirectSumForPermutationLists, distributivity_expanding_for_triple, distributivity_factoring_for_triple;
    
    ####################################
    # Monoidal structure
    ####################################
    
    ##
    AddTensorUnit( sgreps,
      function( sgreps )
        local unit_index;
        
        unit_index := IndexOfTrivialCharacterInListOfIrreducibleCharacters( sgreps );
        
        return ObjectConstructor( sgreps, NTuple( 3, 1, [ unit_index ], [ 1 ] ) );
        
    end );
    
    # Sebastian's PhD. thesis construction I.3.47.
    AddLeftUnitorWithGivenTensorProduct( sgreps,
      function( sgreps, object, tensor_product )
        
        return IdentityMorphism( sgreps, object );
        
    end );
    
    # Sebastian's PhD. thesis construction I.3.47.
    AddRightUnitorWithGivenTensorProduct( sgreps,
      function( sgreps, object, tensor_product )
        
        return IdentityMorphism( sgreps, object );
        
    end );
    
    # Sebastian's PhD. thesis construction I.3.12.
    AddTensorProductOnObjects( sgreps,
      function( sgreps, object_1, object_2 )
        local direct_sum_category, category_of_rows, irreducible_characters, model_1, model_2, nr_support_1, nr_support_2, support_1, support_2, components_1, components_2, product;
        
        direct_sum_category := ModelingCategory( sgreps );
        
        category_of_rows := UnderlyingAdditiveCategory( direct_sum_category );
        
        irreducible_characters := UnderlyingIrreducibleCharacters( sgreps );
        
        model_1 := ModelingObject( sgreps, object_1 );
        nr_support_1 := NrSupport( model_1 );
        support_1 := Support( model_1 );
        components_1 := Components( model_1 );
        
        model_2 := ModelingObject( sgreps, object_2 );
        nr_support_2 := NrSupport( model_2 );
        support_2 := Support( model_2 );
        components_2 := Components( model_2 );
        
        # Example in S4:
        #
        #   (χ₁⊕2χ₄)·(χ₂⊕3χ₃)
        # = [(χ₁·χ₂) ⊕ (χ₁·3χ₃)] ⊕ [(2χ₄·χ₂) ⊕ (2χ₄·3χ₃)]
        # = [(χ₁·χ₂) ⊕ 3(χ₁·χ₃)] ⊕ [2(χ₄·χ₂) ⊕ 6(χ₄·χ₃)]
        # = [ (χ₄)   ⊕   3(χ₃) ] ⊕ [2(χ₁⊕χ₂⊕χ₃⊕χ₄) ⊕ 6(χ₂⊕χ₄)]
        # = 2χ₁⊕8χ₂⊕5χ₃⊕9χ₄
        product :=
            DirectSum( sgreps, List( [ 1 .. nr_support_1 ], i ->
                DirectSum( sgreps, List( [ 1 .. nr_support_2 ], function( j )
                    local multiplicity_of_product, decomposition, decomposition_nr_support, decomposition_support, decomposition_components, result;
                    
                    multiplicity_of_product :=
                        TensorProductOnObjects( category_of_rows, components_1[i], components_2[j] );
                    
                    decomposition := ProductOfCharactersAsObjectInModelingProductCategory( sgreps, support_1[i], support_2[j] );
                    
                    decomposition_nr_support := NrSupport( decomposition );
                    
                    decomposition_support := Support( decomposition );
                    
                    decomposition_components := Components( decomposition );
                    
                    decomposition_components :=
                        List( [ 1 .. decomposition_nr_support ], n ->
                            TensorProductOnObjects( category_of_rows, decomposition_components[n], multiplicity_of_product ) );
                    
                    result :=
                        ObjectConstructor( direct_sum_category,
                            NTuple( 3,
                                decomposition_nr_support,
                                decomposition_support,
                                decomposition_components ) );
                    
                    return ReinterpretationOfObject( sgreps, result );
                    
                end ) ) ) );
                
        return product;
        
    end );
    
    # Sebastian's PhD. thesis construction I.3.12.
    # (ɑ⊗ɣ)ₖ := ⊕ᵢ ⊕ⱼ (ɑᵢ⊗ɣⱼ⊗Iₙ₍ᵢⱼ₎ₖ)
    AddTensorProductOnMorphismsWithGivenTensorProducts( sgreps,
      function( sgreps, source, alpha, gamma, target )
        local direct_sum_category, category_of_rows, irreducible_characters, nr_irreducible_characters, alpha_model, gamma_model, alpha_nr_support, gamma_nr_support, alpha_support, gamma_support, alpha_components, gamma_components, tensored_morphisms_matrix, support, nr_support, indices_tensored_morphisms, tensored_morphisms, sums_of_morphisms, positions, matrices;
        
        direct_sum_category := ModelingCategory( sgreps );
        category_of_rows := UnderlyingAdditiveCategory( direct_sum_category );
        
        irreducible_characters := UnderlyingIrreducibleCharacters( sgreps );
        nr_irreducible_characters := NrIrreducibleCharacters( sgreps );
        
        alpha_model := ModelingMorphism( sgreps, alpha );
        alpha_nr_support := NrSupport( alpha_model );
        alpha_support := Support( alpha_model );
        alpha_components := Components( alpha_model );
        
        gamma_model := ModelingMorphism( sgreps, gamma );
        gamma_nr_support := NrSupport( gamma_model );
        gamma_support := Support( gamma_model );
        gamma_components := Components( gamma_model );
        
        support := Union2( Support( source ), Support( target ) );
        
        nr_support := Length( support );
        
        # A matrix with elements
        # [ [ ɑ₁⊗ɣ₁ ], ..., [ ɑ₁⊗ɣₗ ] ].
        # [     .                .
        # [     .        .       .
        # [     .                .
        # [ [ ɑₙ⊗ɣ₁ ], ..., [ ɑₙ⊗ɣₗ ] ].
        tensored_morphisms :=
            List( [ 1 .. alpha_nr_support ], i ->
                List( [ 1 .. gamma_nr_support ], j ->
                    TensorProductOnMorphisms( category_of_rows, alpha_components[i], gamma_components[j] ) ) );
                    
        # (ɑ⊗ɣ)ₖ := ⊕ᵢ ⊕ⱼ (ɑᵢ⊗ɣⱼ⊗Iₙ₍ᵢⱼ₎ₖ)
        sums_of_morphisms :=
            List( [ 1 .. nr_support ],
              function( k )
                local alpha_gamma_identity, nr_rows, nr_cols, sources, targets, inner_sums, outer_sum;
                
                # Precompute the tensor products (ɑᵢ⊗ɣⱼ)⊗Iₙ₍ᵢⱼ₎ₖ
                alpha_gamma_identity :=
                    List( [ 1 .. alpha_nr_support ], i ->
                        List( [ 1 .. gamma_nr_support ],
                          function( j )
                            local n_ijk, alpha_gamma, identity_morphism, direct_sum;
                            
                            # n₍ᵢⱼ₎ₖ = ⟨χᵢ·χⱼ,χₖ⟩
                            n_ijk := SGREPS_ScalarProduct( irreducible_characters, support[k], alpha_support[i], gamma_support[j] );
                            
                            # If n₍ᵢⱼ₎ₖ = 0, then Iₙ₍ᵢⱼ₎ₖ = 0 so (ɑᵢ⊗ɣⱼ)⊗Iₙ₍ᵢⱼ₎ₖ = 0.
                            # 
                            # if n_ijl = 0 then
                            #
                            #     return ZeroMorphism( category_of_rows, ZeroObject( category_of_rows ), ZeroObject( category_of_rows ) );
                            #
                            # fi;
                            
                            # ɑᵢ⊗ɣⱼ
                            alpha_gamma := tensored_morphisms[i][j];
                            
                            # Iₙ₍ᵢⱼ₎ₖ
                            identity_morphism :=
                                IdentityMorphism( category_of_rows, ObjectConstructor( category_of_rows, n_ijk ) );
                            
                            # (ɑᵢ⊗ɣⱼ)⊗Iₙ₍ᵢⱼ₎ₖ
                            return TensorProductOnMorphisms( category_of_rows, alpha_gamma, identity_morphism );
                            
                          end ) );
                          
                nr_rows := Length( alpha_gamma_identity );
                nr_cols := Length( alpha_gamma_identity[1] );
                
                # Compute the inner sums: ⊕ⱼ (ɑᵢ⊗ɣⱼ⊗Iₙ₍ᵢⱼ₎ₖ)
                
                sources :=
                    List( [ 1 .. nr_rows ], i ->
                        List( [ 1 .. nr_cols ], j ->
                            Source( alpha_gamma_identity[i][j] ) ) );
                            
                targets :=
                    List( [ 1 .. nr_rows ], i ->
                        List( [ 1 .. nr_cols ], j ->
                            Target( alpha_gamma_identity[i][j] ) ) );
                            
                inner_sums :=
                    List( [ 1 .. nr_rows ], i ->
                        DirectSumFunctorialWithGivenDirectSums( category_of_rows,
                            DirectSum( category_of_rows, sources[i] ),
                            sources[i],
                            alpha_gamma_identity[i],
                            targets[i],
                            DirectSum( category_of_rows, targets[i] ) ) );
                            
                # Compute the outer sum: ⊕ᵢ ⊕ⱼ (ɑᵢ⊗ɣⱼ⊗Iₙ₍ᵢⱼ₎ₖ).
                
                outer_sum :=
                    DirectSumFunctorialWithGivenDirectSums( category_of_rows,
                        Component( ModelingObject( sgreps, source ), support[k] ),
                        List( [ 1 .. nr_rows ], i -> Source( inner_sums[i] ) ),
                        inner_sums,
                        List( [ 1 .. nr_rows ], i -> Target( inner_sums[i] ) ),
                        Component( ModelingObject( sgreps, target ), support[k] ) );
                
                return outer_sum;
                
            end );
            
        matrices := List( [ 1 .. nr_support ], i -> UnderlyingMatrix( sums_of_morphisms[i] ) );;
        
        return MorphismConstructor( sgreps,
                    source,
                    NTuple(3,
                        nr_support,
                        support,
                        matrices ),
                    target );
                    
    end );
    
    # Sebastian's PhD. thesis construction I.3.38.
    AddAssociatorLeftToRightWithGivenTensorProducts( sgreps,
      function( sgreps, source, a, b, c, target )
        local product_kron_comon, a_product_kron_comon, b_product_kron_comon, c_product_kron_comon, source_product_kron_comon, morphism_1, morphism_2, morphism_3, morphism_4, morphism_5, morphism_6, morphism_7, morphism_123_perm, morphism_567_perm, morphism_123, morphism_567;
        
        # TODO: This if-statement is currently necessary, because AssociatorData( sgreps )
        #       from Sebastians database has no entries in these cases,
        #       which results in an out of bounds error later.
        if IsZeroForObjects( sgreps, a ) or IsZeroForObjects( sgreps, b ) or IsZeroForObjects( sgreps, c ) then
            
            return ZeroMorphism( sgreps, source, target );
            
        fi;
        
        # TODO: check if a, b or c is the tensor unit and return IdentityMorphism( source )?
        
        product_kron_comon := SubcategoryOfSparseProductOfKroneckerComonoids( sgreps );
        a_product_kron_comon := AsObjectInSubcategoryOfSparseProductOfKroneckerComonoids( product_kron_comon, a );
        b_product_kron_comon := AsObjectInSubcategoryOfSparseProductOfKroneckerComonoids( product_kron_comon, b );
        c_product_kron_comon := AsObjectInSubcategoryOfSparseProductOfKroneckerComonoids( product_kron_comon, c );
        source_product_kron_comon := AsObjectInSubcategoryOfSparseProductOfKroneckerComonoids( product_kron_comon, source );
        
        # (a⊗b)⊗c  ⥲  ⊕ᵢ aᵢ((χᵢ⊗b)⊗c)
        # morphism_1 := SGREPS_Associator_1_Morphism( sgreps, a, b, c, source );
        
        # ⊕ᵢ ɑᵢ((χᵢ⊗b)⊗c)  ⥲  ⊕ᵢ ɑᵢ ⊕ⱼ bⱼ((χᵢ⊗χⱼ)⊗c)
        # morphism_2 := SGREPS_Associator_2_Morphism( sgreps, a, b, c, source );
        
        # ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ (χᵢ⊗χⱼ)⊗c ] ]  ⥲  ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ ⊕ₖ cₖ·[ (χᵢ⊗χⱼ)⊗χₖ ] ] ]
        # morphism_3 := SGREPS_Associator_3_Morphism( sgreps, a, b, c, source );
        
        # ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ ⊕ₖ cₖ·[ χᵢ⊗(χⱼ⊗χₖ) ] ] ]  ⥲  ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ χᵢ⊗(χⱼ⊗c) ] ]
        # morphism_5 := SGREPS_Associator_5_Morphism( sgreps, a, b, c, source );
        
        # ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ χᵢ⊗(χⱼ⊗c) ] ]  ⥲  ⊕ᵢ ɑᵢ·[ χᵢ⊗(b⊗c) ]
        # morphism_6 := SGREPS_Associator_6_Morphism( sgreps, a, b, c, source );
        
        # ⊕ᵢ aᵢ·[ χᵢ⊗(b⊗c) ]  ⥲  a⊗(b⊗c)
        # morphism_7 := SGREPS_Associator_7_Morphism( sgreps, a, b, c, source );
        
        # (a⊗b)⊗c  ⥲  ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ ⊕ₖ cₖ·[ (χᵢ⊗χⱼ)⊗χₖ ] ] ]
        # morphism_123_perm := SGREPS_Associator_123_Morphism( sgreps, a, b, c, source );
        morphism_123_perm := SGREPS_Associator_123_Morphism_multiplicity( product_kron_comon,
                                                                          a_product_kron_comon,
                                                                          b_product_kron_comon,
                                                                          c_product_kron_comon,
                                                                          source_product_kron_comon );
        
        # ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ ⊕ₖ cₖ·[ (χᵢ⊗χⱼ)⊗χₖ ] ] ]  ⥲  ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ ⊕ₖ cₖ·[ χᵢ⊗(χⱼ⊗χₖ) ] ] ]
        # morphism_4 := SGREPS_Associator_4_Morphism( sgreps, a, b, c, source );
        morphism_4 := SGREPS_Associator_4_Morphism_multiplicity( sgreps, a, b, c, source );
        
        # ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ ⊕ₖ cₖ·[ χᵢ⊗(χⱼ⊗χₖ) ] ] ]  ⥲  a⊗(b⊗c)
        # morphism_567_perm := SGREPS_Associator_567_Morphism( sgreps, a, b, c, source );
        morphism_567_perm := SGREPS_Associator_567_Morphism_multiplicity( product_kron_comon,
                                                                          a_product_kron_comon,
                                                                          b_product_kron_comon,
                                                                          c_product_kron_comon,
                                                                          source_product_kron_comon );
        
        # morphism_4 is given by matrices, so for the composition
        # we need to convert the permutations into matrices as well.
        morphism_123 := EmbeddingProductCatOfPermutationCatIntoSGRepsOnMorphism( sgreps, morphism_123_perm );
        morphism_567 := EmbeddingProductCatOfPermutationCatIntoSGRepsOnMorphism( sgreps, morphism_567_perm );
        
        return PreComposeList( sgreps, source, [ morphism_123, morphism_4, morphism_567 ], target );
        
    end );
    
    # Sebastian's PhD. thesis construction I.3.42.
    AddBraidingWithGivenTensorProducts( sgreps,
      function( sgreps, ab, a, b, ba )
        local morphism_1, morphism_2, morphism_3, morphism_4, morphism_5, morphism_12, morphism_45, L;
       
        if IsZeroForObjects( sgreps, a ) or IsZeroForObjects( sgreps, b ) then
            
            return ZeroMorphism( sgreps, ab, ba );
            
        fi;
        
        # (a⊗b)⊗c  ⥲  ⊕ᵢ aᵢ·[(χᵢ⊗b)⊗c]
        # morphism_1 := SGREPS_Braiding_1_Morphism( sgreps, a, b, ab );
        
        # ⊕ᵢ ɑᵢ·(χᵢ⊗b)  ⥲  ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·(χᵢ⊗χⱼ) ]
        # morphism_2 := SGREPS_Braiding_2_Morphism( sgreps, a, b, ab );
        
        # ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·(χᵢ⊗χⱼ) ]  ⥲  ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·(χⱼ⊗χᵢ) ]
        # morphism_3 := SGREPS_Braiding_3_Morphism( sgreps, a, b, ab );
        
        # ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·(χⱼ⊗χᵢ) ]  ⥲  ⊕ᵢ ɑᵢ·(b⊗χᵢ)
        # morphism_4 := SGREPS_Braiding_4_Morphism( sgreps, a, b, ab );
        
        # ⊕ᵢ ɑᵢ·(b⊗χᵢ)  ⥲  a⊗b
        # morphism_5 := SGREPS_Braiding_5_Morphism( sgreps, a, b, ab );
        
        # (a⊗b)⊗c  ⥲  ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·(χᵢ⊗χⱼ) ]
        morphism_12 := SGREPS_Braiding_12_Morphism( sgreps, a, b, ab );
        
        # ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·(χᵢ⊗χⱼ) ]  ⥲  ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·(χⱼ⊗χᵢ) ]
        morphism_3 := SGREPS_Braiding_3_Morphism( sgreps, a, b, ab );
        
        # ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·(χⱼ⊗χᵢ) ]  ⥲  a⊗b
        morphism_45 := SGREPS_Braiding_45_Morphism( sgreps, a, b, ba );
        
        L := [ morphism_12, morphism_3, morphism_45 ];
        
        return PreComposeList( sgreps, ab, L, ba );
        
    end );
    
    # (l₁⊕...⊕lₙ)⊗a ⥲ (l₁⊗a)⊕...⊕(lₙ⊗a)
    # AddRightDistributivityExpandingWithGivenObjects( sgreps,
    #   function( sgreps, source, L, a, target )
    #     local morphism;
    #
    #     morphism := SGREPS_RightDistributivityExpandingPermutation( sgreps, L, a, source );
    #
    #     return SGREPS_FunctorFromMorphismPermutationsToMorphismMatrices( sgreps, source, morphism, target );
    #
    # end );
    
    # Compilation of RightDistributivityExpanding with 
    # RightDistributivityExpandingWithGivenObjects( product_kron_comon, ... )
    # given as most high level categorical code takes 1h2m
    # 
    # (l₁⊕...⊕lₙ)⊗a ⥲ (l₁⊗a)⊕...⊕(lₙ⊗a)
    AddRightDistributivityExpandingWithGivenObjects( sgreps,
      function( sgreps, source, L, a, target )
        local product_kron_comon, F_product_permcat, morphism_product_kron_comon, morphism_product_perms;
        
        product_kron_comon := SubcategoryOfSparseProductOfKroneckerComonoids( sgreps );
        F_product_permcat := IsomorphismFromCoreToProductCategoryOfPermutationCategory( product_kron_comon );
        
        morphism_product_kron_comon :=
            RightDistributivityExpandingWithGivenObjects( product_kron_comon,
                AsObjectInSubcategoryOfSparseProductOfKroneckerComonoids( product_kron_comon, source ),
                List( L, object -> AsObjectInSubcategoryOfSparseProductOfKroneckerComonoids( product_kron_comon, object ) ),
                AsObjectInSubcategoryOfSparseProductOfKroneckerComonoids( product_kron_comon, a ),
                AsObjectInSubcategoryOfSparseProductOfKroneckerComonoids( product_kron_comon, target ) );
        
        # We need to invert the permutations, because EmbeddingProductCatOfPermutationCatIntoSGRepsOnMorphism
        # uses PermMat, which constructs a matrix from a permutation via rows,
        # but we need to construct them via columns.
        
        # morphism_product_perms := ApplyFunctor( F_product_permcat, morphism_product_kron_comon );
        # morphism_product_perms := InverseForMorphisms( morphism_product_perms );
        
        # TODO: is the following faster, which uses PermutationMat?
        # return EmbeddingProductCatOfPermutationCatIntoSGRepsOnMorphism( sgreps, morphism_product_perms );
        
        # TODO: or is the following code faster, which uses CertainColumns?
        return FunctorProdInsMatIntoSGRepsUsingCertainCols( sgreps, morphism_product_kron_comon );
        
    end );
    
    # (l₁⊗a)⊕...⊕(lₙ⊗a) ⥲ (l₁⊕...⊕lₙ)⊗a
    AddRightDistributivityFactoringWithGivenObjects( sgreps,
      function( sgreps, source, L, a, target )
        local morphism;
        
        morphism := SGREPS_RightDistributivityFactoringPermutation( sgreps, L, a, source );
        
        return SGREPS_FunctorFromMorphismPermutationsToMorphismMatrices( sgreps, source, morphism, target );
        
    end );
    
    # a⊗(l₁⊕...⊕lₙ) ⥲ (a⊗l₁)⊕...⊕(a⊗lₙ)
    # AddLeftDistributivityExpandingWithGivenObjects( sgreps,
    #   function( sgreps, source, a, L, target )
    #     local morphism;
    #
    #     morphism := SGREPS_LeftDistributivityExpandingPermutation( sgreps, a, L, source );
    #
    #     return SGREPS_FunctorFromMorphismPermutationsToMorphismMatrices( sgreps, source, morphism, target );
    #
    # end );
    
    # a⊗(l₁⊕...⊕lₙ) ⥲ (a⊗l₁)⊕...⊕(a⊗lₙ)
    AddLeftDistributivityExpandingWithGivenObjects( sgreps,
      function( sgreps, source, a, L, target )
        local product_kron_comon, F_product_permcat, morphism_product_kron_comon, morphism_product_perms;
        
        product_kron_comon := SubcategoryOfSparseProductOfKroneckerComonoids( sgreps );
        F_product_permcat := IsomorphismFromCoreToProductCategoryOfPermutationCategory( product_kron_comon );
        
        morphism_product_kron_comon :=
            LeftDistributivityExpandingWithGivenObjects( product_kron_comon,
                AsObjectInSubcategoryOfSparseProductOfKroneckerComonoids( product_kron_comon, source ),
                AsObjectInSubcategoryOfSparseProductOfKroneckerComonoids( product_kron_comon, a ),
                List( L, object -> AsObjectInSubcategoryOfSparseProductOfKroneckerComonoids( product_kron_comon, object ) ),
                AsObjectInSubcategoryOfSparseProductOfKroneckerComonoids( product_kron_comon, target ) );
        
        # We need to invert the permutations, because EmbeddingProductCatOfPermutationCatIntoSGRepsOnMorphism
        # uses PermMat, which constructs a matrix from a permutation via rows,
        # but we need to construct them via columns.
        
        # morphism_product_perms := ApplyFunctor( F_product_permcat, morphism_product_kron_comon );
        # morphism_product_perms := InverseForMorphisms( morphism_product_perms );
        
        # TODO: is the following faster, which uses PermutationMat?
        # return EmbeddingProductCatOfPermutationCatIntoSGRepsOnMorphism( sgreps, morphism_product_perms );
        
        # TODO: or is the following code faster, which uses CertainColumns?
        return FunctorProdInsMatIntoSGRepsUsingCertainCols( sgreps, morphism_product_kron_comon );
        
    end );
    
    # (a⊗l₁)⊕...⊕(a⊗lₙ) ⥲ a⊗(l₁⊕...⊕lₙ)
    AddLeftDistributivityFactoringWithGivenObjects( sgreps,
      function( sgreps, source, a, L, target )
        local morphism;
        
        morphism := SGREPS_LeftDistributivityFactoringPermutation( sgreps, a, L, source );
        
        return SGREPS_FunctorFromMorphismPermutationsToMorphismMatrices( sgreps, source, morphism, target );
        
    end );
    
    # Sebastian's PhD. thesis section I.3.3.6.
    AddDualOnObjects( sgreps,
      function( sgreps, a )
        local a_nr_support, a_support, a_components, dual_support, dual_datum;
        
        a_nr_support := NrSupport( a );
        a_support := Support( a );
        a_components := Components( a );
        
        dual_support := List( [ 1 .. a_nr_support ], i ->
            SGREPS_IndexOfDualOfIrreducibleCharacter( sgreps, a_support[i] ) );
            
        dual_datum := SGREPS_DualObjectDatum( sgreps, a_nr_support, dual_support, a_components );
        
        return ObjectConstructor( sgreps, dual_datum );
        
    end );
    
    # Sebastian's PhD. thesis section I.3.3.6.
    AddDualOnMorphismsWithGivenDuals( sgreps,
      function( sgreps, source, alpha, target )
        local direct_sum_category, category_of_rows, alpha_model, nr_support, support, components, source_model, target_model, dual_support, dual_components, dual_datum, dual;
        
        direct_sum_category := ModelingCategory( sgreps );
        category_of_rows := UnderlyingAdditiveCategory( direct_sum_category );
        
        alpha_model := ModelingMorphism( sgreps, alpha );
        
        nr_support := NrSupport( alpha_model );
        support := Support( alpha_model );
        components := Components( alpha_model );
        
        source_model := ModelingObject( sgreps, source );
        target_model := ModelingObject( sgreps, target );
        
        dual_support := List( [ 1 .. nr_support ], i ->
            SGREPS_IndexOfDualOfIrreducibleCharacter( sgreps, support[i] ) );
            
        dual_components := List( [ 1 .. nr_support ], function( i )
            local s, t;
            
            s := Component( source_model, support[i] );
            t := Component( target_model, support[i] );
            
            return UnderlyingMatrix( DualOnMorphismsWithGivenDuals( category_of_rows, s, components[i], t ) );
            
        end );
        
        dual_datum := SGREPS_DualMorphismDatum( sgreps, nr_support, dual_support, dual_components );
        
        # 'source' and 'target' are swapped because the dual is a contravariant functor.
        return MorphismConstructor( sgreps, source, dual_datum, target );
        
    end );
    
    # Sebastian's PhD. thesis Construction I.3.55.
    # Note: there are typos with the duals, they have to be swapped.
    AddCoevaluationForDualWithGivenTensorProduct( sgreps,
      function( sgreps, unit, a, aav )
        local morphism_1, morphism_2, morphism_3, morphism_23;
        
        # 1·χᵤ → ⊕ᵢ ɑᵢ·[ ⊕ⱼ aⱼ·(χᵢ⊗χⱼᵛ) ]
        morphism_1 := SGREPS_CoevaluationForDual_1_Morphism( sgreps, unit, a, aav );
        
        # ⊕ᵢ ɑᵢ·[ ⊕ⱼ aⱼ·(χᵢ⊗χⱼᵛ) ] → ⊕ᵢ ɑᵢ·(χᵢ⊗aᵛ)
        # morphism_2 := SGREPS_CoevaluationForDual_2_Morphism( sgreps, a, aav );
        
        # ⊕ᵢ ɑᵢ·(χᵢ⊗aᵛ) → a⊗aᵛ
        # morphism_3 := SGREPS_CoevaluationForDual_3_Morphism( sgreps, a, aav );
        
        # ⊕ᵢ ɑᵢ·[ ⊕ⱼ aⱼ·(χᵢ⊗χⱼᵛ) ] → a⊗aᵛ
        morphism_23 := SGREPS_CoevaluationForDual_23_Morphism( sgreps, a, aav );
        
        return PreComposeList( sgreps, unit, [ morphism_1, morphism_23 ], aav );
        
    end );
    
    # Sebastian's PhD. thesis Construction I.3.55.
    # Note: there are typos with the duals, they have to be swapped.
    AddEvaluationForDualWithGivenTensorProduct( sgreps,
      function( sgreps, ava, a, unit )
        local morphism_1, morphism_2, morphism_3, morphism_12;
        
        # aᵛ⊗a → ⊕ᵢ ɑᵢ·(χᵢᵛ⊗a)
        # morphism_1 := SGREPS_EvaluationForDual_1_Morphism( sgreps, ava, a );
        
        # ⊕ᵢ ɑᵢ·(χᵢᵛ⊗a) → ⊕ᵢ ɑᵢ·[ ⊕ⱼ aⱼ·(χᵢᵛ⊗χⱼ) ]
        # morphism_2 := SGREPS_EvaluationForDual_2_Morphism( sgreps, ava, a );
        
        # aᵛ⊗a → ⊕ᵢ ɑᵢ·[ ⊕ⱼ aⱼ·(χᵢᵛ⊗χⱼ) ]
        morphism_12 := SGREPS_EvaluationForDual_12_Morphism( sgreps, ava, a );
        
        # ⊕ᵢ ɑᵢ·[ ⊕ⱼ aⱼ·(χᵢᵛ⊗χⱼ) ] → 1·χᵤ
        morphism_3 := SGREPS_EvaluationForDual_3_Morphism( sgreps, ava, a, unit );
        
        return PreComposeList( sgreps, ava, [ morphism_12, morphism_3 ], unit );
        
    end );
    
end );

####################################
##
## Attributes
##
####################################

InstallMethodForCompilerForCAP( NrSupport,
                                [ IsObjectInSkeletalCategoryOfGroupRepresentations ],
                                
  function( object )
    
    return TripleOfNrSupportListOfSupportListOfRanks( object )[1];
    
end );

InstallMethodForCompilerForCAP( NrSupport,
                                [ IsMorphismInSkeletalCategoryOfGroupRepresentations ],
                                
  function( morphism )
    
    return TripleOfNrSupportListOfSupportListOfMatrices( morphism )[1];
    
end );

InstallMethodForCompilerForCAP( Support,
                                [ IsObjectInSkeletalCategoryOfGroupRepresentations ],
                                
  function( object )
    
    return TripleOfNrSupportListOfSupportListOfRanks( object )[2];
    
end );

InstallMethodForCompilerForCAP( Support,
                                [ IsMorphismInSkeletalCategoryOfGroupRepresentations ],
                                
  function( morphism )
    
    return TripleOfNrSupportListOfSupportListOfMatrices( morphism )[2];
    
end );

InstallMethodForCompilerForCAP( Components,
                                [ IsObjectInSkeletalCategoryOfGroupRepresentations ],
                                
  function( object )
    
    return TripleOfNrSupportListOfSupportListOfRanks( object )[3];
    
end );

InstallMethodForCompilerForCAP( Components,
                                [ IsMorphismInSkeletalCategoryOfGroupRepresentations ],
                                
  function( morphism )
    
    return TripleOfNrSupportListOfSupportListOfMatrices( morphism )[3];
    
end );

InstallMethodForCompilerForCAP( DecompositionIntoSimpleObjects,
                                [ IsObjectInSkeletalCategoryOfGroupRepresentations ],
                                
  function( object )
    local sgreps, nr_support, support, components;
    
    sgreps := CapCategory( object );
    
    nr_support := NrSupport( object );
    support := Support( object );
    components := Components( object );
    
    return Concatenation( List( [ 1 .. nr_support ], i ->
        List( [ 1 .. components[i] ], j ->
            ObjectConstructor( sgreps, NTuple( 3, 1, [ support[i] ], [ 1 ] ) ) ) ) );
    
end );

InstallMethodForCompilerForCAP( DecompositionIntoListOfSupportingObjects,
                                [ IsObjectInSkeletalCategoryOfGroupRepresentations ],
                                
  function( object )
    local sgreps, nr_support, support, components;
    
    sgreps := CapCategory( object );
    
    nr_support := NrSupport( object );
    support := Support( object );
    components := Components( object );
    
    return List( [ 1 .. nr_support ], i ->
        ObjectConstructor( sgreps, NTuple( 3, 1, [ support[i] ], [ components[i] ] ) ) );
    
end );

####################################
##
## Operations
##
####################################

InstallMethodForCompilerForCAP( Component,
                                [ IsObjectInSkeletalCategoryOfGroupRepresentations, IsBigInt ],
                                
  function( object, i )
    local support, components;
    
    #% CAP_JIT_DROP_NEXT_STATEMENT
    Assert( 0, 1 <= i and i <= NrIrreducibleCharacters( CapCategory( object ) ) );
    
    support := Support( object );
    
    components := Components( object );
    
    return [ [ BigInt( 0 ) ], components{ Positions( support, i ) } ][ 1 + BooleanToInteger( i in support ) ][1];
    
end );

InstallMethodForCompilerForCAP( Component,
                                [ IsMorphismInSkeletalCategoryOfGroupRepresentations, IsBigInt ],
                                
  function( morphism, i )
    local splitting_field, zero_matrix, support, matrices;
    
    #% CAP_JIT_DROP_NEXT_STATEMENT
    Assert( 0, 1 <= i and i <= NrIrreducibleCharacters( CapCategory( morphism ) ) );
    
    splitting_field := UnderlyingSplittingField( CapCategory( morphism ) );
    
    zero_matrix := HomalgZeroMatrix( 0, 0, splitting_field );
    
    support := Support( morphism );
    
    matrices := Components( morphism );
    
    return [ [ zero_matrix ], matrices{ Positions( support, i ) } ][ 1 + BooleanToInteger( i in support ) ][1];
    
end );

##
InstallMethodForCompilerForCAP( \[\],
                                [ IsObjectInSkeletalCategoryOfGroupRepresentations, IsInt ],
                                
  function( object, i )
    
    return Component( object, i );
    
end );

##
InstallMethodForCompilerForCAP( \[\],
                                [ IsMorphismInSkeletalCategoryOfGroupRepresentations, IsInt ],
                                
  function( morphism, i )
    
    return Component( morphism, i );
    
end );

InstallMethodForCompilerForCAP( ProductOfCharactersAsObjectInModelingProductCategory,
                                [ IsSkeletalCategoryOfGroupRepresentations, IsBigInt, IsBigInt ],
                                
  function( sgreps, i, j )
    local direct_sum_category, category_of_rows, irreducible_characters, nr_irreducible_characters, scalar_product, support, components;
    
    direct_sum_category := ModelingCategory( sgreps );
    category_of_rows := UnderlyingAdditiveCategory( direct_sum_category );
    
    irreducible_characters := UnderlyingIrreducibleCharacters( sgreps );
    nr_irreducible_characters := NrIrreducibleCharacters( sgreps );
    
    scalar_product := List( [ 1 .. nr_irreducible_characters ], k -> SGREPS_ScalarProduct( irreducible_characters, k, i, j ) );
    
    support := Filtered( [ 1 .. nr_irreducible_characters ], k -> not IsZero( scalar_product[k] ) );
    
    components := List( support, k -> ObjectConstructor( category_of_rows, scalar_product[k] ) );
    
    return ObjectConstructor( direct_sum_category, NTuple( 3, Length( support ), support, components ) );
    
end );

InstallMethodForCompilerForCAP( SecondExteriorPowerOfSimpleObject,
                                [ IsSkeletalCategoryOfGroupRepresentations,
                                  IsObjectInSkeletalCategoryOfGroupRepresentations ],
                                
  function( sgreps, a )
    local character_table, irreducible_characters, character, exterior_power, scalar_products, components, support;
    
    character_table := UnderlyingCharacterTable( sgreps );
    
    irreducible_characters := UnderlyingIrreducibleCharacters( sgreps );
    
    character := irreducible_characters[ Support( a )[1] ];
    
    exterior_power := AntiSymmetricParts( character_table, [ character ], 2 )[1];
    
    scalar_products := List( [ 1 .. NrIrreducibleCharacters( sgreps ) ], i ->
        ScalarProduct( irreducible_characters[ i ], exterior_power ) );
        
    components := Filtered( scalar_products, prod -> not IsZero( prod ) );
        
    support := Filtered( [ 1 .. NrIrreducibleCharacters( sgreps ) ], i ->
        not IsZero( scalar_products[i] ) );
        
    return ObjectConstructor( sgreps, NTuple( 3, Length( support ), support, components ) );
    
end );

#########################################################
#
# Functors: SGReps ⟷ Sparse poduct of Kronecker comonoids
#
#########################################################

InstallMethodForCompilerForCAP( AsObjectInSubcategoryOfSparseProductOfKroneckerComonoids,
                                [ IsSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfKroneckerComonoids,
                                  IsObjectInSkeletalCategoryOfGroupRepresentations ],
                                
  function( product_kron_comon, object )
    local sgreps;
    
    sgreps := CapCategory( object );
    
    return ObjectConstructor( product_kron_comon, ObjectDatum( sgreps, object ) );
    
end );

# TODO: switch to the CapFunctor EmbeddingOfSparseProductOfKroneckerComonoids
InstallMethodForCompilerForCAP( FunctorProdInsMatIntoSGRepsUsingUnionOfCols,
                                [ IsSkeletalCategoryOfGroupRepresentations,
                                  IsMorphismInSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfKroneckerComonoids ],
                                
  function( sgreps, morphism )
    local direct_sum_category, category_of_rows, homalg_field, embedding_product_kron_comon, source, target, nr_support_morphism, support_morphism, list_nr_blockcols_blockcols, matrices;
    
    direct_sum_category := ModelingCategory( sgreps );
    
    category_of_rows := UnderlyingAdditiveCategory( direct_sum_category );
    
    homalg_field := UnderlyingRing( category_of_rows );
    
    embedding_product_kron_comon := EmbeddingOfSparseProductOfKroneckerComonoids( sgreps );
    
    source := Source( morphism );
    target := Target( morphism );
    
    nr_support_morphism := NrSupport( morphism );
    support_morphism := Support( morphism );
    
    # A list of the form:
    # [
    #   [ m, [ [a,b], ..., [c,d] ] ],
    #                  .
    #                  .
    #                  .
    #   [ n, [ [e,f], ..., [g,h] ] ]
    # ]
    list_nr_blockcols_blockcols := Components( morphism );
    
    # TODO: use CertainRows/CertainCols instead of UnionOfRows(...).
    matrices :=
        List( [ 1 .. nr_support_morphism ], function( i )
            local nr_rows, nr_cols, block_cols, matrix;
            
            nr_rows := Component( source, support_morphism[i] );
            nr_cols := Component( target, support_morphism[i] );
            
            block_cols := list_nr_blockcols_blockcols[i][2];
            
            # Blocks are of the form:
            # ┌   ┐
            # │0ₘₙ│
            # │1ₙ │
            # │0ₗₙ│
            # └   ┘
            block_cols := List( block_cols, function( block )
                local cols;
                
                cols := block[2] - block[1] + 1;
                
                return UnionOfRows( homalg_field, cols, [
                             HomalgZeroMatrix( block[1] - 1, cols, homalg_field ),
                             HomalgIdentityMatrix( cols, homalg_field ),
                             HomalgZeroMatrix( nr_rows - block[2], cols, homalg_field ) ] );
                 
            end );
            
            return UnionOfColumns( homalg_field, nr_rows, block_cols );
            
        end );
        
    return MorphismConstructor( sgreps,
                ApplyFunctor( embedding_product_kron_comon, source ),
                NTuple( 3, nr_support_morphism, support_morphism, matrices ),
                ApplyFunctor( embedding_product_kron_comon, target ) );
     
end );

# TODO: switch to the CapFunctor EmbeddingOfSparseProductOfKroneckerComonoids
InstallMethodForCompilerForCAP( FunctorProdInsMatIntoSGRepsUsingCertainCols,
                                [ IsSkeletalCategoryOfGroupRepresentations,
                                  IsMorphismInSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfKroneckerComonoids ],
                                
  function( sgreps, morphism )
    local direct_sum_category, category_of_rows, splitting_field, embedding_product_kron_comon, source, target, source_components, nr_support_morphism, support_morphism, list_nr_blockcols_blockcols, matrices;
    
    direct_sum_category := ModelingCategory( sgreps );
    
    category_of_rows := UnderlyingAdditiveCategory( direct_sum_category );
    
    splitting_field := UnderlyingSplittingField( sgreps );
    
    embedding_product_kron_comon := EmbeddingOfSparseProductOfKroneckerComonoids( sgreps );
    
    source := Source( morphism );
    target := Target( morphism );
    
    source_components := Components( source );
    
    nr_support_morphism := NrSupport( morphism );
    support_morphism := Support( morphism );
    
    # A list of the form:
    # [
    #   [ m, [ [a,b], ..., [c,d] ] ],
    #                  .
    #                  .
    #                  .
    #   [ n, [ [e,f], ..., [g,h] ] ]
    # ]
    list_nr_blockcols_blockcols := Components( morphism );
    
    matrices := List( [ 1 .. nr_support_morphism ], function( i )
        local perm_list, matrix, dimension;
        
        perm_list := list_nr_blockcols_blockcols[i][2];
        
        perm_list := List( [ 1 .. list_nr_blockcols_blockcols[i][1] ], j -> [ perm_list[j][1] .. perm_list[j][2] ] );
        
        perm_list := Concatenation( perm_list );
        
        dimension := source_components[i];
        
        return CertainColumns( HomalgIdentityMatrix( dimension, splitting_field ), perm_list );
        
    end );
    
    return MorphismConstructor( sgreps,
                ApplyFunctor( embedding_product_kron_comon, source ),
                NTuple( 3, nr_support_morphism, support_morphism, matrices ),
                ApplyFunctor( embedding_product_kron_comon, target ) );
    
end );

####################################
#
# Functors: SGReps ⟷ ProdPermCat
#
####################################

# TODO: switch to the CapFunctor EmbeddingOfProductCategoryOfPermutationCategory
InstallMethodForCompilerForCAP( EmbeddingProductCatOfPermutationCatIntoSGRepsOnObject,
                                [ IsSkeletalCategoryOfGroupRepresentations,
                                  IsObjectInSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfPermutationCategory ],
                                
  function( sgreps, object )
    
    return ObjectConstructor( sgreps, NTuple( 3, NrSupport( object ), Support( object ), Components( object ) ) );
    
end );

# TODO: switch to the CapFunctor EmbeddingOfProductCategoryOfPermutationCategory
InstallMethodForCompilerForCAP( EmbeddingProductCatOfPermutationCatIntoSGRepsOnMorphism,
                                [ IsSkeletalCategoryOfGroupRepresentations,
                                  IsMorphismInSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfPermutationCategory ],
                                
  function( sgreps, morphism )
    local splitting_field, nr_support, components, source, source_components, matrices;
    
    splitting_field := UnderlyingSplittingField( sgreps );
    
    nr_support := NrSupport( morphism );
    components := Components( morphism );
    
    source := Source( morphism );
    source_components := Components( source );
    
    # TODO: is CertainRows( HomalgIdentityMatrix( ListPerm( ... ) ), ... ) faster?
    # TODO: should we use Source( components[i] ) instead?
    matrices := List( [ 1 .. nr_support ], i ->
        CertainColumns( HomalgIdentityMatrix( source_components[i], splitting_field ), ListPerm( components[i], source_components[i] ) ) );
        # HomalgMatrix( PermutationMat( components[i], source_components[i] ), splitting_field ) ); # Too slow, don't activate! See Coevaluation tests.
    
    return MorphismConstructor( sgreps,
                EmbeddingProductCatOfPermutationCatIntoSGRepsOnObject( sgreps, source ),
                NTuple( 3, nr_support, Support( morphism ), matrices ),
                EmbeddingProductCatOfPermutationCatIntoSGRepsOnObject( sgreps, source ) );
    
end );

####################################
##
## Compilation helper functions
##
####################################

InstallGlobalFunction( SGREPS_ScalarProduct,
  
  function( irreducible_characters, k, i, j )
    local xk, xi, xj, xixj;
    
    xk := irreducible_characters[k];
    xi := irreducible_characters[i];
    xj := irreducible_characters[j];
    
    xixj := xi * xj;
    
    return ScalarProduct( xk, xixj );
    
end );

InstallGlobalFunction( SGREPS_IndexOfTrivialCharacter,
  
  function( sgreps )
    local irreducible_characters;
    
    irreducible_characters := UnderlyingIrreducibleCharacters( sgreps );
    
    return PositionProperty( irreducible_characters, IsOne );
    
end );

InstallGlobalFunction( SGREPS_IndexOfDualOfIrreducibleCharacter,
  
  function( sgreps, character_nr )
    local irreducible_characters, character;
    
    irreducible_characters := UnderlyingIrreducibleCharacters( sgreps );
    
    character := irreducible_characters[ character_nr ];
    
    return Position( irreducible_characters, ComplexConjugate( character ) );
    
end );

InstallGlobalFunction( SGREPS_DualObjectDatum,
  
  function( sgreps, nr_support, dual_support, dual_components )
    local permutation, support, components;
    
    # TODO: Can we use Sortex or would the sorting be
    #       a side-effect which is bad for the compiler?
    permutation := SortingPerm( dual_support );
    
    support := Permuted( dual_support, permutation );
    components := Permuted( dual_components, permutation );
    
    return NTuple( 3, nr_support, support, components );
    
end );

InstallGlobalFunction( SGREPS_DualMorphismDatum,
  
  function( sgreps, nr_support, dual_support, dual_components )
    local permutation, support, components;
    
    # TODO: Can we use Sortex or would the sorting be
    #       a side-effect which is bad for the compiler?
    permutation := SortingPerm( dual_support );
    
    support := Permuted( dual_support, permutation );
    components := Permuted( dual_components, permutation );
    
    return NTuple( 3, nr_support, support, components );
    
end );

####################################
##
## View & Display
##
####################################

SubscriptDigits := [ "₀", "₁", "₂", "₃", "₄", "₅", "₆", "₇", "₈", "₉" ];

# Convert a number into a unicode subscript.
ToSubscript := function( n )
    local digits, subscripts, d;
    
    if n = 0 then
        
        return SubscriptDigits[1];
        
    fi;
    
    digits := [];
    
    while n > 0 do
        
        Add( digits, n mod 10 );
        
        n := Int( n / 10 );
        
    od;
    
    subscripts := [];
    
    for d in Reversed( digits ) do
        
        Append( subscripts, SubscriptDigits[d + 1] );
        
    od;
    
    return subscripts;
    
end;

##
InstallMethod( DisplayString,
               [ IsObjectInSkeletalCategoryOfGroupRepresentations ],
               
  function( object )
    local string, nr_support, support, ranks, i, character_nr, rank;
    
    string := "";
    
    nr_support := NrSupport( object );
    support := Support( object );
    ranks := Components( object );
    
    if nr_support = 0 then
        
        string := String( 0 );
        
    elif nr_support = 1 then
        
        character_nr := support[1];
        rank := ranks[1];
        
        if rank = 1 then
            
            string := Concatenation( "χ", ToSubscript( character_nr ) );
            
        else
            
            string := Concatenation( String( rank ), "χ", ToSubscript( character_nr ) );
            
        fi;
        
    elif nr_support > 1 then
        
        character_nr := support[1];
        rank := ranks[1];
        
        if rank = 1 then
            
            string := Concatenation( "χ", ToSubscript( character_nr ) );
            
        else
            
            string := Concatenation( String( rank ), "χ", ToSubscript( character_nr ) );
            
        fi;
        
        for i in [ 2 .. nr_support ] do
            
            character_nr := support[i];
            rank := ranks[i];
            
            if rank = 1 then
                
                string := Concatenation( string, "⊕χ", ToSubscript( character_nr ) );
                
            else
                
                string := Concatenation( string, "⊕", String( ranks[i] ), "χ", ToSubscript( character_nr ) );
                
            fi;
            
        od;
        
    fi;
    
    return string;
    
end );

##
InstallMethod( Display,
               [ IsMorphismInSkeletalCategoryOfGroupRepresentations ],
               
  function( morphism )
    local length, support, matrices, i;
    
    if IsZeroForMorphisms( morphism ) then
        
        Display( "0" );
        
    else
        
        length := NrSupport( morphism );
        support := Support( morphism );
        matrices := Components( morphism );
        
        for i in [ 1 .. length ] do
            
            Print( Concatenation( "Component: (", String( support[i] ), ")\n" ) );
            
            Print( "\n" );
            
            Display( matrices[i] );
            
            Print( "\n------------------------\n" );
            
        od;
        
    fi;
    
end );

