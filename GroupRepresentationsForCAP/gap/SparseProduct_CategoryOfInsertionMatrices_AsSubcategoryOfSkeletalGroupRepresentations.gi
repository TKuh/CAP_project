# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Implementations
#

#! @Chapter Semisimple Categories

ReadPackage(
    "GroupRepresentationsForCAP",
    "gap/precompiled_categories/SparseProduct_CategoryOfInsertionMatrices_AsSubcategoryOfSkeletalGroupRepresentations_S4_precompiled.gi" );

####################################
##
## Constructors
##
####################################

##
InstallMethod( SparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations,
               [ IsList ],
               
  FunctionWithNamedArguments(
  [
    [ "no_precompiled_code", false ],
    [ "ins_mat_no_precompiled_code", false ],
    [ "FinalizeCategory", true ],
  ],
  function( CAP_NAMED_ARGUMENTS, irreducible_characters )
    local name, category_filter, category_object_filter, category_morphism_filter, nr_irreducible_characters, ins_mat, product_ins_mat, object_datum_type, object_datum, object_constructor, morphism_datum_type, morphism_datum, morphism_constructor, modeling_tower_object_datum, modeling_tower_object_constructor, modeling_tower_morphism_datum, modeling_tower_morphism_constructor, subcat;
    
    ##
    name := Concatenation( "Reinterp( 𝚷( ", String( Length( irreducible_characters ) ), ", CategoryOfInsertionMatrices ) )" );
    
    ##
    category_filter := IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations;
    category_object_filter := IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations;
    category_morphism_filter := IsMorphismInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations;
    
    ##
    object_datum_type :=
        CapJitDataTypeOfNTupleOf( 3,
            IsBigInt,
            CapJitDataTypeOfListOf( IsBigInt ),
            CapJitDataTypeOfListOf( IsBigInt ) );
    
    ##
    object_constructor :=
      function( subcat, triple )
        local length, support, list_nr_elements;
        
        length := triple[1];
        support := triple[2];
        list_nr_elements := triple[3];
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, 0 <= length and length <= NrIrreducibleCharacters( subcat ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( support ) = length );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( list_nr_elements ) = length );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( [ 1 .. length ], i ->
            1 <= support[i] and support[i] <= NrIrreducibleCharacters( subcat ) ) );
        
        # The supporting integers must be strictly increasing.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( [ 1 .. length - 1 ], i ->
            support[i] < support[i+1] ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( list_nr_elements, rank -> not rank = 0 ) );
        
        return CreateCapCategoryObjectWithAttributes( subcat,
                       TripleOfNrSupportListOfSupportListOfNumberElements, triple );
        
    end;
    
    ##
    object_datum := { subcat, obj } -> TripleOfNrSupportListOfSupportListOfNumberElements( obj );
    
    ##
    morphism_datum_type :=
        CapJitDataTypeOfNTupleOf( 3,
            IsBigInt,
            CapJitDataTypeOfListOf( IsBigInt ),
            CapJitDataTypeOfListOf(
                CapJitDataTypeOfNTupleOf( 2,
                    IsBigInt,
                    CapJitDataTypeOfListOf(
                        CapJitDataTypeOfNTupleOf( 2,
                            IsBigInt,
                            IsBigInt ) ) ) ) );
                            
    ##
    morphism_constructor :=
      function( subcat, S, triple, T )
        local length, support, list_list_columns, matrix, length_source, support_source, ranks_source, length_target, support_target, ranks_target, i, current_support, source, target, s, t;
        
        length := triple[1];
        support := triple[2];
        list_list_columns := triple[3];
        
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
        Assert( 0, Length( list_list_columns ) = length );
        
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
                    TripleOfNrSupportListOfSupportListOfNrBlockColumnsAndListOfBlockColumns, triple );
                    
    end;
    
    ##
    morphism_datum :=
        { subcat, phi } -> TripleOfNrSupportListOfSupportListOfNrBlockColumnsAndListOfBlockColumns( phi );
        
    ####################################
    # Modeling
    ####################################
    
    ## building the categorical tower:
    
    nr_irreducible_characters := Length( irreducible_characters );
    
    ins_mat :=
        CategoryOfInsertionMatrices(
            : no_precompiled_code := CAP_NAMED_ARGUMENTS.ins_mat_no_precompiled_code,
              FinalizeCategory := true );
    
    product_ins_mat :=
        SparseProductOfCartesianCategory(
            nr_irreducible_characters,
            ins_mat
            : FinalizeCategory := true );
        
    ## From the raw object data to the object in the modeling category.
    modeling_tower_object_constructor :=
      function( subcat, triple )
        local product_ins_mat, C, nr_support, support, list_nr_elements, components;
        
        product_ins_mat := ModelingCategory( subcat );
        
        C := UnderlyingCartesianCategory( product_ins_mat );
        
        nr_support := triple[1];
        support := triple[2];
        list_nr_elements := triple[3];
        
        # Turn the integer list_nr_elements into objects of C.
        components :=
            List( [ 1 .. nr_support ], n ->
                ObjectConstructor( C, list_nr_elements[n] ) );
        
        return ObjectConstructor( product_ins_mat, NTuple( 3, nr_support, support, components ) );
        
    end;
    
    ## From the object in the modeling category to the raw object data.
    modeling_tower_object_datum :=
      function( subcat, object )
        local nr_support, support, components, list_nr_elements;
        
        nr_support := NrSupport( object );
        support := Support( object );
        components := Components( object );
        
        # Turn the objects of C into integers.
        list_nr_elements :=
            List( [ 1 .. nr_support ], n ->
                NumberElements( components[n] ) );
                
        return NTuple( 3, nr_support, support, list_nr_elements );
        
    end;
    
    ## From the raw morphism data to the morphism in the modeling category.
    modeling_tower_morphism_constructor :=
      function( subcat, source, triple, target )
        local product_ins_mat, C, nr_support, support, list_nr_blockcols_blockcols, source_components, morphisms;
        
        product_ins_mat := ModelingCategory( subcat );
        
        C := UnderlyingCartesianCategory( product_ins_mat );
        
        nr_support := triple[1];
        support := triple[2];
        
        # A list of the form:
        # [
        #   [ m, [ [a,b], ..., [c,d] ] ],
        #                  .
        #                  .
        #                  .
        #   [ n, [ [e,f], ..., [g,h] ] ]
        # ]
        list_nr_blockcols_blockcols := triple[3];
        
        source_components := Components( source );
        
        # Turn the lists of block columns into morphisms of C.
        # We need to extract the target, i.e., the number of columns (not block columns!),
        # from 'list_nr_blockcols_blockcols', since some objects in 'target' might
        # be terminal objects, and hence not available (sparse datastructure).
        #
        # Note: source_components[n] = list_nr_blockcols_blockcols[n][1].
        #       so we do not need to call Component( source, n ).
        morphisms :=
            List( [ 1 .. nr_support ], n ->
                MorphismConstructor( C,
                    source_components[n],
                    list_nr_blockcols_blockcols[n],
                    Component( target, support[n] ) ) );
                    
        return MorphismConstructor( product_ins_mat,
                    source,
                    NTuple( 3, nr_support, support, morphisms ),
                    target );
                    
    end;
    
    ## From the morphism in the modeling category to the raw morphism data
    modeling_tower_morphism_datum :=
      function( subcat, morphism )
        local nr_support, support, morphisms, list_nr_blockcols_blockcols;
        
        nr_support := NrSupport( morphism );
        support := Support( morphism );
        morphisms := Components( morphism );
        
        # Unpack the morphisms of C.
        list_nr_blockcols_blockcols :=
            List( [ 1 .. nr_support ], n ->
                NrBlockColumnsAndListOfBlockColumns( morphisms[n] ) );
        
        return NTuple( 3, nr_support, support, list_nr_blockcols_blockcols );
        
    end;
    
    subcat :=
        ReinterpretationOfCategory( product_ins_mat,
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
    
    SetUnderlyingIrreducibleCharacters( subcat, irreducible_characters );
    
    SetNrIrreducibleCharacters( subcat, nr_irreducible_characters );
    
    Append( subcat!.compiler_hints.category_attribute_names,
        [ "NrIrreducibleCharacters",
          "UnderlyingIrreducibleCharacters" ] );
          
    ## See AddTensorProductOnObjects in
    ## SkeletalCategoryOfGroupRepresentations.gi
    ##
    ## DirectSum -> DirectProduct
    AddTensorProductOnObjects( subcat,
      function( subcat, object_1, object_2 )
        local product_ins_mat, ins_mat, model_1, model_2, nr_support_1, nr_support_2, support_1, support_2, components_1, components_2, product;
        
        product_ins_mat := ModelingCategory( subcat );
        
        ins_mat := UnderlyingCartesianCategory( product_ins_mat );
        
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
                        TensorProductOnObjects( ins_mat, components_1[i], components_2[j] );
                        
                    decomposition := ProductOfCharactersAsObjectInModelingProductCategory( subcat, support_1[i], support_2[j] );
                    
                    decomposition_nr_support := NrSupport( decomposition );
                    
                    decomposition_support := Support( decomposition );
                    
                    decomposition_components := Components( decomposition );
                    
                    decomposition_components :=
                        List( [ 1 .. decomposition_nr_support ], n ->
                            TensorProductOnObjects( ins_mat, decomposition_components[n], multiplicity_of_product ) );
                            
                    result :=
                        ObjectConstructor( product_ins_mat,
                            NTuple( 3,
                                decomposition_nr_support,
                                decomposition_support,
                                decomposition_components ) );
                                
                    return ReinterpretationOfObject( subcat, result );
                    
                end ) ) ) );
                
        return product;
        
    end );
    
    ## See AddTensorProductOnMorphismsWithGivenTensorProducts in
    ## SkeletalCategoryOfGroupRepresentations.gi
    ##
    ## DirectSum -> DirectProduct
    ## DirectSumFunctorial -> DirectProductFunctorial
    AddTensorProductOnMorphismsWithGivenTensorProducts( subcat,
      function( subcat, source, alpha, gamma, target )
        local product_ins_mat, ins_mat, nr_irreducible_characters, irreducible_characters, alpha_model, gamma_model, length_alpha, length_gamma, support_alpha, support_gamma, components_alpha, components_gamma, tensored_morphisms_matrix, support, length_support, indices_tensored_morphisms, tensored_morphisms, products_of_morphisms, positions, list_nr_blockcols_blockcols;
        
        product_ins_mat := ModelingCategory( subcat );
        
        ins_mat := UnderlyingCartesianCategory( product_ins_mat );
        
        irreducible_characters := UnderlyingIrreducibleCharacters( subcat );
        nr_irreducible_characters := NrIrreducibleCharacters( subcat );
        
        alpha_model := ModelingMorphism( subcat, alpha );
        gamma_model := ModelingMorphism( subcat, gamma );
        
        length_alpha := NrSupport( alpha_model );
        length_gamma := NrSupport( gamma_model );
        
        support_alpha := Support( alpha_model );
        support_gamma := Support( gamma_model );
        
        components_alpha := Components( alpha_model );
        components_gamma := Components( gamma_model );
        
        support := Union2( Support( source ), Support( target ) );
        
        length_support := Length( support );
        
        # A matrix with elements
        # [ [ ɑ₁⊗ɣ₁ ], ..., [ ɑ₁⊗ɣₗ ] ].
        # [     .                .
        # [     .        .       .
        # [     .                .
        # [ [ ɑₙ⊗ɣ₁ ], ..., [ ɑₙ⊗ɣₗ ] ].
        tensored_morphisms :=
            List( [ 1 .. length_alpha ], i ->
                List( [ 1 .. length_gamma ], j ->
                    TensorProductOnMorphisms( ins_mat, components_alpha[i], components_gamma[j] ) ) );
                    
        # (ɑ⊗ɣ)ₖ := 𝚷ᵢ 𝚷ⱼ (ɑᵢ⊗ɣⱼ⊗Iₙ₍ᵢⱼ₎ₖ)
        products_of_morphisms :=
            List( [ 1 .. length_support ],
              function( k )
                local alpha_gamma_identity, nr_rows, nr_cols, list_of_sources, list_of_targets, inner_products, outer_product;
                
                # Precompute the tensor products (ɑᵢ⊗ɣⱼ)⊗Iₙ₍ᵢⱼ₎ₖ
                alpha_gamma_identity :=
                    List( [ 1 .. length_alpha ], i ->
                        List( [ 1 .. length_gamma ],
                          function( j )
                            local n_ijk, alpha_gamma, identity_morphism, direct_sum;
                            
                            # n₍ᵢⱼ₎ₖ = ⟨χᵢ·χⱼ,χₖ⟩
                            n_ijk := SGREPS_ScalarProduct( irreducible_characters, support[k], support_alpha[i], support_gamma[j] );
                            
                            # If n₍ᵢⱼ₎ₖ = 0, then Iₙ₍ᵢⱼ₎ₖ = 0 so (ɑᵢ⊗ɣⱼ)⊗Iₙ₍ᵢⱼ₎ₖ = 0.
                            # 
                            # if n_ijl = 0 then
                            #
                            #     return ZeroMorphism( ins_mat, ZeroObject( ins_mat ), ZeroObject( ins_mat ) );
                            #
                            # fi;
                            
                            # ɑᵢ⊗ɣⱼ
                            alpha_gamma := tensored_morphisms[i][j];
                            
                            # Iₙ₍ᵢⱼ₎ₖ
                            identity_morphism :=
                                IdentityMorphism( ins_mat, ObjectConstructor( ins_mat, n_ijk ) );
                                
                            # (ɑᵢ⊗ɣⱼ)⊗Iₙ₍ᵢⱼ₎ₖ
                            return TensorProductOnMorphisms( ins_mat, alpha_gamma, identity_morphism );
                            
                          end ) );
                          
                nr_rows := Length( alpha_gamma_identity );
                nr_cols := Length( alpha_gamma_identity[1] );
                
                # Compute the inner products: 𝚷ⱼ (ɑᵢ⊗ɣⱼ⊗Iₙ₍ᵢⱼ₎ₖ)
                
                list_of_sources :=
                    List( [ 1 .. nr_rows ], i ->
                        List( [ 1 .. nr_cols ], j ->
                            Source( alpha_gamma_identity[i][j] ) ) );
                            
                list_of_targets :=
                    List( [ 1 .. nr_rows ], i ->
                        List( [ 1 .. nr_cols ], j ->
                            Target( alpha_gamma_identity[i][j] ) ) );
                            
                inner_products :=
                    List( [ 1 .. nr_rows ], i ->
                        DirectProductFunctorialWithGivenDirectProducts( ins_mat,
                            DirectProduct( ins_mat, list_of_sources[i] ),
                            list_of_sources[i],
                            alpha_gamma_identity[i],
                            list_of_targets[i],
                            DirectProduct( ins_mat, list_of_targets[i] ) ) );
                            
                # Compute the outer product: 𝚷ᵢ 𝚷ⱼ (ɑᵢ⊗ɣⱼ⊗Iₙ₍ᵢⱼ₎ₖ).
                
                outer_product :=
                    DirectProductFunctorialWithGivenDirectProducts( ins_mat,
                        Component( ModelingObject( subcat, source ), k ),
                        List( [ 1 .. Length( inner_products ) ], i -> Source( inner_products[i] ) ),
                        inner_products,
                        List( [ 1 .. Length( inner_products ) ], i -> Target( inner_products[i] ) ),
                        Component( ModelingObject( subcat, target ), k ) );
                        
                return outer_product;
                
            end );
            
        list_nr_blockcols_blockcols :=
            List( [ 1 .. length_support ], i ->
                NrBlockColumnsAndListOfBlockColumns( products_of_morphisms[i] ) );;
                
        return MorphismConstructor( subcat,
                    source,
                    NTuple(3,
                        length_support,
                        support,
                        list_nr_blockcols_blockcols ),
                    target );
                    
    end );
    
    # TODO: Should be a derivation in CartesianMonoidal
    # The following compiles in 15m57s
    # AddRightDistributivityExpandingWithGivenObjects( subcat,
    #   function( subcat, source, L, a, target )
    #     local nr_L, projection_list, projection_list_tensored, id, diagram;
    #
    #     nr_L := Length( L );
    #
    #     id := IdentityMorphism( subcat, a );
    #
    #     projection_list :=
    #         List( [ 1 .. nr_L ], i ->
    #             ProjectionInFactorOfDirectProduct( subcat, L, i ) );
    #
    #     diagram :=
    #         List( [ 1 .. nr_L ], i ->
    #             TensorProductOnObjects( subcat, L[i], a ) );
    #
    #     projection_list_tensored :=
    #         List( [ 1 .. nr_L ], i ->
    #             TensorProductOnMorphismsWithGivenTensorProducts( subcat,
    #                 source,
    #                 projection_list[i],
    #                 id,
    #                 diagram[i] ) );
    #
    #     return UniversalMorphismIntoDirectProductWithGivenDirectProduct( subcat, diagram, source, projection_list_tensored, target );
    #
    # end );
    # TODO: math comments
    # The following compiles in 43s
    AddRightDistributivityExpandingWithGivenObjects( subcat,
      function( subcat, source, L, a, L_tensor_a )
        local model, ins_mat, irreducible_characters, L_length, L_model, L_product_model, L_product_nr_support, L_product_support, L_product_components, a_model, a_nr_support, a_support, a_components, L_tensor_a_model, L_tensor_a_nr_support, L_tensor_a_support, L_tensor_a_components, components;

        model := ModelingCategory( subcat );
        ins_mat := UnderlyingCartesianCategory( model );

        irreducible_characters := UnderlyingIrreducibleCharacters( subcat );

        L_length := Length( L );

        L_model := List( L, object -> ModelingObject( subcat, object ) );

        L_product_model := DirectProduct( model, L_model );
        L_product_nr_support := NrSupport( L_product_model );
        L_product_support := Support( L_product_model );
        L_product_components := Components( L_product_model );

        a_model := ModelingObject( subcat, a );
        a_nr_support := NrSupport( a_model );
        a_support := Support( a_model );
        a_components := Components( a_model );

        L_tensor_a_model := ModelingObject( subcat, L_tensor_a );
        L_tensor_a_nr_support := NrSupport( L_tensor_a_model );
        L_tensor_a_support := Support( L_tensor_a_model );
        L_tensor_a_components := Components( L_tensor_a_model );

        components := List( [ 1 .. L_tensor_a_nr_support ], function( k )
            local product_morphisms, universal_mor;

            product_morphisms := List( [ 1 .. L_length ], function( l )
                local projection_l, tensored_morphisms, sources, targets;

                projection_l :=
                    ProjectionInFactorOfDirectProductWithGivenDirectProduct( model, L_model, l, L_product_model );

                tensored_morphisms := Concatenation( List( [ 1 .. L_product_nr_support ], function( i )
                    local projection_l_component_i;

                    projection_l_component_i := Component( projection_l, L_product_support[i] );

                    return List( [ 1 .. a_nr_support ], function( j )
                        local n_ijk, a_j_times_n_ijk, id_a_j_times_n_ijk, source, target;

                        n_ijk := ObjectConstructor( ins_mat, SGREPS_ScalarProduct( irreducible_characters, L_tensor_a_support[k], L_product_support[i], a_support[j] ) );

                        a_j_times_n_ijk := TensorProductOnObjects( ins_mat, a_components[j], n_ijk );

                        id_a_j_times_n_ijk := IdentityMorphism( ins_mat, a_j_times_n_ijk );

                        source := TensorProductOnObjects( ins_mat, Source( projection_l_component_i ), Source( id_a_j_times_n_ijk ) );
                        target := TensorProductOnObjects( ins_mat, Target( projection_l_component_i ), Target( id_a_j_times_n_ijk ) );

                        return TensorProductOnMorphismsWithGivenTensorProducts( ins_mat, source, projection_l_component_i, id_a_j_times_n_ijk, target );

                    end );

                end ) );

                sources := List( tensored_morphisms, morphism -> Source( morphism ) );
                targets := List( tensored_morphisms, morphism -> Target( morphism ) );

                return DirectProductFunctorialWithGivenDirectProducts(
                            ins_mat,
                            DirectProduct( ins_mat, sources ),
                            sources,
                            tensored_morphisms,
                            targets,
                            DirectProduct( ins_mat, targets ) );

            end );

            return UniversalMorphismIntoDirectProductWithGivenDirectProduct( ins_mat,
                        List( product_morphisms, morphism -> Target( morphism ) ),
                        L_tensor_a_components[k],
                        product_morphisms,
                        L_tensor_a_components[k] );

        end );

        return MorphismConstructor( subcat,
                    source,
                    NTuple(
                        3,
                        L_tensor_a_nr_support,
                        L_tensor_a_support,
                        List( components, NrBlockColumnsAndListOfBlockColumns ) ),
                    L_tensor_a );

    end );
    
    if CAP_NAMED_ARGUMENTS.no_precompiled_code <> true then
        
        ADD_FUNCTIONS_FOR_SparseProduct_CategoryOfInsertionMatrices_AsSubcategoryOfSkeletalGroupRepresentations_S4_precompiled( subcat );
        
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
                                [ IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ],
                                
  function( object )
    
    return TripleOfNrSupportListOfSupportListOfNumberElements( object )[1];
    
end );

InstallMethodForCompilerForCAP( NrSupport,
                                [ IsMorphismInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ],
                                
  function( morphism )
    
    return TripleOfNrSupportListOfSupportListOfNrBlockColumnsAndListOfBlockColumns( morphism )[1];
    
end );

InstallMethodForCompilerForCAP( Support,
                                [ IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ],
                                
  function( object )
    
    return TripleOfNrSupportListOfSupportListOfNumberElements( object )[2];
    
end );

InstallMethodForCompilerForCAP( Support,
                                [ IsMorphismInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ],
                                
  function( morphism )
    
    return TripleOfNrSupportListOfSupportListOfNrBlockColumnsAndListOfBlockColumns( morphism )[2];
    
end );

InstallMethodForCompilerForCAP( Components,
                                [ IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ],
                                
  function( object )
    
    return TripleOfNrSupportListOfSupportListOfNumberElements( object )[3];
    
end );

InstallMethodForCompilerForCAP( Components,
                                [ IsMorphismInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ],
                                
  function( morphism )
    
    return TripleOfNrSupportListOfSupportListOfNrBlockColumnsAndListOfBlockColumns( morphism )[3];
    
end );

####################################
##
## Operations
##
####################################

InstallMethodForCompilerForCAP( Component,
                                [ IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations,
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
                                [ IsMorphismInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations,
                                  IsBigInt ],
                                
  function( morphism, i )
    local support, list_list_columns;
    
    #% CAP_JIT_DROP_NEXT_STATEMENT
    Assert( 0, 1 <= i and i <= NrIrreducibleCharacters( CapCategory( morphism ) ) );
    
    support := Support( morphism );
    
    list_list_columns := Components( morphism );
    
    # TODO: CapJitTypedExpression
    return [ [ [ ] ], list_list_columns{ Positions( support, i ) } ][ 1 + BooleanToInteger( i in support ) ][1];
    
end );

InstallMethodForCompilerForCAP( ProductOfCharactersAsObjectInModelingProductCategory,
                                [ IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations, IsBigInt, IsBigInt ],
                                
  function( subcat, i, j )
    local product_ins_mat, ins_mat, irreducible_characters, scalar_product, support, components;
    
    product_ins_mat := ModelingCategory( subcat );
    ins_mat := UnderlyingCartesianCategory( product_ins_mat );
    
    irreducible_characters := UnderlyingIrreducibleCharacters( subcat );
    
    scalar_product := List( [ 1 .. NrIrreducibleCharacters( subcat ) ], k ->
        SGREPS_ScalarProduct( irreducible_characters, k, i, j ) );
        
    support := Filtered( [ 1 .. Length( irreducible_characters ) ], i ->
        not IsZero( scalar_product[i] ) );
        
    components :=
        List( scalar_product{ support }, character ->
            ObjectConstructor( ins_mat, character ) );
            
    return ObjectConstructor( product_ins_mat, NTuple( 3, Length( support ), support, components ) );
    
end );

####################################
##
##  Functors
##
####################################

InstallMethodForCompilerForCAP( FunctorProdInsMatIntoProdCatOfPermsOnObject,
                                [ IsSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations,
                                  IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ],
                                
  function( product_cat_of_perms, object )
    
    return ObjectConstructor( product_cat_of_perms, TripleOfNrSupportListOfSupportListOfNumberElements( object ) );
    
end );

InstallMethodForCompilerForCAP( FunctorProdInsMatIntoProdCatOfPermsOnMorphism,
                                [ IsSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations,
                                  IsMorphismInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ],
                                
  function( product_cat_of_perms, morphism )
    
    
    
end );

####################################
##
## View & Display
##
####################################

##
InstallMethod( DisplayString,
               [ IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ],
               
  object -> String( TripleOfNrSupportListOfSupportListOfNumberElements( object ) )
  
);

##
InstallMethod( Display,
               [ IsMorphismInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ],
               
  function( morphism )
    local length, support, list_list_columns, i;
    
    if IsEqualForObjects( Target( morphism ), TerminalObject( CapCategory( morphism ) ) ) then
        
        Display( "T" );
        
    else
        
        length := NrSupport( morphism );
        support := Support( morphism );
        list_list_columns := Components( morphism );
        
        for i in [ 1 .. length ] do
            
            Print( Concatenation( "Component: (", String( support[i] ), ")\n" ) );
            
            Print( "\n" );
            
            Display( list_list_columns[i] );
            
            Print( "\n------------------------\n" );
            
        od;
        
    fi;
    
end );

