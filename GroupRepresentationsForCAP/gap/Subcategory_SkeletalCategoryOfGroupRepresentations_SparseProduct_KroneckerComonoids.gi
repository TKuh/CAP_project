# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Implementations
#

#! @Chapter Semisimple Categories

ReadPackage(
    "GroupRepresentationsForCAP",
    "gap/precompiled_categories/Subcategory_SkeletalCategoryOfGroupRepresentations_S4_SparseProduct_KroneckerComonoids_precompiled.gi" );

####################################
##
## Constructors
##
####################################

##
InstallMethod( SubcategoryOfSkeletalCategoryOfGroupRepresentationsOfSparseProductOfKroneckerComonoids,
               [ IsList ],
               
  FunctionWithNamedArguments(
  [
    [ "no_precompiled_code", false ],
    [ "FinalizeCategory", true ],
  ],
  function( CAP_NAMED_ARGUMENTS, irreducible_characters )
    local name, category_filter, category_object_filter, category_morphism_filter, nr_irreducible_characters, kron_comon, product_kron_comon, object_datum_type, object_datum, object_constructor, morphism_datum_type, morphism_datum, morphism_constructor, modeling_tower_object_datum, modeling_tower_object_constructor, modeling_tower_morphism_datum, modeling_tower_morphism_constructor, subcat, product_permcat, F_product_permcat;
    
    ##
    name := Concatenation( "Reinterp( 𝚷( ", String( Length( irreducible_characters ) ), ", KroneckerComonoids ) )" );
    
    ##
    category_filter := IsSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfKroneckerComonoids;
    category_object_filter := IsObjectInSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfKroneckerComonoids;
    category_morphism_filter := IsMorphismInSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfKroneckerComonoids;
    
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
    
    kron_comon :=
        CategoryOfKroneckerComonoids(
            : no_precompiled_code := CAP_NAMED_ARGUMENTS.no_precompiled_code,
              FinalizeCategory := true );
    
    product_kron_comon :=
        SparseProductOfCartesianCategory(
            nr_irreducible_characters,
            kron_comon
            : FinalizeCategory := true );
        
    ## From the raw object data to the object in the modeling category.
    modeling_tower_object_constructor :=
      function( subcat, triple )
        local product_kron_comon, C, nr_support, support, list_nr_elements, components;
        
        product_kron_comon := ModelingCategory( subcat );
        
        C := UnderlyingCartesianCategory( product_kron_comon );
        
        nr_support := triple[1];
        support := triple[2];
        list_nr_elements := triple[3];
        
        # Turn the integer list_nr_elements into objects of subcat.
        components :=
            List( [ 1 .. nr_support ], n ->
                ObjectConstructor( C, list_nr_elements[n] ) );
        
        return ObjectConstructor( product_kron_comon, NTuple( 3, nr_support, support, components ) );
        
    end;
    
    ## From the object in the modeling category to the raw object data.
    modeling_tower_object_datum :=
      function( subcat, object )
        local nr_support, support, components, list_nr_elements;
        
        nr_support := NrSupport( object );
        support := Support( object );
        components := Components( object );
        
        # Turn the objects of subcat into integers.
        list_nr_elements :=
            List( [ 1 .. nr_support ], n ->
                NumberElements( components[n] ) );
                
        return NTuple( 3, nr_support, support, list_nr_elements );
        
    end;
    
    ## From the raw morphism data to the morphism in the modeling category.
    modeling_tower_morphism_constructor :=
      function( subcat, source, triple, target )
        local product_kron_comon, C, nr_support, support, list_nr_blockcols_blockcols, source_components, morphisms;
        
        product_kron_comon := ModelingCategory( subcat );
        
        C := UnderlyingCartesianCategory( product_kron_comon );
        
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
        
        # Turn the lists of block columns into morphisms of subcat.
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
                    
        return MorphismConstructor( product_kron_comon,
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
        
        # Unpack the morphisms of subcat.
        list_nr_blockcols_blockcols :=
            List( [ 1 .. nr_support ], n ->
                NrBlockColumnsAndListOfBlockColumns( morphisms[n] ) );
        
        return NTuple( 3, nr_support, support, list_nr_blockcols_blockcols );
        
    end;
    
    subcat :=
        ReinterpretationOfCategory( product_kron_comon,
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
    
    product_permcat := SubcategoryOfSkeletalCategoryOfGroupRepresentationsOfSparseProductOfPermutationCategory(
                                irreducible_characters
                                : no_precompiled_code := CAP_NAMED_ARGUMENTS.no_precompiled_code );
    
    SetUnderlyingProductCategoryOfPermutationCategory( subcat, product_permcat );
    
    Append( subcat!.compiler_hints.category_attribute_names,
        [ "NrIrreducibleCharacters",
          "UnderlyingIrreducibleCharacters",
          "SubcategoryOfSparseProductOfPermutationCategory",
          "FunctorIntoSparseProductOfPermutationCategory" ] );
    
    ## See AddTensorProductOnObjects in
    ## SkeletalCategoryOfGroupRepresentations.gi
    ##
    ## DirectSum -> DirectProduct
    AddTensorProductOnObjects( subcat,
      function( subcat, object_1, object_2 )
        local product_kron_comon, kron_comon, model_1, model_2, nr_support_1, nr_support_2, support_1, support_2, components_1, components_2, product;
        
        product_kron_comon := ModelingCategory( subcat );
        
        kron_comon := UnderlyingCartesianCategory( product_kron_comon );
        
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
                        TensorProductOnObjects( kron_comon, components_1[i], components_2[j] );
                        
                    decomposition := ProductOfCharactersAsObjectInModelingProductCategory( subcat, support_1[i], support_2[j] );
                    
                    decomposition_nr_support := NrSupport( decomposition );
                    
                    decomposition_support := Support( decomposition );
                    
                    decomposition_components := Components( decomposition );
                    
                    decomposition_components :=
                        List( [ 1 .. decomposition_nr_support ], n ->
                            TensorProductOnObjects( kron_comon, decomposition_components[n], multiplicity_of_product ) );
                            
                    result :=
                        ObjectConstructor( product_kron_comon,
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
        local product_kron_comon, kron_comon, nr_irreducible_characters, irreducible_characters, alpha_model, gamma_model, alpha_nr_support, gamma_nr_support, alpha_support, gamma_support, alpha_components, gamma_components, tensored_morphisms_matrix, support, nr_support, tensored_morphisms, products_of_morphisms, positions, list_nr_blockcols_blockcols;
        
        product_kron_comon := ModelingCategory( subcat );
        
        kron_comon := UnderlyingCartesianCategory( product_kron_comon );
        
        irreducible_characters := UnderlyingIrreducibleCharacters( subcat );
        nr_irreducible_characters := NrIrreducibleCharacters( subcat );
        
        alpha_model := ModelingMorphism( subcat, alpha );
        alpha_nr_support := NrSupport( alpha_model );
        alpha_support := Support( alpha_model );
        alpha_components := Components( alpha_model );
        
        gamma_model := ModelingMorphism( subcat, gamma );
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
                    TensorProductOnMorphisms( kron_comon, alpha_components[i], gamma_components[j] ) ) );
        
        # (ɑ⊗ɣ)ₖ := 𝚷ᵢ 𝚷ⱼ (ɑᵢ⊗ɣⱼ⊗Iₙ₍ᵢⱼ₎ₖ)
        products_of_morphisms :=
            List( [ 1 .. nr_support ],
              function( k )
                local alpha_gamma_identity, nr_rows, nr_cols, sources, targets, inner_products, outer_product;
                
                # Precompute the tensor products (ɑᵢ⊗ɣⱼ)⊗Iₙ₍ᵢⱼ₎ₖ
                alpha_gamma_identity :=
                    List( [ 1 .. alpha_nr_support ], i ->
                        List( [ 1 .. gamma_nr_support ],
                          function( j )
                            local n_ijk, alpha_gamma, identity_morphism, source, target;
                            
                            # n₍ᵢⱼ₎ₖ = ⟨χᵢ·χⱼ,χₖ⟩
                            n_ijk := SGREPS_ScalarProduct( irreducible_characters, support[k], alpha_support[i], gamma_support[j] );
                            
                            # If n₍ᵢⱼ₎ₖ = 0, then Iₙ₍ᵢⱼ₎ₖ = 0 so (ɑᵢ⊗ɣⱼ)⊗Iₙ₍ᵢⱼ₎ₖ = 0.
                            # 
                            # if n_ijl = 0 then
                            #
                            #     return ZeroMorphism( kron_comon, ZeroObject( kron_comon ), ZeroObject( kron_comon ) );
                            #
                            # fi;
                            
                            n_ijk := ObjectConstructor( kron_comon, n_ijk );
                            
                            # ɑᵢ⊗ɣⱼ
                            alpha_gamma := tensored_morphisms[i][j];
                            
                            # Iₙ₍ᵢⱼ₎ₖ
                            identity_morphism := IdentityMorphism( kron_comon, n_ijk );
                            
                            source := TensorProductOnObjects( kron_comon, Source( alpha_gamma ), n_ijk );
                            target := TensorProductOnObjects( kron_comon, Target( alpha_gamma ), n_ijk );
                            
                            # (ɑᵢ⊗ɣⱼ)⊗Iₙ₍ᵢⱼ₎ₖ
                            return CATEGORY_OF_KRONECKER_COMONOIDS_TensorProductOfMorphismWithIdentityWithGivenTensorProducts( kron_comon, source, alpha_gamma, identity_morphism, target );
                            
                          end ) );
                          
                nr_rows := Length( alpha_gamma_identity );
                nr_cols := Length( alpha_gamma_identity[1] );
                
                # Compute the inner products: 𝚷ⱼ (ɑᵢ⊗ɣⱼ⊗Iₙ₍ᵢⱼ₎ₖ)
                
                sources :=
                    List( [ 1 .. nr_rows ], i ->
                        List( [ 1 .. nr_cols ], j ->
                            Source( alpha_gamma_identity[i][j] ) ) );
                
                targets :=
                    List( [ 1 .. nr_rows ], i ->
                        List( [ 1 .. nr_cols ], j ->
                            Target( alpha_gamma_identity[i][j] ) ) );
                
                inner_products :=
                    List( [ 1 .. nr_rows ], i ->
                        DirectProductFunctorialWithGivenDirectProducts( kron_comon,
                            DirectProduct( kron_comon, sources[i] ),
                            sources[i],
                            alpha_gamma_identity[i],
                            targets[i],
                            DirectProduct( kron_comon, targets[i] ) ) );
                
                # Compute the outer product: 𝚷ᵢ 𝚷ⱼ (ɑᵢ⊗ɣⱼ⊗Iₙ₍ᵢⱼ₎ₖ).
                
                outer_product :=
                    DirectProductFunctorialWithGivenDirectProducts( kron_comon,
                        Component( ModelingObject( subcat, source ), support[k] ),
                        List( [ 1 .. nr_rows ], i -> Source( inner_products[i] ) ),
                        inner_products,
                        List( [ 1 .. nr_rows ], i -> Target( inner_products[i] ) ),
                        Component( ModelingObject( subcat, target ), support[k] ) );
                
                return outer_product;
                
            end );
            
        list_nr_blockcols_blockcols :=
            List( [ 1 .. nr_support ], i ->
                NrBlockColumnsAndListOfBlockColumns( products_of_morphisms[i] ) );;
        
        return MorphismConstructor( subcat,
                    source,
                    NTuple(3,
                        nr_support,
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
        local model, kron_comon, irreducible_characters, L_length, L_model, L_product_model, L_product_nr_support, L_product_support, L_product_components, a_model, a_nr_support, a_support, a_components, L_tensor_a_model, L_tensor_a_nr_support, L_tensor_a_support, L_tensor_a_components, projections, projections_components, result_components;

        model := ModelingCategory( subcat );
        kron_comon := UnderlyingCartesianCategory( model );

        irreducible_characters := UnderlyingIrreducibleCharacters( subcat );

        L_length := Length( L );

        L_model := List( L, object -> ModelingObject( subcat, object ) );

        # TODO: for the associator morphisms we will have
        #       L_product := DirectProduct( DecompositionIntoSimpleObjects( L_product ) ),
        #       which the compiler should recognize as superflous?
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

        projections := List( [ 1 .. L_length ], l ->
            ProjectionInFactorOfDirectProductWithGivenDirectProduct( model, L_model, l, L_product_model ) );

        projections_components :=
            List( [ 1 .. L_length ], l ->
                List( [ 1 .. L_product_nr_support ], i ->
                    Component( projections[l], L_product_support[i] ) ) );

        result_components := List( [ 1 .. L_tensor_a_nr_support ], function( k )
            local product_morphisms, universal_mor, mor, i, j;

            product_morphisms := List( [ 1 .. L_length ], function( l )
                local projection_l_components, tensored_morphisms, sources, targets, product_mor;

                projection_l_components := projections_components[l];

                tensored_morphisms := Concatenation( List( [ 1 .. L_product_nr_support ], function( i )
                    local projection_l_component_i;

                    projection_l_component_i := projection_l_components[i];

                    return List( [ 1 .. a_nr_support ], function( j )
                        local n_ijk, a_j_times_n_ijk, id_a_j_times_n_ijk, source, target;

                        n_ijk := ObjectConstructor( kron_comon, SGREPS_ScalarProduct( irreducible_characters, L_tensor_a_support[k], L_product_support[i], a_support[j] ) );

                        # if IsTerminal( n_ijk ) then
                        #
                        #     return IdentityMorphism( kron_comon, TerminalObject( kron_comon ) );
                        #
                        # fi;

                        a_j_times_n_ijk := TensorProductOnObjects( kron_comon, a_components[j], n_ijk );

                        id_a_j_times_n_ijk := IdentityMorphism( kron_comon, a_j_times_n_ijk );

                        source := TensorProductOnObjects( kron_comon, Source( projection_l_component_i ), Source( id_a_j_times_n_ijk ) );
                        target := TensorProductOnObjects( kron_comon, Target( projection_l_component_i ), Target( id_a_j_times_n_ijk ) );

                        return CATEGORY_OF_KRONECKER_COMONOIDS_TensorProductOfMorphismWithIdentityWithGivenTensorProducts( kron_comon, source, projection_l_component_i, id_a_j_times_n_ijk, target );

                    end );

                end ) );

                sources := List( tensored_morphisms, Source );
                targets := List( tensored_morphisms, Target );

                product_mor := DirectProductFunctorialWithGivenDirectProducts( kron_comon,
                                    DirectProduct( kron_comon, sources ),
                                    sources,
                                    tensored_morphisms,
                                    targets,
                                    DirectProduct( kron_comon, targets ) );

                # for mor in tensored_morphisms do
                #     Print( "k: ", k, ", l: ", l, ", " );
                #     Print( "source: " );
                #     Display( Source( mor ) );
                #     Print( ", target: " );
                #     Display( Target( mor ) );
                #     Print( ", " );
                #     Display( mor );
                #     Print( "\n" );
                # od;
                # Print( "Product: " );
                # Display( product_mor );
                # Print( "\n\n" );

                return product_mor;

            end );

            universal_mor :=
                UniversalMorphismIntoDirectProductWithGivenDirectProduct( kron_comon,
                    List( product_morphisms, morphism -> Target( morphism ) ),
                    L_tensor_a_components[k],
                    product_morphisms,
                    L_tensor_a_components[k] );

            return universal_mor;

        end );

        return MorphismConstructor( subcat,
                    source,
                    NTuple(
                        3,
                        L_tensor_a_nr_support,
                        L_tensor_a_support,
                        List( result_components, NrBlockColumnsAndListOfBlockColumns ) ),
                    L_tensor_a );

    end );
    
    AddLeftDistributivityExpandingWithGivenObjects( subcat,
      function( subcat, source, a, L, a_tensor_L )
        local model, kron_comon, irreducible_characters, L_length, L_model, L_product_model, L_product_nr_support, L_product_support, L_product_components, a_model, a_nr_support, a_support, a_components, id_a_model, id_a_components, a_tensor_L_model, a_tensor_L_nr_support, a_tensor_L_support, a_tensor_L_components, zero, projections, projections_components, result_components;

        #% CAP_JIT_RESOLVE_FUNCTION
        
        model := ModelingCategory( subcat );
        kron_comon := UnderlyingCartesianCategory( model );

        irreducible_characters := UnderlyingIrreducibleCharacters( subcat );

        L_length := Length( L );

        L_model := List( L, object -> ModelingObject( subcat, object ) );

        # TODO: for the associator morphisms we will have
        #       L_product := DirectProduct( DecompositionIntoSimpleObjects( L_product ) ),
        #       which the compiler should recognize as superfluous.
        L_product_model := DirectProduct( model, L_model );
        L_product_nr_support := NrSupport( L_product_model );
        L_product_support := Support( L_product_model );
        L_product_components := Components( L_product_model );

        a_model := ModelingObject( subcat, a );
        a_nr_support := NrSupport( a_model );
        a_support := Support( a_model );
        a_components := Components( a_model );

        id_a_model := IdentityMorphism( model, a_model );
        id_a_components := Components( id_a_model );

        a_tensor_L_model := ModelingObject( subcat, a_tensor_L );
        a_tensor_L_nr_support := NrSupport( a_tensor_L_model );
        a_tensor_L_support := Support( a_tensor_L_model );
        a_tensor_L_components := Components( a_tensor_L_model );

        zero := TerminalObject( kron_comon );

        projections := List( [ 1 .. L_length ], l ->
            ProjectionInFactorOfDirectProductWithGivenDirectProduct( model, L_model, l, L_product_model ) );
        
        projections_components :=
            List( [ 1 .. L_length ], l ->
                List( [ 1 .. L_product_nr_support ], j ->
                    Component( projections[l], L_product_support[j] ) ) );

        result_components := List( [ 1 .. a_tensor_L_nr_support ], function( k )
            local product_morphisms, universal_mor, mor, i, j;

            product_morphisms := List( [ 1 .. L_length ], function( l )
                local tensored_morphisms, sources, targets, mor, product_mor;

                tensored_morphisms := Concatenation( List( [ 1 .. a_nr_support ], function( i )
                    local id_a_component_i, projection_l_components;

                    id_a_component_i := id_a_components[i];
                    
                    projection_l_components := projections_components[l];

                    return List( [ 1 .. L_product_nr_support ], function( j )
                        local n_ijk, id_n_ijk, projection_l_component_j, proj_times_id_n_ijk, result;

                        n_ijk := ObjectConstructor( kron_comon, SGREPS_ScalarProduct( irreducible_characters, a_tensor_L_support[k], a_support[i], L_product_support[j] ) );

                        # if IsTerminal( n_ijk ) then
                        #
                        #     return IdentityMorphism( kron_comon, zero );
                        #
                        # fi;

                        id_n_ijk := IdentityMorphism( kron_comon, n_ijk );

                        projection_l_component_j := projection_l_components[j];

                        proj_times_id_n_ijk := CATEGORY_OF_KRONECKER_COMONOIDS_TensorProductOfMorphismWithIdentityWithGivenTensorProducts( kron_comon,
                                                    TensorProductOnObjects( kron_comon, Source( projection_l_component_j ), n_ijk ),
                                                    projection_l_component_j,
                                                    id_n_ijk,
                                                    TensorProductOnObjects( kron_comon, Target( projection_l_component_j ), n_ijk ) );

                        result := CATEGORY_OF_KRONECKER_COMONOIDS_TensorProductOfIdentityWithMorphismWithGivenTensorProducts( kron_comon,
                                        TensorProductOnObjects( kron_comon, a_components[i], Source( proj_times_id_n_ijk ) ),
                                        id_a_component_i,
                                        proj_times_id_n_ijk,
                                        TensorProductOnObjects( kron_comon, a_components[i], Target( proj_times_id_n_ijk ) ) );

                        return result;

                    end );

                end ) );

                sources := List( tensored_morphisms, Source );
                targets := List( tensored_morphisms, Target );

                product_mor := DirectProductFunctorialWithGivenDirectProducts( kron_comon,
                                    DirectProduct( kron_comon, sources ),
                                    sources,
                                    tensored_morphisms,
                                    targets,
                                    DirectProduct( kron_comon, targets ) );

                # for mor in tensored_morphisms do
                #     Print( "k: ", k, ", l: ", l, ", " );
                #     Print( "source: " );
                #     Display( Source( mor ) );
                #     Print( ", target: " );
                #     Display( Target( mor ) );
                #     Print( ", " );
                #     Display( mor );
                #     Print( "\n" );
                # od;
                # Print( "Product: " );
                # Display( product_mor );
                # Print( "\n\n" );

                return product_mor;

            end );

            return UniversalMorphismIntoDirectProductWithGivenDirectProduct( kron_comon,
                        List( product_morphisms, morphism -> Target( morphism ) ),
                        a_tensor_L_components[k],
                        product_morphisms,
                        a_tensor_L_components[k] );

        end );

        return MorphismConstructor( subcat,
                    source,
                    NTuple(
                        3,
                        a_tensor_L_nr_support,
                        a_tensor_L_support,
                        List( result_components, NrBlockColumnsAndListOfBlockColumns ) ),
                    a_tensor_L );

    end );
    
    F_product_permcat := CapFunctor( Concatenation( "Functor from Core( ",
                                              Name( subcat ),
                                              " ) to ",
                                              Name( product_permcat ) ),
                               subcat,
                               product_permcat );
    
    AddObjectFunction( F_product_permcat,
      function( object )
        local product_permcat;
        
        product_permcat := UnderlyingProductCategoryOfPermutationCategory( CapCategory( object ) );
        
        return ObjectConstructor( product_permcat, TripleOfNrSupportListOfSupportListOfNumberElements( object ) );
        
    end );
    
    AddMorphismFunction( F_product_permcat,
      function( source, morphism, target )
        local product_permcat, nr_support, support, components, permutations;
        
        product_permcat := UnderlyingProductCategoryOfPermutationCategory( CapCategory( morphism ) );
        
        Assert( 0, IsEqualForObjects( product_permcat, source, target ) );
        
        nr_support := NrSupport( morphism );
        support := Support( morphism );
        components := Components( morphism );
        
        # Convert all the component-morphisms into permutations.
        permutations := List( [ 1 .. nr_support ], function( i )
            local nr_blockcols, blockcols, l;
            
            nr_blockcols := components[i][1];
            blockcols := components[i][2];
            
            l := List( [ 1 .. nr_blockcols ], function( j )
                local blockcol;
                
                blockcol := blockcols[j];
                
                return [ [ blockcol[1] .. blockcol[2] ], [ blockcol[1] ] ][ BooleanToInteger( blockcol[1] = blockcol[2] ) + 1 ];
                
            end );
            
            return PermList( Concatenation( l ) );
            
        end );
        
        return MorphismConstructor( product_permcat,
                    source,
                    NTuple( 3, nr_support, support, permutations ),
                    target );
        
    end );
    
    SetIsomorphismFromCoreToProductCategoryOfPermutationCategory( subcat, F_product_permcat );
    
    if CAP_NAMED_ARGUMENTS.no_precompiled_code <> true then
        
        ADD_FUNCTIONS_FOR_Subcategory_SkeletalCategoryOfGroupRepresentations_S4_SparseProduct_KroneckerComonoids_precompiled( subcat );
        
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
                                [ IsObjectInSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfKroneckerComonoids ],
                                
  function( object )
    
    return TripleOfNrSupportListOfSupportListOfNumberElements( object )[1];
    
end );

InstallMethodForCompilerForCAP( NrSupport,
                                [ IsMorphismInSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfKroneckerComonoids ],
                                
  function( morphism )
    
    return TripleOfNrSupportListOfSupportListOfNrBlockColumnsAndListOfBlockColumns( morphism )[1];
    
end );

InstallMethodForCompilerForCAP( Support,
                                [ IsObjectInSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfKroneckerComonoids ],
                                
  function( object )
    
    return TripleOfNrSupportListOfSupportListOfNumberElements( object )[2];
    
end );

InstallMethodForCompilerForCAP( Support,
                                [ IsMorphismInSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfKroneckerComonoids ],
                                
  function( morphism )
    
    return TripleOfNrSupportListOfSupportListOfNrBlockColumnsAndListOfBlockColumns( morphism )[2];
    
end );

InstallMethodForCompilerForCAP( Components,
                                [ IsObjectInSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfKroneckerComonoids ],
                                
  function( object )
    
    return TripleOfNrSupportListOfSupportListOfNumberElements( object )[3];
    
end );

InstallMethodForCompilerForCAP( Components,
                                [ IsMorphismInSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfKroneckerComonoids ],
                                
  function( morphism )
    
    return TripleOfNrSupportListOfSupportListOfNrBlockColumnsAndListOfBlockColumns( morphism )[3];
    
end );

####################################
##
## Operations
##
####################################

InstallMethodForCompilerForCAP( Component,
                                [ IsObjectInSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfKroneckerComonoids,
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
                                [ IsMorphismInSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfKroneckerComonoids,
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
                                [ IsSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfKroneckerComonoids, IsBigInt, IsBigInt ],
                                
  function( subcat, i, j )
    local product_kron_comon, kron_comon, irreducible_characters, scalar_product, support, components;
    
    product_kron_comon := ModelingCategory( subcat );
    kron_comon := UnderlyingCartesianCategory( product_kron_comon );
    
    irreducible_characters := UnderlyingIrreducibleCharacters( subcat );
    
    scalar_product := List( [ 1 .. NrIrreducibleCharacters( subcat ) ], k ->
        SGREPS_ScalarProduct( irreducible_characters, k, i, j ) );
        
    support := Filtered( [ 1 .. Length( irreducible_characters ) ], i ->
        not IsZero( scalar_product[i] ) );
        
    components :=
        List( scalar_product{ support }, character ->
            ObjectConstructor( kron_comon, character ) );
            
    return ObjectConstructor( product_kron_comon, NTuple( 3, Length( support ), support, components ) );
    
end );

# TODO: can this be removed?
InstallMethodForCompilerForCAP( DecompositionIntoSimpleObjects,
                                [ IsObjectInSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfKroneckerComonoids ],
                                
  function( object )
    local subcat, nr_support, support, components;
    
    subcat := CapCategory( object );
    
    nr_support := NrSupport( object );
    support := Support( object );
    components := Components( object );
    
    return Concatenation( List( [ 1 .. nr_support ], i ->
        List( [ 1 .. components[i] ], j ->
            ObjectConstructor( subcat, NTuple( 3, 1, [ support[i] ], [ 1 ] ) ) ) ) );
    
end );

####################################
##
## Global functions
##
####################################

InstallGlobalFunction( PRODUCT_OF_CATEGORY_OF_KRONECKER_COMONOIDS_AS_SUBCAT_TensorProductOfMorphismWithIdentityWithGivenTensorProducts,
  function( subcat, source, morphism, identity, target )
    local product_kron_comon, kron_comon, nr_irreducible_characters, irreducible_characters, morphism_model, identity_model, morphism_nr_support, identity_nr_support, morphism_support, identity_support, morphism_components, identity_components, tensored_morphisms_matrix, support, nr_support, products_of_morphisms, positions, list_nr_blockcols_blockcols;
    
    product_kron_comon := ModelingCategory( subcat );
    kron_comon := UnderlyingCartesianCategory( product_kron_comon );
    
    irreducible_characters := UnderlyingIrreducibleCharacters( subcat );
    nr_irreducible_characters := NrIrreducibleCharacters( subcat );
    
    morphism_model := ModelingMorphism( subcat, morphism );
    morphism_nr_support := NrSupport( morphism_model );
    morphism_support := Support( morphism_model );
    morphism_components := Components( morphism_model );
    
    identity_model := ModelingMorphism( subcat, identity );
    identity_support := Support( identity_model );
    identity_nr_support := NrSupport( identity_model );
    identity_components := Components( identity_model );
    
    support := Union2( Support( source ), Support( target ) );
    
    nr_support := Length( support );
    
    # (M⊗I)ₖ := 𝚷ᵢ 𝚷ⱼ (Mᵢ⊗Iⱼ⊗Iₙ₍ᵢⱼ₎ₖ)
    products_of_morphisms :=
        List( [ 1 .. nr_support ],
          function( k )
            local morphism_identity_identity, nr_rows, nr_cols, sources, targets, inner_products, outer_product;
            
            # Precompute the tensor products Mᵢ⊗(Iⱼ⊗Iₙ₍ᵢⱼ₎ₖ)
            morphism_identity_identity :=
                List( [ 1 .. morphism_nr_support ], function( i )
                    local components_morphism_i, source_morphism_i, target_morphism_i;
                    
                    components_morphism_i := morphism_components[i];
                    source_morphism_i := Source( components_morphism_i );
                    target_morphism_i := Target( components_morphism_i );
                    
                    return List( [ 1 .. identity_nr_support ], function( j )
                        local n_ijk, dimension_identity_j, dimension_identity_j_times_n_ijk, identity_j_times_identity_nijk, source, target;
                        
                        # n₍ᵢⱼ₎ₖ = ⟨χᵢ·χⱼ,χₖ⟩
                        n_ijk := SGREPS_ScalarProduct( irreducible_characters, support[k], morphism_support[i], identity_support[j] );
                        
                        # If n₍ᵢⱼ₎ₖ = 0, then Iₙ₍ᵢⱼ₎ₖ = 0 so (Mᵢ⊗Iⱼ)⊗Iₙ₍ᵢⱼ₎ₖ = 0.
                        # 
                        # if n_ijl = 0 then
                        #
                        #     return ZeroMorphism( kron_comon, ZeroObject( kron_comon ), ZeroObject( kron_comon ) );
                        #
                        # fi;
                        
                        n_ijk := ObjectConstructor( kron_comon, n_ijk );
                        
                        dimension_identity_j := Source( identity_components[j] );
                        
                        dimension_identity_j_times_n_ijk := TensorProductOnObjects( kron_comon, dimension_identity_j, n_ijk );
                        
                        # Iⱼ ⊗ Iₙ₍ᵢⱼ₎ₖ
                        identity_j_times_identity_nijk := IdentityMorphism( kron_comon, dimension_identity_j_times_n_ijk );
                        
                        source := TensorProductOnObjects( kron_comon, source_morphism_i, dimension_identity_j_times_n_ijk );
                        target := TensorProductOnObjects( kron_comon, target_morphism_i, dimension_identity_j_times_n_ijk );
                        
                        # Mᵢ⊗(Iⱼ⊗Iₙ₍ᵢⱼ₎ₖ)
                        return CATEGORY_OF_KRONECKER_COMONOIDS_TensorProductOfMorphismWithIdentityWithGivenTensorProducts( kron_comon,
                                    source,
                                    components_morphism_i,
                                    identity_j_times_identity_nijk,
                                    target );
                        
                      end );
                end );
                
            nr_rows := Length( morphism_identity_identity );
            nr_cols := Length( morphism_identity_identity[1] );
            
            # Compute the inner products: 𝚷ⱼ (Mᵢ⊗Iⱼ⊗Iₙ₍ᵢⱼ₎ₖ)
            
            sources :=
                List( [ 1 .. nr_rows ], i ->
                    List( [ 1 .. nr_cols ], j ->
                        Source( morphism_identity_identity[i][j] ) ) );
            
            targets :=
                List( [ 1 .. nr_rows ], i ->
                    List( [ 1 .. nr_cols ], j ->
                        Target( morphism_identity_identity[i][j] ) ) );
            
            inner_products :=
                List( [ 1 .. nr_rows ], i ->
                    DirectProductFunctorialWithGivenDirectProducts( kron_comon,
                        DirectProduct( kron_comon, sources[i] ),
                        sources[i],
                        morphism_identity_identity[i],
                        targets[i],
                        DirectProduct( kron_comon, targets[i] ) ) );
            
            # Compute the outer product: 𝚷ᵢ 𝚷ⱼ (Mᵢ⊗Iⱼ⊗Iₙ₍ᵢⱼ₎ₖ).
            
            outer_product :=
                DirectProductFunctorialWithGivenDirectProducts( kron_comon,
                    Component( ModelingObject( subcat, source ), support[k] ),
                    List( [ 1 .. nr_rows ], i -> Source( inner_products[i] ) ),
                    inner_products,
                    List( [ 1 .. nr_rows ], i -> Target( inner_products[i] ) ),
                    Component( ModelingObject( subcat, target ), support[k] ) );
            
            return outer_product;
            
        end );
        
    list_nr_blockcols_blockcols :=
        List( [ 1 .. nr_support ], i ->
            NrBlockColumnsAndListOfBlockColumns( products_of_morphisms[i] ) );;
    
    return MorphismConstructor( subcat,
                source,
                NTuple(3,
                    nr_support,
                    support,
                    list_nr_blockcols_blockcols ),
                target );
    
end );

InstallGlobalFunction( PRODUCT_OF_CATEGORY_OF_KRONECKER_COMONOIDS_AS_SUBCAT_TensorProductOfIdentityWithMorphismWithGivenTensorProducts,
  function( subcat, source, identity, morphism, target )
    local product_kron_comon, kron_comon, nr_irreducible_characters, irreducible_characters, identity_model, morphism_model, identity_nr_support, morphism_nr_support, identity_support, morphism_support, identity_components, morphism_components, tensored_identities_matrix, support, nr_support, products_of_identities, positions, list_nr_blockcols_blockcols;
    
    product_kron_comon := ModelingCategory( subcat );
    kron_comon := UnderlyingCartesianCategory( product_kron_comon );
    
    irreducible_characters := UnderlyingIrreducibleCharacters( subcat );
    nr_irreducible_characters := NrIrreducibleCharacters( subcat );
    
    identity_model := ModelingMorphism( subcat, identity );
    identity_nr_support := NrSupport( identity_model );
    identity_support := Support( identity_model );
    identity_components := Components( identity_model );
    
    morphism_model := ModelingMorphism( subcat, morphism );
    morphism_support := Support( morphism_model );
    morphism_nr_support := NrSupport( morphism_model );
    morphism_components := Components( morphism_model );
    
    support := Union2( Support( source ), Support( target ) );
    
    nr_support := Length( support );
    
    # (I⊗M)ₖ := 𝚷ᵢ 𝚷ⱼ (Iᵢ⊗Mⱼ⊗Iₙ₍ᵢⱼ₎ₖ)
    products_of_identities :=
        List( [ 1 .. nr_support ],
          function( k )
            local identity_morphism_morphism, nr_rows, nr_cols, sources, targets, inner_products, outer_product;
            
            # Precompute the tensor products Iᵢ⊗(Mⱼ⊗Iₙ₍ᵢⱼ₎ₖ)
            identity_morphism_morphism :=
                List( [ 1 .. identity_nr_support ], function( i )
                    local components_identity_i, source_identity_i, target_identity_i;
                    
                    components_identity_i := identity_components[i];
                    source_identity_i := Source( components_identity_i );
                    target_identity_i := Target( components_identity_i );
                    
                    return List( [ 1 .. morphism_nr_support ], function( j )
                        local n_ijk, id_nijk, morphism_j, source_morphism_j_times_nijk, target_morphism_j_times_nijk, morphism_j_times_id_nijk, source, target;
                        
                        # n₍ᵢⱼ₎ₖ = ⟨χᵢ·χⱼ,χₖ⟩
                        n_ijk := SGREPS_ScalarProduct( irreducible_characters, support[k], identity_support[i], morphism_support[j] );
                        
                        # If n₍ᵢⱼ₎ₖ = 0, then Iₙ₍ᵢⱼ₎ₖ = 0 so (Iᵢ⊗Mⱼ)⊗Iₙ₍ᵢⱼ₎ₖ = 0.
                        # 
                        # if n_ijl = 0 then
                        #
                        #     return ZeroMorphism( kron_comon, ZeroObject( kron_comon ), ZeroObject( kron_comon ) );
                        #
                        # fi;
                        
                        # Iₙ₍ᵢⱼ₎ₖ
                        n_ijk := ObjectConstructor( kron_comon, n_ijk );
                        id_nijk := IdentityMorphism( kron_comon, n_ijk );
                        
                        # Mⱼ
                        morphism_j := morphism_components[j];
                        
                        source_morphism_j_times_nijk := TensorProductOnObjects( kron_comon, Source( morphism_j ), n_ijk );
                        target_morphism_j_times_nijk := TensorProductOnObjects( kron_comon, Target( morphism_j ), n_ijk );
                        
                        # Mⱼ ⊗ Iₙ₍ᵢⱼ₎ₖ
                        morphism_j_times_id_nijk := CATEGORY_OF_KRONECKER_COMONOIDS_TensorProductOfMorphismWithIdentityWithGivenTensorProducts( kron_comon,
                                                        source_morphism_j_times_nijk,
                                                        morphism_j,
                                                        id_nijk,
                                                        target_morphism_j_times_nijk );
                        
                        source := TensorProductOnObjects( kron_comon, source_identity_i, Source( morphism_j_times_id_nijk ) );
                        target := TensorProductOnObjects( kron_comon, target_identity_i, Target( morphism_j_times_id_nijk ) );
                        
                        # Iᵢ⊗(Mⱼ⊗Iₙ₍ᵢⱼ₎ₖ)
                        return CATEGORY_OF_KRONECKER_COMONOIDS_TensorProductOfIdentityWithMorphismWithGivenTensorProducts( kron_comon,
                                    source,
                                    components_identity_i,
                                    morphism_j_times_id_nijk,
                                    target );
                        
                      end );
                end );
                
            nr_rows := Length( identity_morphism_morphism );
            nr_cols := Length( identity_morphism_morphism[1] );
            
            # Compute the inner products: 𝚷ⱼ (Mᵢ⊗Iⱼ⊗Iₙ₍ᵢⱼ₎ₖ)
            
            sources :=
                List( [ 1 .. nr_rows ], i ->
                    List( [ 1 .. nr_cols ], j ->
                        Source( identity_morphism_morphism[i][j] ) ) );
            
            targets :=
                List( [ 1 .. nr_rows ], i ->
                    List( [ 1 .. nr_cols ], j ->
                        Target( identity_morphism_morphism[i][j] ) ) );
            
            inner_products :=
                List( [ 1 .. nr_rows ], i ->
                    DirectProductFunctorialWithGivenDirectProducts( kron_comon,
                        DirectProduct( kron_comon, sources[i] ),
                        sources[i],
                        identity_morphism_morphism[i],
                        targets[i],
                        DirectProduct( kron_comon, targets[i] ) ) );
            
            # Compute the outer product: 𝚷ᵢ 𝚷ⱼ (Mᵢ⊗Iⱼ⊗Iₙ₍ᵢⱼ₎ₖ).
            
            outer_product :=
                DirectProductFunctorialWithGivenDirectProducts( kron_comon,
                    Component( ModelingObject( subcat, source ), support[k] ),
                    List( [ 1 .. nr_rows ], i -> Source( inner_products[i] ) ),
                    inner_products,
                    List( [ 1 .. nr_rows ], i -> Target( inner_products[i] ) ),
                    Component( ModelingObject( subcat, target ), support[k] ) );
            
            return outer_product;
            
        end );
        
    list_nr_blockcols_blockcols :=
        List( [ 1 .. nr_support ], i ->
            NrBlockColumnsAndListOfBlockColumns( products_of_identities[i] ) );;
    
    return MorphismConstructor( subcat,
                source,
                NTuple(3,
                    nr_support,
                    support,
                    list_nr_blockcols_blockcols ),
                target );
    
end );

InstallGlobalFunction( RightDistributivityExpandingWithGivenMultiplicitiesAndObjects,
  function( subcat, source, L, a, multiplicities, L_tensor_a )
    local model, kron_comon, irreducible_characters, L_length, L_model, L_model_duplicated, L_product_model, L_product_nr_support, L_product_support, L_product_components, a_model, a_nr_support, a_support, a_components, L_tensor_a_model, L_tensor_a_nr_support, L_tensor_a_support, L_tensor_a_components, zero, initial_projections_components, result_components;

    #% CAP_JIT_RESOLVE_FUNCTION
    
    model := ModelingCategory( subcat );
    kron_comon := UnderlyingCartesianCategory( model );

    irreducible_characters := UnderlyingIrreducibleCharacters( subcat );
    
    L_length := Length( L );
    
    L_model := List( L, object -> ModelingObject( subcat, object ) );
    L_model_duplicated := Concatenation( List( [ 1 .. L_length ], i ->
        ListWithIdenticalEntries( multiplicities[i], L_model[i] ) ) );
    
    # TODO: for the associator morphisms we will have
    #       L_product := DirectProduct( DecompositionIntoSimpleObjects( L_product ) ),
    #       which the compiler should recognize as superfluous.
    L_product_model := DirectProduct( model, L_model_duplicated );
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
    
    zero := TerminalObject( kron_comon );
    
    # The components of all the initial projections
    # π₁, ... πₘ with m := Length(L) of the multiplicity adjusted list
    #
    #              m₁ times          mₗ times          mₘ times
    #             ┌─────────┐       ┌─────────┐       ┌─────────┐
    # L_mult := [ L₁, ..., L₁, ..., Lₗ, ..., Lₗ, ..., Lₘ, ..., Lₘ ].
    #             │                 │                 │
    #             │π₁               │πₗ               │πₘ
    #             ↓                 ↓                 ↓
    #             L₁                Lₗ                Lₘ
    #
    initial_projections_components :=
        List( [ 1 .. L_length ], function( l )
            local proj_number, projection_l;
            
            proj_number := Sum( multiplicities{[ 1 .. l-1 ]} ) + 1;
            
            projection_l := ProjectionInFactorOfDirectProductWithGivenDirectProduct( model,
                                L_model_duplicated,
                                proj_number,
                                L_product_model );
            
            return Components( projection_l );
            
        end );
    
    # ((l₁⊕...⊕lₙ)⊗a)ₖ ⥲ ((l₁⊗a)⊕...⊕(lₙ⊗a))ₖ
    result_components := List( [ 1 .. L_tensor_a_nr_support ], function( k )
        local projections_times_id_a, universal_mor, mor, i, j;
        
        # The list of tensorproducts
        #
        # (πₗ ⊗ Iₐ)ₖ := 𝚷ᵢ 𝚷ⱼ (πₗᵢ ⊗ Iₐⱼ ⊗ Iₙ₍ᵢⱼ₎ₖ),  1 <= l <= Length( L_mult ).
        #
        # with the projections πₗ for the multiplicity adjusted list L_mult.
        projections_times_id_a := Concatenation( List( [ 1 .. L_length ], function( l )
            local projection_l_components, inner_morphisms, projections_l_times_id_a, sources, targets;
            
            projection_l_components := initial_projections_components[l];
            
            # The inner morphisms πₗᵢ ⊗ Iₐⱼ ⊗ Iₙ₍ᵢⱼ₎ₖ for the tensorproduct (πₗ ⊗ Iₐ)ₖ
            # with the initial projection πₗ for the original list L (without multiplicities).
            inner_morphisms := Concatenation( List( [ 1 .. L_product_nr_support ], function( i )
                local projection_l_component_i;
                
                # πₗᵢ
                projection_l_component_i := projection_l_components[i];
                
                # [ πₗᵢ ⊗ Iₐⱼ ⊗ Iₙ₍ᵢⱼ₎ₖ ]
                return List( [ 1 .. a_nr_support ], function( j )
                    local n_ijk, a_j_times_n_ijk, id_a_j_times_n_ijk, source, target;
                    
                    n_ijk := ObjectConstructor( kron_comon, SGREPS_ScalarProduct( irreducible_characters, L_tensor_a_support[k], L_product_support[i], a_support[j] ) );
                    
                    # if IsTerminal( n_ijk ) then
                    #
                    #     return IdentityMorphism( kron_comon, zero );
                    #
                    # fi;
                    
                    a_j_times_n_ijk := TensorProductOnObjects( kron_comon, a_components[j], n_ijk );
                    
                    # Iₐⱼ ⊗ Iₙ₍ᵢⱼ₎ₖ
                    id_a_j_times_n_ijk := IdentityMorphism( kron_comon, a_j_times_n_ijk );

                    source := TensorProductOnObjects( kron_comon, Source( projection_l_component_i ), Source( id_a_j_times_n_ijk ) );
                    target := TensorProductOnObjects( kron_comon, Target( projection_l_component_i ), Target( id_a_j_times_n_ijk ) );
                    
                    # πₗᵢ ⊗ Iₐⱼ ⊗ Iₙ₍ᵢⱼ₎ₖ
                    return CATEGORY_OF_KRONECKER_COMONOIDS_TensorProductOfMorphismWithIdentityWithGivenTensorProducts( kron_comon, source, projection_l_component_i, id_a_j_times_n_ijk, target );
                    
                end );
                
            end ) );
            
            # Remove 0x0 morphisms from the list
            # of initial inner morphisms [ πₗᵢ ⊗ Iₐⱼ ⊗ Iₙ₍ᵢⱼ₎ₖ ].
            inner_morphisms := Filtered( inner_morphisms, mor ->
                not( IsEqualForObjects( kron_comon, Source( mor ), zero ) and
                     IsEqualForObjects( kron_comon, Target( mor ), zero ) ) );
            
            # We now duplicate and shift the inner morphisms
            # for the tensorproduct of the initial projection
            # πₗ with Iₐ to generate the inner morphisms
            # for the tensorproducts of the remaining projections
            # for the Lₗ's with Iₐ (of the multiplicity adjusted list L_mult).
            projections_l_times_id_a :=
                List( [ 0 .. multiplicities[l] - 1 ], function( m )
                    local shifted_mors, sources, targets, product;
                    
                    shifted_mors := List( inner_morphisms, mor ->
                        CATEGORY_OF_KRONECKER_COMONOIDS_RowDownwardShift( kron_comon, mor, m ) );
                    
                    sources := List( shifted_mors, Source );
                    targets := List( shifted_mors, Target );
                    
                    product := DirectProductFunctorialWithGivenDirectProducts( kron_comon,
                                    DirectProduct( kron_comon, sources ),
                                    sources,
                                    shifted_mors,
                                    targets,
                                    DirectProduct( kron_comon, targets ) );
                    
                    return product;
                    
                end );
            
            # for mor in inner_morphisms do
            #     Print( "k: ", k, ", l: ", l, ", " );
            #     Print( "source: " );
            #     Display( Source( mor ) );
            #     Print( ", target: " );
            #     Display( Target( mor ) );
            #     Print( ", " );
            #     Display( mor );
            #     Print( "\n" );
            # od;
            # Print( "\n" );
            # for mor in projections_l_times_id_a do
            #     Print( "k: ", k, ", l: ", l, ", " );
            #     Print( "source: " );
            #     Display( Source( mor ) );
            #     Print( ", target: " );
            #     Display( Target( mor ) );
            #     Print( ", " );
            #     Display( mor );
            #     Print( "\n" );
            # od;
            # Print( "\n" );

            return projections_l_times_id_a;
             
        end ) );
        
        #  ( (l₁⊕...⊕l₁⊕...⊕lₙ⊕...⊕lₙ) ⊗ a)ₖ
        #                 ╱⏐╲
        #                ╱ ⏐ ╲
        #               ╱  ⏐  ╲
        #              ╱   ⏐   ╲
        #       (π₁ ⊗ Iₐ)ₖ   (πₙ ⊗ Iₐ)ₖ
        #            ╱     ⏐     ╲
        #           ╱      ⏐      ╲
        #          ╱       ⏐       ╲
        #         ↓        ↓        ↓
        #     (l₁ ⊗ a)ₖ   ...   (lₘ ⊗ a)ₖ
        #
        return UniversalMorphismIntoDirectProductWithGivenDirectProduct( kron_comon,
                    List( projections_times_id_a, morphism -> Target( morphism ) ),
                    L_tensor_a_components[k],
                    projections_times_id_a,
                    L_tensor_a_components[k] );
        
    end );
    
    return MorphismConstructor( subcat,
                source,
                NTuple(
                    3,
                    L_tensor_a_nr_support,
                    L_tensor_a_support,
                    List( result_components, NrBlockColumnsAndListOfBlockColumns ) ),
                L_tensor_a );

end );

InstallGlobalFunction( LeftDistributivityExpandingWithGivenMultiplicitiesAndObjects,
  function( subcat, source, a, L, multiplicities, a_tensor_L )
    local model, kron_comon, irreducible_characters, L_length, L_model, L_model_duplicated, L_product_model, L_product_nr_support, L_product_support, L_product_components, a_model, a_nr_support, a_support, a_components, id_a_model, id_a_components, a_tensor_L_model, a_tensor_L_nr_support, a_tensor_L_support, a_tensor_L_components, zero, initial_projections_components, result_components;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    model := ModelingCategory( subcat );
    kron_comon := UnderlyingCartesianCategory( model );
    
    irreducible_characters := UnderlyingIrreducibleCharacters( subcat );
    
    L_length := Length( L );
    
    L_model := List( L, object -> ModelingObject( subcat, object ) );
    L_model_duplicated := Concatenation( List( [ 1 .. L_length ], i ->
        ListWithIdenticalEntries( multiplicities[i], L_model[i] ) ) );
    
    # TODO: for the associator morphisms we will have
    #       L_product := DirectProduct( DecompositionIntoSimpleObjects( L_product ) ),
    #       which the compiler should recognize as superfluous.
    L_product_model := DirectProduct( model, L_model_duplicated );
    L_product_nr_support := NrSupport( L_product_model );
    L_product_support := Support( L_product_model );
    L_product_components := Components( L_product_model );
    
    a_model := ModelingObject( subcat, a );
    a_nr_support := NrSupport( a_model );
    a_support := Support( a_model );
    a_components := Components( a_model );
    
    id_a_model := IdentityMorphism( model, a_model );
    id_a_components := Components( id_a_model );
    
    a_tensor_L_model := ModelingObject( subcat, a_tensor_L );
    a_tensor_L_nr_support := NrSupport( a_tensor_L_model );
    a_tensor_L_support := Support( a_tensor_L_model );
    a_tensor_L_components := Components( a_tensor_L_model );
    
    zero := TerminalObject( kron_comon );
    
    # The components of all the initial projections
    # π₁, ... πₘ with m := Length(L) of the multiplicity adjusted list
    #
    #              m₁ times          mₗ times          mₘ times
    #             ┌─────────┐       ┌─────────┐       ┌─────────┐
    # L_mult := [ L₁, ..., L₁, ..., Lₗ, ..., Lₗ, ..., Lₘ, ..., Lₘ ].
    #             │                 │                 │
    #             │π₁               │πₗ               │πₘ
    #             ↓                 ↓                 ↓
    #             L₁                Lₗ                Lₘ
    #
    initial_projections_components :=
        List( [ 1 .. L_length ], function( l )
            local proj_number, projection_l;
            
            proj_number := Sum( multiplicities{[ 1 .. l-1 ]} ) + 1;
            
            projection_l := ProjectionInFactorOfDirectProductWithGivenDirectProduct( model,
                                L_model_duplicated,
                                proj_number,
                                L_product_model );
            
            return Components( projection_l );
            
        end );
    
    # (a⊗(l₁⊕...⊕lₙ))ₖ ⥲ ((a⊗l₁)⊕...⊕(la⊗ₙ))ₖ
    result_components := List( [ 1 .. a_tensor_L_nr_support ], function( k )
        local projections_times_id_a, universal_mor, mor, i, j;
        
        # The list of tensorproducts
        #
        # (Iₐ ⊗ πₗ)ₖ := 𝚷ᵢ 𝚷ⱼ (Iₐᵢ ⊗ πₗⱼ ⊗ Iₙ₍ᵢⱼ₎ₖ),  1 <= l <= Length( L_mult ).
        #
        # with the projections πₗ for the multiplicity adjusted list L_mult.
        projections_times_id_a := Concatenation( List( [ 1 .. L_length ], function( l )
            local inner_morphisms, sources, targets, product, target_of_product_is_nonzero, range, shifts_of_product;
            
            # The inner morphisms Iₐᵢ ⊗ πₗⱼ ⊗ Iₙ₍ᵢⱼ₎ₖ for the tensorproduct (Iₐ ⊗ πₗ)ₖ
            # with the initial projection πₗ for the original list L (without multiplicities).
            inner_morphisms := Concatenation( List( [ 1 .. a_nr_support ], function( i )
                local id_a_component_i, projection_l_components, inner_morphisms_i, duplicated_tensored_morphisms;
                
                # Iₐᵢ
                id_a_component_i := id_a_components[i];
                
                # πₗ
                projection_l_components := initial_projections_components[l];
                
                # [ Iₐᵢ ⊗ πₗⱼ ⊗ Iₙ₍ᵢⱼ₎ₖ ]
                inner_morphisms_i := List( [ 1 .. L_product_nr_support ], function( j )
                    local n_ijk, id_n_ijk, projection_l_component_j, proj_times_id_n_ijk;
                    
                    n_ijk := ObjectConstructor( kron_comon, SGREPS_ScalarProduct( irreducible_characters, a_tensor_L_support[k], a_support[i], L_product_support[j] ) );
                    
                    # if IsTerminal( n_ijk ) then
                    #
                    #     return IdentityMorphism( kron_comon, zero );
                    #
                    # fi;
                    
                    # Iₙ₍ᵢⱼ₎ₖ
                    id_n_ijk := IdentityMorphism( kron_comon, n_ijk );
                    
                    # πₗⱼ
                    projection_l_component_j := projection_l_components[j];
                    
                    # πₗⱼ ⊗ Iₙ₍ᵢⱼ₎ₖ
                    proj_times_id_n_ijk := CATEGORY_OF_KRONECKER_COMONOIDS_TensorProductOfMorphismWithIdentityWithGivenTensorProducts( kron_comon,
                                                TensorProductOnObjects( kron_comon, Source( projection_l_component_j ), n_ijk ),
                                                projection_l_component_j,
                                                id_n_ijk,
                                                TensorProductOnObjects( kron_comon, Target( projection_l_component_j ), n_ijk ) );
                    
                    # Iₐᵢ ⊗ πₗⱼ ⊗ Iₙ₍ᵢⱼ₎ₖ
                    return CATEGORY_OF_KRONECKER_COMONOIDS_TensorProductOfIdentityWithMorphismWithGivenTensorProducts( kron_comon,
                                    TensorProductOnObjects( kron_comon, a_components[i], Source( proj_times_id_n_ijk ) ),
                                    id_a_component_i,
                                    proj_times_id_n_ijk,
                                    TensorProductOnObjects( kron_comon, a_components[i], Target( proj_times_id_n_ijk ) ) );
                    
                end );
                
                # Remove 0x0 morphisms from inner_morphisms_i.
                inner_morphisms_i := Filtered( inner_morphisms_i, mor ->
                    not( IsEqualForObjects( kron_comon, Source( mor ), zero ) and
                         IsEqualForObjects( kron_comon, Target( mor ), zero ) ) );
                
                return inner_morphisms_i;
            
            end ) );
            
            sources := List( inner_morphisms, Source );
            targets := List( inner_morphisms, Target );
            
            # (Iₐ ⊗ πₗ)ₖ := 𝚷ᵢ 𝚷ⱼ (Iₐᵢ ⊗ πₗⱼ ⊗ Iₙ₍ᵢⱼ₎ₖ)
            product := DirectProductFunctorialWithGivenDirectProducts( kron_comon,
                            DirectProduct( kron_comon, sources ),
                            sources,
                            inner_morphisms,
                            targets,
                            DirectProduct( kron_comon, targets ) );
            
            # We now duplicate and shift the tensorproduct (Iₐ ⊗ πₗ)ₖ
            # to generate the tensorproducts with the projections
            # for the remaining Lₗ's of the multiplicity adjusted list L_mult.
            
            # If `product` is a ?x0 morphism, then its shifts via the
            # current multiplicity are also ?x0 morphisms and hence irrelevant
            # for the UniversalMorphismIntoDirectProduct later on.
            # In that case, `range` will be equal to 0 and `shifts_of_product`
            # will become an empty list.
            # Otherwise we return a list of shifts of `product` as
            # demanded by the multiplicity for the current object at position `l`.
            target_of_product_is_nonzero := BooleanToInteger( not IsEqualForObjects( kron_comon, Target( product ), zero ) );
            range := multiplicities[l] * target_of_product_is_nonzero;
            
            shifts_of_product :=
                List( [ 0 .. range - 1 ], m ->
                    CATEGORY_OF_KRONECKER_COMONOIDS_RowDownwardShift( kron_comon, product, m ) );
            
            # Print( "k: ", k, ", l: ", l );
            # Print( ", source: " );
            # Display( Source( product ) );
            # Print( ", target: " );
            # Display( Target( product ) );
            # Print( ", product: " );
            # Display( product );
            # Print( ", is_zero: " );
            # Display( target_of_product_is_nonzero );
            # Print( "\n" );
            # Print( "shifts_of_product:\n" );
            # for mor in shifts_of_product do
            #     Print( "k: ", k, ", l: ", l );
            #     Print( ", source: " );
            #     Display( Source( mor ) );
            #     Print( ", target: " );
            #     Display( Target( mor ) );
            #     Print( ", " );
            #     Display( mor );
            #     Print( "\n" );
            # od;
            # Print( "\n" );
            
            return shifts_of_product;
            
        end ) );
        
        #  (a ⊗ (l₁⊕...⊕l₁⊕...⊕lₙ⊕...⊕lₙ))ₖ
        #                 ╱⏐╲
        #                ╱ ⏐ ╲
        #               ╱  ⏐  ╲
        #              ╱   ⏐   ╲
        #       (Iₐ ⊗ π₁)ₖ   (Iₐ ⊗ πₙ)ₖ
        #            ╱     ⏐     ╲
        #           ╱      ⏐      ╲
        #          ╱       ⏐       ╲
        #         ↓        ↓        ↓
        #     (a ⊗ l₁)ₖ   ...   (a ⊗ lₘ)ₖ
        #
        return UniversalMorphismIntoDirectProductWithGivenDirectProduct( kron_comon,
                    List( projections_times_id_a, morphism -> Target( morphism ) ),
                    a_tensor_L_components[k],
                    projections_times_id_a,
                    a_tensor_L_components[k] );
        
    end );
    
    return MorphismConstructor( subcat,
                source,
                NTuple(
                    3,
                    a_tensor_L_nr_support,
                    a_tensor_L_support,
                    List( result_components, NrBlockColumnsAndListOfBlockColumns ) ),
                a_tensor_L );
    
end );

####################################
##
## View & Display
##
####################################

##
InstallMethod( DisplayString,
               [ IsObjectInSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfKroneckerComonoids ],
               
  object -> String( TripleOfNrSupportListOfSupportListOfNumberElements( object ) )
  
);

##
InstallMethod( Display,
               [ IsMorphismInSubcategoryOfSkeletalGroupRepresentationsOfSparseProductOfKroneckerComonoids ],
               
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

