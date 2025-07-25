# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Implementations
#
#! @Chapter Semisimple Categories

####################################
##
## Constructors
##
####################################

# InstallMethod( SGRepObject,
#                [ IsSkeletalCategoryOfGroupRepresentations, IsList ],
#
#   function( SGReps, pairs_of_multiplicities_and_objects)
#     local Coproduct, L, P, lifted_pairs_of_multiplicities_and_objects;
#
#     S := ModelingCategory( SGReps );
#     L := UnderlyingCategory( S );;
#
#     lifted_pairs_of_multiplicities_and_objects :=
#         List( pairs_of_multiplicities_and_objects, pair ->
#             Npair( 2, pair[1], ObjectConstructor( L, pair[2] ) ) );
#
#     return ObjectConstructor( SGReps, ObjectConstructor( Coproduct, lifted_pairs_of_multiplicities_and_objects ) );
#
# end );

##
InstallMethod( SkeletalCategoryOfGroupRepresentations,
               [ IsGroup, IsFieldForHomalg ],
               
  FunctionWithNamedArguments(
  [
    [ "FinalizeCategory", true ],
  ],
  function( CAP_NAMED_ARGUMENTS, G, splitting_field )
    local character_table, irreducible_characters, nr_irreducible_characters, Rows, Coproduct, decompose_product_of_characters, object_datum_type, object_datum, object_constructor, morphism_datum_type, morphism_datum, morphism_constructor, modeling_tower_object_datum, modeling_tower_object_constructor, modeling_tower_morphism_datum, modeling_tower_morphism_constructor, name, SGReps;
    
    Assert( 0, HasCharacteristic( splitting_field ) and Characteristic( splitting_field ) = 0 );
    
    character_table := CharacterTable( G );
    
    irreducible_characters := Irr( character_table );
    
    nr_irreducible_characters := Length( irreducible_characters );
    
    Rows := CategoryOfRows( splitting_field );
    
    Coproduct :=
        CoproductOfCategoryOfRowsWithSparseDatastructure( Rows,
                                                          nr_irreducible_characters
                                                          : FinalizeCategory := false );
    
    ####################################
    # Monoidal structure
    ####################################
    
    AddTensorUnit( Coproduct,
      function( Coproduct )
        local unit_index, unit_character;
        
        unit_index := PositionProperty( irreducible_characters, IsOne );
        
        return ObjectConstructor( Coproduct, [ [ 1, unit_index ] ] );
        
    end );
    
    AddLeftUnitorWithGivenTensorProduct( Coproduct,
      function( Coproduct, object, tensor_product )
        
        return IdentityMorphism( Coproduct, object );
        
    end );
    
    AddRightUnitorWithGivenTensorProduct( Coproduct,
      function( Coproduct, object, tensor_product )
        
        return IdentityMorphism( Coproduct, object );
        
    end );
    
    # Returns a list containing the multiplicity of each irreducible character
    # occuring in the direct sum decomposion of the product.
    # The arguments are the indices of characters.
    # 
    # Example in S4: χ₂·χ₃ = χ₂⊕ χ₄,
    #                so this function returns [ [1, 2], [1, 4] ].
    decompose_product_of_characters :=
      function( character_1, character_2 )
        local chi_1, chi_2, product, decomposed_product;
        #% CAP_JIT_RESOLVE_FUNCTION
        
        # Get the actual characters.
        chi_1 := irreducible_characters[ character_1 ];
        chi_2 := irreducible_characters[ character_2 ];
        
        product := chi_1 * chi_2;
        
        decomposed_product :=
            CAP_INTERNAL_skeletal_group_reps_decompose_character( Rows, irreducible_characters, product );
        
        return decomposed_product;
        
    end;
    
    AddTensorProductOnObjects( Coproduct,
      function( Coproduct, object_1, object_2 )
        local pairs_1, pairs_2, product;
        
        pairs_1 := ListOfPairsOfObjectAndIndex( object_1 );
        pairs_2 := ListOfPairsOfObjectAndIndex( object_2 );
        
        # Example: (χ₁⊕ 2χ₄)·(χ₂⊕ 3χ₃)
        #        = [(χ₁·χ₂) ⊕  (χ₁·3χ₃)] ⊕  [(2χ₄·χ₂) ⊕  (2χ₄·3χ₃)]
        #        = [(χ₁·χ₂) ⊕  3(χ₁·χ₃)] ⊕  [2(χ₄·χ₂) ⊕  6(χ₄·χ₃)]
        #        = [ (χ₄)   ⊕    3(χ₃) ] ⊕  [2(χ₁⊕ χ₂⊕ χ₃⊕ χ₄) ⊕  6(χ₂⊕ χ₄)]
        #        = 2χ₁⊕ 8χ₂⊕ 5χ₃⊕ 9χ₄
        product :=
            DirectSum( Coproduct, List( pairs_1, pair_1 ->
                DirectSum( Coproduct, List( pairs_2, function( pair_2 )
                    local multiplicity_of_product, chi_1, chi_2, product, decomposed_product;
                    
                    chi_1 := irreducible_characters[ pair_1[2] ];
                    chi_2 := irreducible_characters[ pair_2[2] ];
                    
                    product := chi_1 * chi_2;
                    
                    decomposed_product :=
                        CAP_INTERNAL_skeletal_group_reps_decompose_character( Rows, irreducible_characters, product );
                    
                    multiplicity_of_product :=
                        TensorProductOnObjects( Rows, pair_1[1], pair_2[1] );
                    
                    decomposed_product :=
                        List( decomposed_product, pair ->
                            [ TensorProductOnObjects( Rows, pair[1], multiplicity_of_product ), pair[2] ] );
                    
                    return ObjectConstructor( Coproduct, decomposed_product );
                    
                end ) ) ) );
                
        return product;
        
    end );
    
    # The l'th component of ɑ⊗ ɣ is given by: (ɑ⊗ ɣ)ₗ := ⊕ ᵢ⊕ ⱼ (ɑᵢ⊗ ɣⱼ⊗ Iₙ₍ᵢⱼ₎ₗ)
    AddTensorProductOnMorphismsWithGivenTensorProducts( Coproduct,
      function( Coproduct, source, alpha, gamma, target )
        local pairs_alpha, pairs_gamma, nr_matrices_1, nr_matrices_2, size_1, size_2, tensor_products_of_matrices, i, j, support, size_support, sums_of_morphisms, chi, i_list, j_list, multiplicity, object, morphism_pairs;
        
        pairs_alpha := ListOfPairsOfMorphismAndIndex( alpha );
        pairs_gamma := ListOfPairsOfMorphismAndIndex( gamma );
        
        # TODO: Can we precompute the direct sum objects and use DirectSumFunctorialWithGivenDirectSums?
        #       Maybe instead of immediately calling DirectSumFunctorial, gather everything inside a big
        #       list and sum up afterwards?
        # 
        # TODO: Do this in a non-functional way or manually compile it?
        #
        #       1) Due to the ZeroMorpism( Rows, ... ) below we will
        #          eventually sum over many unnecessary zero morphism 0 -> 0
        #          and might even end up with zero morphisms in
        #          the final tensor product. We should not return
        #          0 -> 0 morphisms, but that would be non-functional?
        #
        #       2) If for a character index 'l', we know from
        #          'source' or 'target' that (ɑ⊗ ɣ)ₗ is a zero morphism,
        #          then the entire computation for the index 'l' can be skipped.
        
        sums_of_morphisms :=
            List( [ 1 .. nr_irreducible_characters ], l ->
                # If source[l] = 0 or range[l] = 0 return ZeroMorphism(...), else:
                DirectSumFunctorial( Rows, List( pairs_alpha, pair_alpha ->
                    DirectSumFunctorial( Rows, List( pairs_gamma, function( pair_gamma )
                        local chi_i, chi_j, chi_l, product, n_ijl, alpha_x_gamma, identity_morphism;
                        
                        chi_i := irreducible_characters[ pair_alpha[2] ];
                        chi_j := irreducible_characters[ pair_gamma[2] ];
                        chi_l := irreducible_characters[ l ];
                        
                        product := chi_i * chi_j;
                        
                        # Get the multiplicity of chi_l in the product.
                        n_ijl := ScalarProduct( chi_l, product );
                        
                        # If the multiplicity is 0, then Iₙ₍ᵢⱼ₎ₗ = 0 so (ɑᵢ⊗ ɣⱼ)⊗ Iₙ₍ᵢⱼ₎ₗ = 0.
                        if n_ijl = 0 then
                            
                            return ZeroMorphism( Rows, ZeroObject( Rows ), ZeroObject( Rows ) );
                        fi;
                        
                        # ɑᵢ⊗ ɣⱼ
                        alpha_x_gamma := TensorProductOnMorphisms( Rows, pair_alpha[1], pair_gamma[1] );
                        
                        # Iₙ₍ᵢⱼ₎ₗ
                        identity_morphism :=
                            IdentityMorphism( Rows, CategoryOfRowsObject( Rows, n_ijl ) );
                        
                        # (ɑᵢ⊗ ɣⱼ)⊗ Iₙ₍ᵢⱼ₎ₗ
                        return TensorProductOnMorphisms( Rows, alpha_x_gamma, identity_morphism );
                        
                    end ) ) ) ) );
                        
        morphism_pairs := List( [ 1 .. nr_irreducible_characters ], i -> [ sums_of_morphisms[i], i ] );
                    
        return MorphismConstructor( Coproduct, source, morphism_pairs, target );
        
    end );
    
    # ## -- Helper functions for distributivity --
    #
    # ##
    # right_distributivity_expanding_permutation := FunctionWithCache(
    #     function( object_b, list_of_objects, direct_sum, support_tensor_product, is_expanded )
    #       local permutation_list, k_permutation, size_support, size_list_of_objects, height, l, i, k, direct_sum_support,
    #             multiplicity_li, sum_up_to_l_minus_1, j, b_j_times_c_kij, cols, rows, height_of_zeros, object_b_list,
    #             multiplicity_directsum_i;
    #
    #       if not is_expanded then
    #
    #           list_of_objects := CAP_INTERNAL_ExpandSemisimpleCategoryObjectList( list_of_objects );
    #
    #       fi;
    #
    #       permutation_list := [ ];
    #
    #       size_list_of_objects := Size( list_of_objects );
    #
    #       object_b_list := SemisimpleCategoryObjectList( object_b );
    #
    #       direct_sum_support := Support( direct_sum );
    #
    #       for k in support_tensor_product do
    #
    #           k_permutation := [ ];
    #
    #           for l in [ 1 .. size_list_of_objects ] do
    #
    #               height := 0;
    #
    #               for i in direct_sum_support do
    #
    #                   multiplicity_li := Multiplicity( list_of_objects[l], i );
    #
    #                   sum_up_to_l_minus_1 :=
    #                     Sum( List( [ 1 .. l - 1 ], m -> Multiplicity( list_of_objects[m], i ) ) );
    #
    #                   multiplicity_directsum_i := Multiplicity( direct_sum, i );
    #
    #                   for j in object_b_list do
    #
    #                       b_j_times_c_kij := j[1] * Multiplicity( k, i, j[2] );
    #
    #                       cols := multiplicity_li * b_j_times_c_kij;
    #
    #                       rows :=  multiplicity_directsum_i * b_j_times_c_kij;
    #
    #                       height_of_zeros := sum_up_to_l_minus_1 * b_j_times_c_kij;
    #
    #                       Append( k_permutation,
    #                         List( [ 1 .. cols ], m -> height + height_of_zeros + m ) );
    #
    #                       height := height + rows;
    #
    #                   od;
    #
    #               od;
    #
    #           od;
    #
    #           Add( permutation_list, [ k_permutation, k ] );
    #
    #       od;
    #
    #       return permutation_list;
    #
    #     end
    # );
    # ##
    # left_distributivity_expanding_permutation := FunctionWithCache(
    #     function( object_b, list_of_objects, direct_sum, support_tensor_product, is_expanded )
    #       local permutation_list, k_permutation, size_list_of_objects, height, l, i, k, direct_sum_support,
    #             j, l_times_j, c_kij, list_of_objects_j, rows, zeros_above, ones, step, object_b_list;
    #
    #       if not is_expanded then
    #
    #           list_of_objects := CAP_INTERNAL_ExpandSemisimpleCategoryObjectList( list_of_objects );
    #
    #       fi;
    #
    #       permutation_list := [ ];
    #
    #       size_list_of_objects := Size( list_of_objects );
    #
    #       object_b_list := SemisimpleCategoryObjectList( object_b );
    #
    #       direct_sum_support := Support( direct_sum );
    #
    #       for k in support_tensor_product do
    #
    #           k_permutation := [ ];
    #
    #           for l in [ 1 .. size_list_of_objects ] do
    #
    #               height := 0;
    #
    #               for i in object_b_list do
    #
    #                   for j in direct_sum_support do
    #
    #                       l_times_j := Multiplicity( list_of_objects[l], j );
    #
    #                       c_kij := Multiplicity( k, i[2], j );
    #
    #                       list_of_objects_j := Multiplicity( direct_sum, j );
    #
    #                       rows := i[1] * list_of_objects_j * c_kij;
    #
    #                       zeros_above := Sum( List( [ 1 .. l - 1 ], m -> Multiplicity( list_of_objects[m], j ) ) ) * c_kij;
    #
    #                       ones := l_times_j * c_kij;
    #
    #                       step := list_of_objects_j * c_kij;
    #
    #                       Append( k_permutation, Flat(
    #                         List( [ 1 .. i[1] ], m -> List( [ 1 .. ones ], n -> height + (m-1)*step + zeros_above + n ) )
    #                       ) );
    #
    #                       height := height + rows;
    #
    #                   od;
    #
    #               od;
    #
    #           od;
    #
    #           Add( permutation_list, [ k_permutation, k ] );
    #
    #       od;
    #
    #       return permutation_list;
    #
    #     end
    # );
    # ##
    # distributivity_function := function( new_source, object_b, list_of_objects, new_range, permutation_function, invert )
    #   local support, support_tensor_product, size_support, direct_sum, morphism_list, k, permutation,
    #         object, dim, homalg_matrix, permutation_list, entry;
    #
    #     support_tensor_product := Support( new_source );
    #
    #     direct_sum := DirectSum( list_of_objects );
    #
    #     permutation_list := permutation_function( object_b, list_of_objects, direct_sum, support_tensor_product, true );
    #
    #     if invert then
    #
    #         permutation_list := 
    #           List( permutation_list, entry ->
    #             [ ListPerm( PermList( entry[1] )^(-1), Size( entry[1] ) ), entry[2] ] );
    #
    #     fi;
    #
    #     morphism_list := [ ];
    #
    #     for entry in permutation_list do
    #
    #         object := Component( new_source, entry[2] );
    #
    #         dim := Dimension( object );
    #
    #         homalg_matrix := CertainRows(
    #           HomalgIdentityMatrix( dim, field ),
    #           entry[1] );
    #
    #         Add( morphism_list, [ VectorSpaceMorphism( object, homalg_matrix, object ), entry[2] ] );
    #
    #     od;
    #
    #     return SemisimpleCategoryMorphism( new_source, morphism_list, new_range );
    #
    # end;
    #
    # ##
    # AddRightDistributivityExpandingWithGivenObjects( Coproduct,
    #   function( Coproduct, new_source, list_of_objects, object_b, new_range )
    #
    #       return distributivity_function(
    #                new_source, object_b, list_of_objects, new_range, right_distributivity_expanding_permutation, true );
    #
    # end );
    #
    #
    # ##
    # AddRightDistributivityFactoringWithGivenObjects( Coproduct,
    #   function( Coproduct, new_source, list_of_objects, object_b, new_range )
    #
    #       return distributivity_function(
    #                new_source, object_b, list_of_objects, new_range, right_distributivity_expanding_permutation, false );
    #
    # end );
    #
    # ##
    # AddLeftDistributivityExpandingWithGivenObjects( Coproduct,
    #   function( Coproduct, new_source, object_b, list_of_objects, new_range )
    #
    #       return distributivity_function(
    #                new_source, object_b, list_of_objects, new_range, left_distributivity_expanding_permutation, true );
    #
    # end );
    #
    # ##
    # AddLeftDistributivityFactoringWithGivenObjects( Coproduct,
    #   function( Coproduct, new_source, object_b, list_of_objects, new_range )
    #
    #       return distributivity_function(
    #                new_source, object_b, list_of_objects, new_range, left_distributivity_expanding_permutation, false );
    #
    # end );
    #
    # ## -- Helper functions for the associator --
    #
    # if associator_available then
    #
    # ## computes the associator (left to right) of (c,a,b) via the coherence axiom involving the braiding
    # InstallMethodWithCacheFromObject( CAP_INTERNAL_AssociatorFromCoherenceAxiomLeft,
    #   [ ObjectFilter( category ) and IsSemisimpleCategoryObject,
    #     ObjectFilter( category ) and IsSemisimpleCategoryObject,
    #     ObjectFilter( category ) and IsSemisimpleCategoryObject,
    #     MorphismFilter( category ) and IsSemisimpleCategoryMorphism,
    #     MorphismFilter( category ) and IsSemisimpleCategoryMorphism ],
    #
    #     function( object_a, object_b, object_c, associator_left_to_right_acb, associator_right_to_left_abc )
    #
    #       return PreCompose( [
    #         TensorProductOnMorphisms( Braiding( object_c, object_a ), IdentityMorphism( object_b ) ),
    #         associator_left_to_right_acb,
    #         TensorProductOnMorphisms( IdentityMorphism( object_a ), Braiding( object_c, object_b ) ),
    #         associator_right_to_left_abc,
    #         Braiding( TensorProductOnObjects( object_a, object_b ), object_c ) ] );
    #
    # end );
    #
    # ## computes the associator (left to right )of (b,c,a) via the coherence axiom involving the braiding
    # InstallMethodWithCacheFromObject( CAP_INTERNAL_AssociatorFromCoherenceAxiomRight,
    #   [ ObjectFilter( category ) and IsSemisimpleCategoryObject,
    #     ObjectFilter( category ) and IsSemisimpleCategoryObject,
    #     ObjectFilter( category ) and IsSemisimpleCategoryObject,
    #     MorphismFilter( category ) and IsSemisimpleCategoryMorphism,
    #     MorphismFilter( category ) and IsSemisimpleCategoryMorphism ],
    #
    #     function( object_a, object_b, object_c, associator_right_to_left_abc, associator_left_to_right_bac )
    #
    #       return PreCompose( [
    #         Braiding( TensorProductOnObjects( object_b, object_c ), object_a ),
    #         associator_right_to_left_abc,
    #         TensorProductOnMorphisms( Braiding( object_a, object_b ), IdentityMorphism( object_c ) ),
    #         associator_left_to_right_bac,
    #         TensorProductOnMorphisms( IdentityMorphism( object_b ), Braiding( object_a, object_c ) ) ] );
    #
    # end );
    #
    #
    # ## the input are objects whose underlying list is of the form [ 1, irr ].
    # associator_on_irreducibles := function( object_1, object_2, object_3 )
    #   local irr_1, irr_2, irr_3, data, morphism_list, object, pos_1, 
    #         pos_2, pos_3, size, homalg_matrix, source, range, i, string,
    #         irr_1_nr, irr_2_nr, irr_3_nr, result_morphism,
    #         associator_left_to_right, associator_right_to_left, intermediate_associator;
    #
    #   irr_1 := SemisimpleCategoryObjectList( object_1 )[1][2];
    #
    #   irr_2 := SemisimpleCategoryObjectList( object_2 )[1][2];
    #
    #   irr_3 := SemisimpleCategoryObjectList( object_3 )[1][2];
    #
    #   object := TensorProductOnObjects( TensorProductOnObjects( object_1, object_2 ), object_3 );
    #
    #   ## handle the cases where one of the inputs is the unit
    #   if IsYieldingIdentities( irr_1 ) or IsYieldingIdentities( irr_2 ) or IsYieldingIdentities( irr_3 ) then
    #
    #       return IdentityMorphism( object );
    #
    #   fi;
    #
    #   if is_complete_data then
    #
    #       morphism_list := AssociatorFromData( irr_1, irr_2, irr_3, associator_data, underlying_category, SemisimpleCategoryObjectList( object ) );
    #
    #       result_morphism := SemisimpleCategoryMorphism( object, morphism_list, object );
    #
    #   else
    #
    #       # A <= B <= C
    #
    #       irr_1_nr := irr_1!.UnderlyingCharacterNumber;
    #
    #       irr_2_nr := irr_2!.UnderlyingCharacterNumber;
    #
    #       irr_3_nr := irr_3!.UnderlyingCharacterNumber;
    #
    #       if Size( Set( [ irr_1_nr, irr_2_nr, irr_3_nr ] ) ) = 2 then
    #
    #           if ( irr_1_nr <= irr_2_nr and irr_2_nr <= irr_3_nr ) then
    #               #(AAB), (ABB): can be loaded directly
    #
    #               morphism_list := AssociatorFromData( irr_1, irr_2, irr_3, associator_data, underlying_category, SemisimpleCategoryObjectList( object ) );
    #
    #               result_morphism := SemisimpleCategoryMorphism( object, morphism_list, object );
    #
    #           elif ( irr_1_nr < irr_2_nr ) then
    #               #(ABA)
    #
    #               associator_left_to_right := AssociatorLeftToRight( object_3, object_1, object_2 );
    #
    #               associator_right_to_left := AssociatorRightToLeft( object_1, object_3, object_2 );
    #
    #               result_morphism := CAP_INTERNAL_AssociatorFromCoherenceAxiomRight(
    #                 object_1, object_3, object_2, associator_right_to_left, associator_left_to_right );
    #
    #           elif ( irr_1_nr = irr_3_nr) then
    #               #(BAB)
    #
    #               associator_right_to_left := AssociatorRightToLeft( object_2, object_1, object_3 );
    #
    #               associator_left_to_right := AssociatorLeftToRight( object_2, object_3, object_1 );
    #
    #               result_morphism := CAP_INTERNAL_AssociatorFromCoherenceAxiomLeft(
    #                 object_2, object_1, object_3, associator_left_to_right, associator_right_to_left );
    #
    #           elif (irr_2_nr = irr_3_nr ) then
    #               #(BAA)
    #
    #               associator_right_to_left := AssociatorRightToLeft( object_2, object_3, object_1 );
    #
    #               associator_left_to_right := AssociatorLeftToRight( object_3, object_2, object_1 );
    #
    #               intermediate_associator := CAP_INTERNAL_AssociatorFromCoherenceAxiomRight(
    #                 object_2, object_3, object_1, associator_right_to_left, associator_left_to_right );
    #
    #               associator_right_to_left := AssociatorRightToLeft( object_2, object_3, object_1 );
    #
    #               result_morphism := CAP_INTERNAL_AssociatorFromCoherenceAxiomLeft(
    #                 object_2, object_3, object_1, intermediate_associator, associator_right_to_left );
    #
    #           else
    #               #(BBA)
    #
    #               associator_left_to_right := AssociatorLeftToRight( object_3, object_2, object_1 );
    #
    #               associator_right_to_left := AssociatorRightToLeft( object_3, object_1, object_2 );
    #
    #               intermediate_associator := CAP_INTERNAL_AssociatorFromCoherenceAxiomLeft(
    #                 object_3, object_1, object_2, associator_left_to_right, associator_right_to_left );
    #
    #               associator_right_to_left := AssociatorRightToLeft( object_3, object_1, object_2 );
    #
    #               result_morphism := CAP_INTERNAL_AssociatorFromCoherenceAxiomRight(
    #                 object_3, object_1, object_2, associator_right_to_left, intermediate_associator );
    #
    #           fi;
    #
    #       else
    #
    #           if ( irr_1_nr <= irr_2_nr ) and ( irr_1_nr <= irr_3_nr ) then
    #               #(ABC), (ACB): can be loaded directly
    #
    #               morphism_list := AssociatorFromData( irr_1, irr_2, irr_3, associator_data, underlying_category, SemisimpleCategoryObjectList( object ) );
    #
    #               result_morphism := SemisimpleCategoryMorphism( object, morphism_list, object );
    #
    #           elif (irr_1_nr <= irr_3_nr ) then
    #               #(CAB), (BAC): usage of 1 helper function
    #
    #               associator_left_to_right := AssociatorLeftToRight( object_2, object_1, object_3 );
    #
    #               associator_right_to_left := AssociatorRightToLeft( object_2, object_3, object_1 );
    #
    #               result_morphism :=
    #                 CAP_INTERNAL_AssociatorFromCoherenceAxiomLeft(
    #                   object_2, object_3, object_1, associator_left_to_right, associator_right_to_left );
    #
    #           else
    #               #(BCA), (CBA): usage of 2 helper functions
    #
    #               associator_left_to_right :=
    #                 AssociatorLeftToRight( object_3, object_1, object_2 );
    #
    #               associator_right_to_left :=
    #                 AssociatorRightToLeft( object_3, object_2, object_1 );
    #
    #               intermediate_associator :=
    #                 CAP_INTERNAL_AssociatorFromCoherenceAxiomLeft( 
    #                   object_3, object_2, object_1, associator_left_to_right, associator_right_to_left );
    #
    #               associator_right_to_left :=
    #                 AssociatorRightToLeft( object_3, object_1, object_2 );
    #
    #               result_morphism :=
    #                 CAP_INTERNAL_AssociatorFromCoherenceAxiomRight( 
    #                   object_3, object_1, object_2, associator_right_to_left, intermediate_associator );
    #
    #           fi;
    #
    #       fi;
    #
    #   fi;
    #
    #   return result_morphism;
    #
    # end;
    #
    # InstallMethodWithCacheFromObject( CAP_INTERNAL_AssociatorOnIrreducibles,
    #   [ ObjectFilter( category ) and IsSemisimpleCategoryObject,
    #     ObjectFilter( category ) and IsSemisimpleCategoryObject,
    #     ObjectFilter( category ) and IsSemisimpleCategoryObject ],
    #
    #     associator_on_irreducibles );
    #
    # fi; ## associator_available
    #
    # ##
    # distributivity_expanding_for_triple := FunctionWithCache(
    #     function( object_1, object_2, direct_sum, object_list_with_actual_objects, left_term )
    #       local object, support_tensor_product_all, direct_sum_2, support_tensor_product_partial,
    #             tensored_object_list_with_actual_objects, permutation_list_1, permutation_list_2, morphism_list, size, i,
    #             dim, string, vector_space_object;
    #
    #       direct_sum_2 := TensorProductOnObjects( direct_sum, object_1 );
    #
    #       object := TensorProductOnObjects( direct_sum_2, object_2 );
    #
    #       support_tensor_product_all := Support( object );
    #
    #       support_tensor_product_partial := Support( direct_sum_2 );
    #
    #       tensored_object_list_with_actual_objects := 
    #         List( object_list_with_actual_objects, pair -> [ pair[1], TensorProductOnObjects( pair[2], object_1 ) ] );
    #
    #       if left_term then
    #
    #           permutation_list_1 :=
    #             right_distributivity_expanding_permutation( 
    #               object_1, object_list_with_actual_objects, direct_sum, support_tensor_product_partial, false );
    #
    #           permutation_list_1 :=
    #             CAP_INTERNAL_TensorProductOfPermutationListWithObjectFromRight( permutation_list_1, object_2, support_tensor_product_all );
    #
    #       else
    #
    #           permutation_list_1 :=
    #             left_distributivity_expanding_permutation( 
    #               object_1, object_list_with_actual_objects, direct_sum, support_tensor_product_partial, false );
    #
    #           permutation_list_1 :=
    #             CAP_INTERNAL_TensorProductOfPermutationListWithObjectFromRight( permutation_list_1, object_2, support_tensor_product_all );
    #
    #       fi;
    #
    #       permutation_list_2 :=
    #         right_distributivity_expanding_permutation(
    #           object_2, tensored_object_list_with_actual_objects, direct_sum_2, support_tensor_product_all, false );
    #
    #       morphism_list := [ ];
    #
    #       ## CLAIM: permutation_lists are sorted w.r.t. ordering in second component
    #       size := Size( permutation_list_1 );
    #
    #       for i in [ 1 .. size ] do
    #
    #           Add( morphism_list,
    #                [ ListPerm( ( PermList( permutation_list_1[i][1] )^(-1) * PermList( permutation_list_2[i][1] )^(-1) )^(-1),
    #                  Size( permutation_list_1[i][1] ) ),
    #                  permutation_list_1[i][2] ] 
    #           );
    #
    #       od;
    #
    #       return morphism_list;
    #
    #     end
    # );
    # ##
    # distributivity_factoring_for_triple := FunctionWithCache(
    #     function( object_1, object_2, direct_sum, object_list_with_actual_objects, right_term )
    #       local object, support_tensor_product_all, direct_sum_2, support_tensor_product_partial,
    #             tensored_object_list_with_actual_objects, permutation_list_1, permutation_list_2, morphism_list, size, i,
    #             dim, string, vector_space_object;
    #
    #       direct_sum_2 := TensorProductOnObjects( direct_sum, object_2 );
    #
    #       object := TensorProductOnObjects( direct_sum_2, object_1 );
    #
    #       support_tensor_product_all := Support( object );
    #
    #       support_tensor_product_partial := Support( direct_sum_2 );
    #
    #       tensored_object_list_with_actual_objects := 
    #         List( object_list_with_actual_objects, pair -> [ pair[1], TensorProductOnObjects( pair[2], object_2 ) ] );
    #
    #       if right_term then
    #
    #           permutation_list_1 :=
    #             left_distributivity_expanding_permutation( 
    #               object_2, object_list_with_actual_objects, direct_sum, support_tensor_product_partial, false );
    #
    #           permutation_list_1 :=
    #             CAP_INTERNAL_TensorProductOfPermutationListWithObjectFromLeft( permutation_list_1, object_1, support_tensor_product_all );
    #
    #       else
    #
    #           permutation_list_1 :=
    #             right_distributivity_expanding_permutation( 
    #               object_2, object_list_with_actual_objects, direct_sum, support_tensor_product_partial, false );
    #
    #           permutation_list_1 :=
    #             CAP_INTERNAL_TensorProductOfPermutationListWithObjectFromLeft( permutation_list_1, object_1, support_tensor_product_all );
    #
    #       fi;
    #
    #       permutation_list_2 :=
    #         right_distributivity_expanding_permutation(
    #           object_1, tensored_object_list_with_actual_objects, direct_sum_2, support_tensor_product_all, false );
    #
    #       morphism_list := [ ];
    #
    #       ## CLAIM: permutation_lists are sorted w.r.t. ordering in second component
    #       size := Size( permutation_list_1 );
    #
    #       for i in [ 1 .. size ] do
    #
    #           Add( morphism_list,
    #                [ ListPerm( ( PermList( permutation_list_2[i][1] ) * PermList( permutation_list_1[i][1] ) )^(-1), 
    #                  Size( permutation_list_2[i][1] ) ),
    #                  permutation_list_1[i][2] ]
    #           );
    #
    #       od;
    #
    #       return morphism_list;
    #
    #     end
    # );
    #
    # if associator_available then
    #
    # ##
    # AddAssociatorLeftToRightWithGivenTensorProducts( Coproduct,
    #   function( Coproduct, new_source, object_a, object_b, object_c, new_range )
    #     local object_a_list, object_b_list, object_c_list, result_morphism,
    #           object_a_expanded_list, object_b_expanded_list, object_c_expanded_list,
    #           elem, morphism, summand_list, inner_summand_list, outer_summand_list, innermost_summand_list,
    #           elem_a, elem_b, elem_c,
    #           morphism_1, morphism_2, morphism_3, morphism_4, morphism_5, morphism_6, morphism_7_inverse,
    #           tensor_product, first_permutation, first_permutation_morphism_list,
    #           second_permutation, second_permutation_morphism_list, chi,
    #           perm1, perm2, perm3, dim, vector_space_object, homalg_matrix, support,
    #           tensor_product_list, nr_components, morphism_4_string_list, morphism_4_position_list, i,
    #           associator_string, add_string, multiplicity,
    #           a_list, b_list, c_list, size_a, size_b, size_c, beta, gamma, a, b, c,
    #           start_pos, g, G, p,
    #           tensor_product_triple_list, matrix, associator_matrix,
    #           morphism_4_degree_list, degree;
    #
    #     object_a_list := SemisimpleCategoryObjectListWithActualObjects( object_a );
    #
    #     object_b_list := SemisimpleCategoryObjectListWithActualObjects( object_b );
    #
    #     object_c_list := SemisimpleCategoryObjectListWithActualObjects( object_c );
    #
    #     if IsEmpty( object_a_list ) or IsEmpty( object_b_list ) or IsEmpty( object_c_list ) then
    #
    #         return ZeroMorphism( new_source, new_range );
    #
    #     fi;
    #
    #     object_a_expanded_list := (Size( object_a_list ) > 1) or (object_a_list[1][1] > 1);
    #
    #     object_b_expanded_list := (Size( object_b_list ) > 1) or (object_b_list[1][1] > 1);
    #
    #     object_c_expanded_list := (Size( object_c_list ) > 1) or (object_c_list[1][1] > 1);
    #
    #     result_morphism := IdentityMorphism( new_source );
    #
    #     support := Support( new_source );
    #
    #     ## morphism_1
    #
    #     morphism_1 := [ ];
    #
    #     if object_a_expanded_list then
    #
    #         morphism_1 := distributivity_expanding_for_triple( object_b, object_c, object_a, object_a_list, true );
    #
    #     fi;
    #
    #     ## morphism_2
    #
    #     morphism_2 := [ ];
    #
    #     if object_b_expanded_list then
    #
    #         summand_list := [ ];
    #
    #         for elem in object_a_list do
    #
    #             morphism := distributivity_expanding_for_triple( elem[2], object_c, object_b, object_b_list, false );
    #
    #             Append( summand_list, List( [ 1 .. elem[1] ], i -> morphism ) );
    #
    #         od;
    #
    #         morphism_2 := CAP_INTERNAL_DirectSumForPermutationLists( summand_list, support );
    #
    #     fi;
    #
    #     ## morphism_3
    #
    #     morphism_3 := [ ];
    #
    #     if object_c_expanded_list then
    #
    #         outer_summand_list := [ ];
    #
    #         for elem_a in object_a_list do
    #
    #             inner_summand_list := [ ];
    #
    #             for elem_b in object_b_list do
    #
    #                 tensor_product := TensorProductOnObjects( elem_a[2], elem_b[2] );
    #
    #                 morphism :=
    #                   left_distributivity_expanding_permutation
    #                     ( tensor_product, object_c_list,
    #                       object_c, Support( TensorProductOnObjects( tensor_product, object_c ) ), false );
    #
    #                 Append( inner_summand_list, List( [ 1 .. elem_b[1] ], i -> morphism ) );
    #
    #             od;
    #
    #             morphism :=
    #               CAP_INTERNAL_DirectSumForPermutationLists(
    #                 inner_summand_list, Support( TensorProductOnObjects( TensorProductOnObjects( elem_a[2], object_b ), object_c ) )
    #               );
    #
    #             Append( outer_summand_list, List( [ 1 .. elem_a[1] ], i -> morphism ) );
    #
    #         od;
    #
    #         morphism_3 := CAP_INTERNAL_DirectSumForPermutationLists( outer_summand_list, support );
    #
    #     fi;
    #
    #     ## morphism_4
    #
    #     if is_magma_ring and is_complete_data then
    #
    #         tensor_product_list := SemisimpleCategoryObjectList( new_source );
    #
    #         nr_components := Size( tensor_product_list );
    #
    #         morphism_4_string_list := List( [ 1 .. nr_components ], i -> "[" );
    #
    #         a_list := SemisimpleCategoryObjectList( object_a );
    #
    #         b_list := SemisimpleCategoryObjectList( object_b );
    #
    #         c_list := SemisimpleCategoryObjectList( object_c );
    #
    #         size_a := Size( a_list );
    #
    #         size_b := Size( b_list );
    #
    #         size_c := Size( c_list );
    #
    #         ## precomputation
    #         beta := 
    #           List( tensor_product_list, d ->
    #             List( a_list, a -> 
    #               List( b_list, b ->
    #                 Sum( List( c_list, c -> c[1] * SignInt( Multiplicity( d[2], a[2], b[2], c[2] ) ) ) )
    #                )
    #             )
    #           );
    #
    #         gamma := 
    #           List( [ 1 .. nr_components ], d ->
    #             List( [ 1 .. size_a ], a ->
    #               Sum( List( [ 1 .. size_b ], b -> b_list[b][1] * beta[d][a][b] ) )
    #             )
    #           );
    #
    #         morphism_4 := List( [ 1 .. nr_components ], i ->[] );
    #
    #         morphism_4_degree_list := List( [ 1 .. nr_components ], i ->[] );
    #
    #         for a in [ 1 .. size_a ] do
    #
    #             for b in [ 1 .. size_b ] do
    #
    #                 for c in [ 1 .. size_c ] do
    #
    #                     if IsYieldingIdentities( a_list[a][2] ) or IsYieldingIdentities( b_list[b][2] ) or IsYieldingIdentities( c_list[c][2] ) then
    #
    #                         tensor_product_triple_list := 
    #                           TensorProductOfIrreduciblesOp( [ a_list[a][2], b_list[b][2], c_list[c][2] ], a_list[a][2] );
    #
    #                         for elem in tensor_product_triple_list do
    #
    #                             i := PositionProperty( tensor_product_list, j -> j[2] = elem[2] );
    #
    #                             multiplicity := elem[1];
    #
    #                             #Compute morphism_4_position_list
    #
    #                             #1.step: find start position
    #
    #                             start_pos := 
    #                               Sum( List( [ 1 .. a-1 ], al -> a_list[al][1] * gamma[i][al] ) )
    #                               + Sum( List( [ 1 .. b-1 ], bl -> b_list[bl][1] * beta[i][a][bl] ) )
    #                               + Sum( List( [ 1 .. c-1 ], cl -> c_list[cl][1] * SignInt( Multiplicity( tensor_product_list[i][2], a_list[a][2], b_list[b][2], c_list[cl][2] ) ) ) )
    #                               + 1;
    #
    #                             #2.step fill in the other positions
    #
    #                             g := beta[i][a][b];
    #
    #                             G := gamma[i][a];
    #
    #                             morphism_4_position_list :=
    #                               Flat(
    #                                 List( [ 0 .. a_list[a][1]-1 ], al ->
    #                                   List( [ 0 .. b_list[b][1]-1 ], bl ->
    #                                     List( [ 0 .. c_list[c][1]-1 ], cl ->
    #                                     start_pos + cl + al*G + bl*g
    #                                   )
    #                                   )
    #                                 )
    #                               );
    #
    #                             matrix := String( Flat( IdentityMat( multiplicity ) ) );
    #
    #                             for p in morphism_4_position_list do
    #
    #                                 morphism_4[i][p] := matrix;
    #
    #                                 morphism_4_degree_list[i][p] := multiplicity;
    #
    #                             od;
    #
    #                         od;
    #
    #                     else
    #
    #                         for i in [ 1 .. nr_components ] do
    #
    #                             associator_string :=
    #                               AssociatorStringListFromData( a_list[a][2], b_list[b][2], c_list[c][2], support[i], associator_data );
    #
    #                             if not IsEmpty( associator_string ) then
    #
    #                                 #Compute morphism_4_position_list
    #
    #                                 #1.step: find start position
    #
    #                                 start_pos := 
    #                                   Sum( List( [ 1 .. a-1 ], al -> a_list[al][1] * gamma[i][al] ) )
    #                                   + Sum( List( [ 1 .. b-1 ], bl -> b_list[bl][1] * beta[i][a][bl] ) )
    #                                   + Sum( List( [ 1 .. c-1 ], cl -> c_list[cl][1] * SignInt( Multiplicity( tensor_product_list[i][2], a_list[a][2], b_list[b][2], c_list[cl][2] ) ) ) )
    #                                   + 1;
    #
    #                                 #2.step fill in the other positions
    #
    #                                 g := beta[i][a][b];
    #
    #                                 G := gamma[i][a];
    #
    #                                 morphism_4_position_list :=
    #                                   Flat(
    #                                     List( [ 0 .. a_list[a][1]-1 ], al ->
    #                                       List( [ 0 .. b_list[b][1]-1 ], bl ->
    #                                         List( [ 0 .. c_list[c][1]-1 ], cl ->
    #                                         start_pos + cl + al*G + bl*g
    #                                       )
    #                                       )
    #                                     )
    #                                   );
    #
    #                                 degree := Sqrt( Size( SplitString( associator_string, "," ) ) );
    #
    #                                 associator_string := Concatenation( "[", associator_string, "]" );
    #
    #                                 for p in morphism_4_position_list do
    #
    #                                     morphism_4[i][p] := associator_string;
    #
    #                                     morphism_4_degree_list[i][p] := degree;
    #
    #                                 od;
    #
    #                             fi;
    #
    #                         od;
    #
    #                     fi;
    #
    #                 od;
    #
    #             od;
    #
    #         od; 
    #
    #         morphism_4 := 
    #           CAP_INTERNAL_Create_Semisimple_Endomorphism_From_String_List( new_source, morphism_4, morphism_4_degree_list );
    #
    #     else
    #
    #         outer_summand_list := [ ];
    #
    #         for elem_a in object_a_list do
    #
    #             inner_summand_list := [ ];
    #
    #             for elem_b in object_b_list do
    #
    #                 innermost_summand_list := [ ];
    #
    #                 for elem_c in object_c_list do
    #
    #                     morphism := CAP_INTERNAL_AssociatorOnIrreducibles( elem_a[2], elem_b[2], elem_c[2] );
    #
    #                     Append( innermost_summand_list, List( [ 1 .. elem_c[1] ], i -> morphism ) );
    #
    #                 od;
    #
    #                 morphism := DirectSumFunctorial( innermost_summand_list );
    #
    #                 Append( inner_summand_list, List( [ 1 .. elem_b[1] ], i -> morphism ) );
    #
    #             od;
    #
    #             morphism := DirectSumFunctorial( inner_summand_list );
    #
    #             Append( outer_summand_list, List( [ 1 .. elem_a[1] ], i -> morphism ) );
    #
    #         od;
    #
    #         morphism_4 := DirectSumFunctorial( outer_summand_list );
    #
    #     fi;
    #
    #     ## morphism_5
    #
    #     morphism_5 := [ ];
    #
    #     if object_c_expanded_list then
    #
    #         outer_summand_list := [ ];
    #
    #         for elem_a in object_a_list do
    #
    #             inner_summand_list := [ ];
    #
    #             for elem_b in object_b_list do
    #
    #                 morphism :=
    #                   distributivity_factoring_for_triple( elem_a[2], elem_b[2], object_c, object_c_list, true );
    #
    #                 Append( inner_summand_list, List( [ 1 .. elem_b[1] ], i -> morphism ) );
    #
    #             od;
    #
    #             morphism := CAP_INTERNAL_DirectSumForPermutationLists( inner_summand_list,
    #                           Support( TensorProductOnObjects( TensorProductOnObjects( elem_a[2], object_b ), object_c ) ) );
    #
    #             Append( outer_summand_list, List( [ 1 .. elem_a[1] ], i -> morphism ) );
    #
    #         od;
    #
    #         morphism_5 := CAP_INTERNAL_DirectSumForPermutationLists( outer_summand_list, support );
    #
    #     fi;
    #
    #     ## morphism_6
    #
    #     morphism_6 := [ ];
    #
    #     if object_b_expanded_list then
    #
    #         summand_list := [ ];
    #
    #         for elem in object_a_list do
    #
    #             morphism := distributivity_factoring_for_triple( elem[2], object_c, object_b, object_b_list, false );
    #
    #             Append( summand_list, List( [ 1 .. elem[1] ], i -> morphism ) );
    #
    #         od;
    #
    #         morphism_6 := CAP_INTERNAL_DirectSumForPermutationLists( summand_list, support );
    #
    #     fi;
    #
    #     ## morphism_7_inverse
    #
    #     morphism_7_inverse := [ ];
    #
    #     if object_a_expanded_list then
    #
    #         tensor_product := TensorProductOnObjects( object_b, object_c );
    #
    #         morphism_7_inverse := 
    #           right_distributivity_expanding_permutation
    #                       ( tensor_product, object_a_list,
    #                         object_a, support, false );
    #
    #     fi;
    #
    #     first_permutation_morphism_list := [ ];
    #
    #     first_permutation := IdentityMorphism( new_source );
    #
    #     if not ( IsEmpty( morphism_1 ) and IsEmpty( morphism_2 ) and IsEmpty( morphism_3 ) ) then
    #
    #         for chi in support do
    #
    #             perm1 := First( morphism_1, i -> i[2] = chi );
    #
    #             if not perm1 = fail then
    #
    #                 perm1 := PermList( perm1[1] )^(-1);
    #
    #             else
    #
    #                 perm1 := ();
    #
    #             fi;
    #
    #             perm2 := First( morphism_2, i -> i[2] = chi );
    #
    #             if not perm2 = fail then
    #
    #                 perm2 := PermList( perm2[1] )^(-1);
    #
    #             else
    #
    #                 perm2 := ();
    #
    #             fi;
    #
    #             perm3 := First( morphism_3, i -> i[2] = chi );
    #
    #             if not perm3 = fail then
    #
    #                 perm3 := PermList( perm3[1] )^(-1);
    #
    #             else
    #
    #                 perm3 := ();
    #
    #             fi;
    #
    #             dim := Multiplicity( new_source, chi );
    #
    #             vector_space_object := MatrixCategoryObject( underlying_category, dim );
    #
    #             homalg_matrix := CertainRows(
    #               HomalgIdentityMatrix( dim, field ),
    #               ListPerm( perm1 * perm2 * perm3, dim )
    #             );
    #
    #             Add( first_permutation_morphism_list, [ VectorSpaceMorphism( vector_space_object, homalg_matrix, vector_space_object ),
    #                  chi ] );
    #
    #         od;
    #
    #         first_permutation := SemisimpleCategoryMorphism( new_source, first_permutation_morphism_list, new_range );
    #
    #     fi;
    #
    #     second_permutation_morphism_list := [ ];
    #
    #     second_permutation := IdentityMorphism( new_source );
    #
    #     if not ( IsEmpty( morphism_5 ) and IsEmpty( morphism_6 ) and IsEmpty( morphism_7_inverse ) ) then
    #
    #         for chi in support do
    #
    #             perm1 := First( morphism_5, i -> i[2] = chi );
    #
    #             if not perm1 = fail then
    #
    #                 perm1 := PermList( perm1[1] )^(-1);
    #
    #             else
    #
    #                 perm1 := ();
    #
    #             fi;
    #
    #             perm2 := First( morphism_6, i -> i[2] = chi );
    #
    #             if not perm2 = fail then
    #
    #                 perm2 := PermList( perm2[1] )^(-1);
    #
    #             else
    #
    #                 perm2 := ();
    #
    #             fi;
    #
    #             perm3 := First( morphism_7_inverse, i -> i[2] = chi );
    #
    #             if not perm3 = fail then
    #
    #                 perm3 := PermList( perm3[1] ); ## the inverse!
    #
    #             else
    #
    #                 perm3 := ();
    #
    #             fi;
    #
    #             dim := Multiplicity( new_source, chi );
    #
    #             vector_space_object := MatrixCategoryObject( underlying_category, dim );
    #
    #             homalg_matrix := CertainRows(
    #               HomalgIdentityMatrix( dim, field ),
    #               ListPerm( perm1 * perm2 * perm3, dim )
    #             );
    #
    #             Add( second_permutation_morphism_list, [ VectorSpaceMorphism( vector_space_object, homalg_matrix, vector_space_object ),
    #                  chi ] );
    #
    #         od;
    #
    #         second_permutation := SemisimpleCategoryMorphism( new_source, second_permutation_morphism_list, new_range );
    #
    #     fi;
    #
    #     return PreCompose( [ first_permutation, morphism_4, second_permutation ] );
    #
    # end );
    #
    # fi; ## associator_available
    #
    # ## -- Helper functions for the braiding --
    #
    # ## the input are objects whose underlying list is of the form [ 1, irr ].
    # braiding_on_irreducibles := function( object_1, object_2 )
    #   local irr_1, irr_2, object, exterior_power_list, exterior_power, object_list, morphism_list,
    #         elem, number_minus_1, number_1, diagonal, homalg_mat, vector_space;
    #
    #   irr_1 := SemisimpleCategoryObjectList( object_1 )[1][2];
    #
    #   irr_2 := SemisimpleCategoryObjectList( object_2 )[1][2];
    #
    #   object := TensorProductOnObjects( object_1, object_2 );
    #
    #   if IsYieldingIdentities( irr_1 ) or IsYieldingIdentities( irr_2 ) then
    #
    #       return IdentityMorphism( object );
    #
    #   fi;
    #
    #   exterior_power_list := ExteriorPower( irr_1, irr_2 );
    #
    #   if IsEmpty( exterior_power_list ) then
    #
    #       return IdentityMorphism( object );
    #
    #   fi;
    #
    #   exterior_power := SemisimpleCategoryObject( exterior_power_list, category );
    #
    #   object_list := SemisimpleCategoryObjectList( object );
    #
    #   morphism_list := [ ];
    #
    #   for elem in object_list do
    #
    #       number_minus_1 := Multiplicity( exterior_power, elem[2] );
    #
    #       number_1 := elem[1] - number_minus_1;
    #
    #       diagonal := Concatenation( List( [ 1 .. number_1 ], i -> 1 ), List( [ 1 .. number_minus_1 ], i -> -1 ) );
    #
    #       homalg_mat := HomalgDiagonalMatrix( diagonal, field );
    #
    #       vector_space := MatrixCategoryObject( underlying_category, elem[1] );
    #
    #       Add( morphism_list, [ VectorSpaceMorphism( vector_space, homalg_mat, vector_space ), elem[2] ] );
    #
    #   od;
    #
    #   return SemisimpleCategoryMorphism( object, morphism_list, object );
    #
    # end;
    #
    # ##
    # InstallMethodWithCacheFromObject( CAP_INTERNAL_Braiding_On_Irreducibles,
    #   [ ObjectFilter( category ) and IsSemisimpleCategoryObject,
    #     ObjectFilter( category ) and IsSemisimpleCategoryObject ],
    #
    #     braiding_on_irreducibles );
    #
    #
    # ##
    # AddBraidingWithGivenTensorProducts( Coproduct,
    #   function( Coproduct, object_a_tensored_object_b, object_a, object_b, object_b_tensored_object_a )
    #     local object_a_list, object_b_list, result_morphism, object_a_expanded_list, object_b_expanded_list,
    #           morphism, outer_summand_list, inner_summand_list, summand_list, elem, elem_a, elem_b;
    #
    #     object_a_list := SemisimpleCategoryObjectListWithActualObjects( object_a );
    #
    #     object_b_list := SemisimpleCategoryObjectListWithActualObjects( object_b );
    #
    #     if IsEmpty( object_a_list ) or IsEmpty( object_b_list ) then
    #
    #         return ZeroMorphism( object_a_tensored_object_b, object_b_tensored_object_a );
    #
    #     fi;
    #
    #     result_morphism := IdentityMorphism( object_a_tensored_object_b );
    #
    #     object_a_expanded_list := CAP_INTERNAL_ExpandSemisimpleCategoryObjectList( object_a_list );
    #
    #     object_b_expanded_list := CAP_INTERNAL_ExpandSemisimpleCategoryObjectList( object_b_list );
    #
    #     ## morphism_1
    #     if Size( object_a_expanded_list ) > 1 then
    #
    #         morphism := RightDistributivityExpanding( object_a_expanded_list, object_b );
    #
    #         result_morphism := PreCompose( result_morphism, morphism );
    #
    #     fi;
    #
    #     ## morphism_2
    #     if Size( object_b_expanded_list ) > 1 then
    #
    #         summand_list := [ ];
    #
    #         for elem in object_a_list do
    #
    #             morphism := LeftDistributivityExpanding( elem[2], object_b_expanded_list );
    #
    #             Append( summand_list, List( [ 1 .. elem[1] ], i -> morphism ) );
    #
    #         od;
    #
    #         morphism := DirectSumFunctorial( summand_list );
    #
    #         result_morphism := PreCompose( result_morphism, morphism );
    #
    #     fi;
    #
    #     ## morphism_3
    #
    #     outer_summand_list := [ ];
    #
    #     for elem_a in object_a_list do
    #
    #         inner_summand_list := [ ];
    #
    #         for elem_b in object_b_list do
    #
    #             morphism := braiding_on_irreducibles( elem_a[2], elem_b[2] );
    #
    #             Append( inner_summand_list, List( [ 1 .. elem_b[1] ], i -> morphism ) );
    #
    #         od;
    #
    #         morphism := DirectSumFunctorial( inner_summand_list );
    #
    #         Append( outer_summand_list, List( [ 1 .. elem_a[1] ], i -> morphism ) );
    #
    #     od;
    #
    #     morphism := DirectSumFunctorial( outer_summand_list );
    #
    #     result_morphism := PreCompose( result_morphism, morphism );
    #
    #     ## morphism_4
    #     if Size( object_b_expanded_list ) > 1 then
    #
    #         summand_list := [ ];
    #
    #         for elem in object_a_list do
    #
    #             morphism := RightDistributivityFactoring( object_b_expanded_list, elem[2] );
    #
    #             Append( summand_list, List( [ 1 .. elem[1] ], i -> morphism ) );
    #
    #         od;
    #
    #         morphism := DirectSumFunctorial( summand_list );
    #
    #         result_morphism := PreCompose( result_morphism, morphism );
    #
    #     fi;
    #
    #     ## morphism_5
    #     if Size( object_a_expanded_list ) > 1 then
    #
    #         morphism := LeftDistributivityFactoring( object_b, object_a_expanded_list );
    #
    #         result_morphism := PreCompose( result_morphism, morphism );
    #
    #     fi;
    #
    #     return result_morphism;
    #
    # end );
    #
    # ##
    # AddDualOnObjects( Coproduct,
    #   function( Coproduct, object )
    #     local object_list, dual_list, elem;
    #
    #     object_list := SemisimpleCategoryObjectList( object );
    #
    #     dual_list := [ ];
    #
    #     for elem in object_list do
    #
    #         Add( dual_list, [ elem[1], Dual( elem[2] ) ] );
    #
    #     od;
    #
    #     return SemisimpleCategoryObject( dual_list, category );
    #
    # end );
    #
    # ##
    # AddDualOnMorphismsWithGivenDuals( Coproduct,
    #   function( Coproduct, dual_source, morphism, dual_range )
    #     local morphism_list;
    #
    #     morphism_list := SemisimpleCategoryMorphismList( morphism );
    #
    #     return SemisimpleCategoryMorphism(
    #              dual_source,
    #              List( morphism_list, elem -> [ DualOnMorphisms( elem[1] ), Dual( elem[2] ) ] ),
    #              dual_range );
    #
    # end );
    #
    # if associator_available then
    #
    # ##
    # AddCoevaluationForDualWithGivenTensorProduct( Coproduct,
    #   function( Coproduct, unit, object, tensor_object )
    #     local object_list, dual_object, dual_object_list, object_expanded_list, elem,
    #           dual_object_expanded_list, dim, matrix_list, zero_list,
    #           summand_list, trivial_chi, vector_space, vector_space_morphism,
    #           i, result_morphism, morphism;
    #
    #     object_list := SemisimpleCategoryObjectListWithActualObjects( object );
    #
    #     if IsEmpty( object_list ) then
    #
    #         return ZeroMorphism( unit, tensor_object );
    #
    #     fi;
    #
    #     dual_object := DualOnObjects( object );
    #
    #     dual_object_list := SemisimpleCategoryObjectListWithActualObjects( dual_object );
    #
    #     object_expanded_list := CAP_INTERNAL_ExpandSemisimpleCategoryObjectList( object_list );
    #
    #     dual_object_expanded_list := CAP_INTERNAL_ExpandSemisimpleCategoryObjectList( dual_object_list );
    #
    #     ## morphism_1
    #
    #     trivial_chi := Support( unit )[1];
    #
    #     matrix_list := [ ];
    #
    #     for elem in object_list do
    #
    #         Add( matrix_list, 1 );
    #
    #         zero_list := List( [ 1 .. elem[1] ], i -> 0 );
    #
    #         for i in [ 2 .. elem[1] ] do
    #
    #             Append( matrix_list, zero_list );
    #
    #             Add( matrix_list, 1 );
    #
    #         od;
    #
    #     od;
    #
    #     dim := Multiplicity( tensor_object, trivial_chi );
    #
    #     vector_space := MatrixCategoryObject( underlying_category, dim );
    #
    #     vector_space_morphism :=
    #       VectorSpaceMorphism( TensorUnit( UnderlyingCategoryForSemisimpleCategory( CapCategory( unit ) ) ),
    #                            HomalgMatrix( matrix_list, 1, dim, field ),
    #                            vector_space );
    #
    #     result_morphism := SemisimpleCategoryMorphismSparse( unit, [ [ vector_space_morphism, trivial_chi ] ], tensor_object );
    #
    #     ## morphism_2 and morphism_3
    #     if Size( object_expanded_list ) > 1 then
    #
    #         ## morphism_2
    #         summand_list := [ ];
    #
    #         for elem in object_list do
    #
    #             morphism := LeftDistributivityFactoring( elem[2], dual_object_expanded_list );
    #
    #             Append( summand_list, List( [ 1 .. elem[1] ], i -> morphism ) );
    #
    #         od;
    #
    #         morphism := DirectSumFunctorial( summand_list );
    #
    #         result_morphism := PreCompose( result_morphism, morphism );
    #
    #         ## morphism_3
    #         morphism := RightDistributivityFactoring( object_expanded_list, dual_object );
    #
    #         result_morphism := PreCompose( result_morphism, morphism );
    #
    #     fi;
    #
    #     return result_morphism;
    #
    # end );
    #
    # ##
    # AddEvaluationForDualWithGivenTensorProduct( Coproduct,
    #   function( Coproduct, tensor_object, object, unit )
    #     local object_list, dual_object, dual_object_list, object_expanded_list, elem,
    #           dual_object_expanded_list, trivial_chi, dim, vector_space, vector_space_morphism,
    #           result_morphism, summand_list, morphism, string, string_entry, i, zero_list;
    #
    #     object_list := SemisimpleCategoryObjectListWithActualObjects( object );
    #
    #     if IsEmpty( object_list ) then
    #
    #         return ZeroMorphism( tensor_object, unit );
    #
    #     fi;
    #
    #     dual_object := DualOnObjects( object );
    #
    #     dual_object_list := SemisimpleCategoryObjectListWithActualObjects( dual_object );
    #
    #     object_expanded_list := CAP_INTERNAL_ExpandSemisimpleCategoryObjectList( object_list );
    #
    #     dual_object_expanded_list := CAP_INTERNAL_ExpandSemisimpleCategoryObjectList( dual_object_list );
    #
    #     ## morphism_3
    #
    #     trivial_chi := Support( unit )[1];
    #
    #     string := "";
    #
    #     for elem in object_list do
    #
    #         string_entry := Concatenation( ",", CAP_INTERNAL_EvaluationForDualOnIrreduciblesAsString( elem[2] ) );
    #
    #         Append( string, string_entry );
    #
    #         zero_list := Concatenation( List( [ 1 .. elem[1] ], i -> ",0" ) );
    #
    #         for i in [ 2 .. elem[1] ] do
    #
    #             Append( string, zero_list );
    #
    #             Append( string, string_entry );
    #
    #         od;
    #
    #     od;
    #
    #     Remove( string, 1 );
    #
    #     string := Concatenation( "[", string, "]" );
    #
    #     dim := Multiplicity( tensor_object, trivial_chi );
    #
    #     vector_space := MatrixCategoryObject( underlying_category, dim );
    #
    #     vector_space_morphism :=
    #       VectorSpaceMorphism( vector_space,
    #                            HomalgMatrix( string, dim, 1, field ),
    #                            TensorUnit( UnderlyingCategoryForSemisimpleCategory( CapCategory( unit ) ) ) );
    #
    #     result_morphism := SemisimpleCategoryMorphismSparse( tensor_object, [ [ vector_space_morphism, trivial_chi ] ], unit );
    #
    #     ## morphism_1 and morphism_2
    #     if Size( object_expanded_list ) > 1 then
    #
    #         ## morphism_2
    #         summand_list := [ ];
    #
    #         for elem in dual_object_list do
    #
    #             morphism := LeftDistributivityExpanding( elem[2], object_expanded_list );
    #
    #             Append( summand_list, List( [ 1 .. elem[1] ], i -> morphism ) );
    #
    #         od;
    #
    #         morphism := DirectSumFunctorial( summand_list );
    #
    #         result_morphism := PreCompose( morphism, result_morphism );
    #
    #         ## morphism_1
    #         morphism := RightDistributivityExpanding( dual_object_expanded_list, object );
    #
    #         result_morphism := PreCompose( morphism, result_morphism );
    #
    #     fi;
    #
    #     return result_morphism;
    #
    # end );
    #
    # fi;
    
    ##
    # AddMorphismToBidualWithGivenBidual( Coproduct,
    #   function( Coproduct, object, bidual_of_object )
    #
    #     return VectorSpaceMorphism( object,
    #                                 HomalgIdentityMatrix( Dimension( object ), homalg_field ),
    #                                 bidual_of_object
    #                               );
    #
    # end );
    
    Finalize( Coproduct );
    
    ####################################
    # Reinterpretation
    ####################################
    
    ##
    object_datum_type :=
        CapJitDataTypeOfListOf(
            CapJitDataTypeOfNTupleOf( 2, IsBigInt, IsBigInt ) );
    
    ##
    object_datum := { SGReps, obj } -> ListOfPairsOfRankAndIndex( obj );
    
    ##
    object_constructor :=
      function( SGReps, list_of_pairs_of_rank_and_index )
        local nr_irreducible_characters, pair, pair_1, pair_2, i;
        
        nr_irreducible_characters := NrIrreducibleCharacters( SGReps );
        
        # The number of pairs can be at most 'nr_irreducible_characters'.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( list_of_pairs_of_rank_and_index ) <= nr_irreducible_characters );
        
        # The rank must be non-negative and the character indices
        # must be in the correct range.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0,
            ForAll( list_of_pairs_of_rank_and_index, pair ->
                0 <= pair[1] and 1 <= pair[2] and pair[2] <= nr_irreducible_characters ) );
        
        # Character indices must be strictly increasing.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0,
            ForAll( [ 1 .. Length( list_of_pairs_of_rank_and_index ) - 1 ], i ->
                list_of_pairs_of_rank_and_index[ i ][2] < list_of_pairs_of_rank_and_index[ i + 1 ][2] ) );
        
        return CreateCapCategoryObjectWithAttributes( SGReps,
                   ListOfPairsOfRankAndIndex, list_of_pairs_of_rank_and_index );
        
    end;
    
    ##
    morphism_datum_type :=
        CapJitDataTypeOfListOf(
            CapJitDataTypeOfNTupleOf( 2, IsHomalgMatrix, IsBigInt ) );
    
    ##
    morphism_datum := { SGReps, phi } -> ListOfPairsOfMatrixAndIndex( phi );
    
    ##
    morphism_constructor :=
      function( SGReps, S, list_of_pairs_of_matrix_and_index, T )
        local nr_irreducible_characters, s_pair, matrix_pair, source_rank, source_index, t_pair, target_rank, target_index;
        
        nr_irreducible_characters := NrIrreducibleCharacters( SGReps );
        
        # The number of pairs can be at most 'nr_irreducible_characters'.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( list_of_pairs_of_matrix_and_index ) <= nr_irreducible_characters );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0,
            ForAll( list_of_pairs_of_matrix_and_index, pair ->
                HomalgRing( pair[1] ) = UnderlyingSplittingField( SGReps ) and
                NrRows( pair[1] ) = Component( S, pair[2] )  and
                NrColumns( pair[1] ) = Component( T, pair[2] ) ) );
        
        # For any source pair [r,l] with r =/= 0, there must
        # explicitly be a morphism pair [m,l] with NrRows( m ) = r.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        for s_pair in ListOfPairsOfRankAndIndex( S ) do
            
            source_rank := s_pair[1];
            source_index := s_pair[2];
            
            if source_rank <> 0 then
                
                # Find the matrix at index 'source_index'.
                matrix_pair := First( Filtered( list_of_pairs_of_matrix_and_index, m_pair -> m_pair[2] = source_index ) );
                
                # Did we find a source rank =/= 0 but not a matrix for it?
                Assert( 0, fail <> matrix_pair[1] );
                
                Assert( 0, source_rank = NrRows( matrix_pair[1] ) );
                
            fi;
            
        od;
        
        # For any target pair [r,l] with r =/= 0, there must
        # explicitly be a morphism pair [m,l] with NrCols( m ) = r.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        for t_pair in ListOfPairsOfRankAndIndex( T ) do
            
            target_rank := t_pair[1];
            target_index := t_pair[2];
            
            if target_rank <> 0 then
                
                # Find the matrix at index 'target_index'.
                matrix_pair := First( Filtered( list_of_pairs_of_matrix_and_index, m_pair -> m_pair[2] = target_index ) );
                
                # Did we find a target rank =/= 0 but not a matrix for it?
                Assert( 0, fail <> matrix_pair );
                
                Assert( 0, NrCols( matrix_pair[1] ) = target_rank );
                
            fi;
            
        od;
        
        return CreateCapCategoryMorphismWithAttributes( SGReps,
                    S,
                    T,
                    ListOfPairsOfMatrixAndIndex, list_of_pairs_of_matrix_and_index );
        
    end;
    
    ####################################
    # Modeling
    ####################################
    
    ## From the raw object data to the object in the modeling category
    modeling_tower_object_constructor :=
      function( SGReps, list_of_pairs_of_rank_and_index )
        local Coproduct, Rows, list_of_pairs_of_object_and_index;
        
        Coproduct := ModelingCategory( SGReps );
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        # Turn the ranks into objects of Rows.
        list_of_pairs_of_object_and_index :=
            List( list_of_pairs_of_rank_and_index, pair ->
                [ CategoryOfRowsObject( Rows, pair[1] ), pair[2] ] );
        
        return ObjectConstructor( Coproduct, list_of_pairs_of_object_and_index );
        
    end;
    
    ## From the object in the modeling category to the raw object data.
    modeling_tower_object_datum :=
      function( SGReps, object )
        local list_of_pairs_of_rank_and_index;
        
        # Turn the objects in the category of rows into their ranks/integers.
        list_of_pairs_of_rank_and_index :=
            List( ListOfPairsOfObjectAndIndex( object ), pair ->
                [ RankOfObject( pair[1] ), pair[2] ] );
        
        return list_of_pairs_of_rank_and_index;
        
    end;
    
    ## From the raw morphism data to the morphism in the modeling category.
    modeling_tower_morphism_constructor :=
      function( SGReps, source, list_of_pairs_of_matrix_and_index, target )
        local Coproduct, Rows, list_of_pairs_of_morphism_and_index;
        
        Coproduct := ModelingCategory( SGReps );
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        # Turn the matrices into morphisms of Rows.
        list_of_pairs_of_morphism_and_index :=
            List( list_of_pairs_of_matrix_and_index, pair ->
                [ AsCategoryOfRowsMorphism( Rows, pair[1] ), pair[2] ] );
        
        return MorphismConstructor( Coproduct,
                    source,
                    list_of_pairs_of_morphism_and_index,
                    target );
        
    end;
    
    ## From the morphism in the modeling category to the raw morphism data
    modeling_tower_morphism_datum :=
      function( SGReps, morphism )
        local list_of_pairs_of_matrix_and_index;
        
        # Turn the morphism in the category of rows into their underlying matrices.
        list_of_pairs_of_matrix_and_index :=
            List( ListOfPairsOfMorphismAndIndex( morphism ), pair ->
                [ UnderlyingMatrix( pair[1] ), pair[2] ] );
        
        return list_of_pairs_of_matrix_and_index;
        
    end;
    
    name := Concatenation( "SkeletalGroupRepresentations( ", String( G ), ", ", String( splitting_field ), " )" );
    
    SGReps :=
        ReinterpretationOfCategory( Coproduct,
            rec( name := name,
                 category_filter := IsSkeletalCategoryOfGroupRepresentations,
                 category_object_filter := IsObjectInSkeletalCategoryOfGroupRepresentations,
                 category_morphism_filter := IsMorphismInSkeletalCategoryOfGroupRepresentations,
                 object_constructor := object_constructor,
                 object_datum := object_datum,
                 morphism_constructor := morphism_constructor,
                 morphism_datum := morphism_datum,
                 modeling_tower_object_constructor := modeling_tower_object_constructor,
                 modeling_tower_object_datum := modeling_tower_object_datum,
                 modeling_tower_morphism_constructor := modeling_tower_morphism_constructor,
                 modeling_tower_morphism_datum := modeling_tower_morphism_datum,
                 only_primitive_operations := true, )
            : FinalizeCategory := false );
    
    # DeactivateCachingOfCategory( SGReps );
    
    # CapCategorySwitchLogicOff( SGReps );
    
    # SetIsRigidSymmetricClosedMonoidalCategory( SGReps, true );
    
    SetUnderlyingCoproductOfCategoryOfRows( SGReps, Coproduct );
    
    SetUnderlyingSplittingField( SGReps, splitting_field );
    
    SetUnderlyingGroup( SGReps, G );
    
    SetUnderlyingCharacterTable( SGReps, character_table );
    
    SetUnderlyingIrreducibleCharacters( SGReps, irreducible_characters );
    
    SetNrIrreducibleCharacters( SGReps, nr_irreducible_characters );
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        
        Finalize( SGReps );
        
    fi;
    
    return SGReps;
    
end ) );

####################################
##
## Attributes
##
####################################


####################################
##
## Operations
##
####################################

InstallMethodForCompilerForCAP( Component,
                                [ IsObjectInSkeletalCategoryOfGroupRepresentations, IsBigInt ],
                                
  function( object, i )
    local component;
    
    Assert( 0, 1 <= i and i <= NrIrreducibleCharacters( CapCategory( object ) ) );
    
    component := First( ListOfPairsOfRankAndIndex( object ), pair -> pair[2] = i );
    
    if component = fail then
        
        return 0;
        
    fi;
    
    return component[1];
    
end );

InstallMethodForCompilerForCAP( Component,
                                [ IsMorphismInSkeletalCategoryOfGroupRepresentations, IsBigInt ],
                                
  function( morphism, i )
    local component, Rows, source, target;
    
    Assert( 0, 1 <= i and i <= NrIrreducibleCharacters( CapCategory( morphism ) ) );
    
    component := First( ListOfPairsOfMatrixAndIndex( morphism ), pair -> pair[2] = i );
    
    if component = fail then
        
        Rows := UnderlyingCategoryOfRows( CapCategory( morphism ) );
        
        source := Component( Source( morphism ), i );
        target := Component( Target( morphism ), i );
        
        return HomalgZeroMatrix( source, target, UnderlyingRing( Rows ) );
        
    fi;
    
    return component[1];
    
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

####################################
##
## Global functions
##
####################################

InstallGlobalFunction( CAP_INTERNAL_skeletal_group_reps_decompose_character,
  function( Rows, irreducible_characters, product_of_characters )
    local decomposed_product, i, scalar_product;
    
    decomposed_product := [ ];
    
    for i in [ 1 .. Length( irreducible_characters ) ] do
        
        scalar_product :=
            ScalarProduct( irreducible_characters[ i ], product_of_characters );
        
        if scalar_product <> 0 then
            
            Add( decomposed_product,
                 [ CategoryOfRowsObject( Rows, scalar_product ), i ] );
            
        fi;
        
    od;
    
    return decomposed_product;
    
end );

####################################
##
## View & Display
##
####################################

SubscriptDigits := [ "₀", "₁", "₂", "₃", "₄", "₅", "₆", "₇", "₈", "₉" ];

# Convert a number into a unicode subscript.
ToSubscript := function ( n )
    local digits, subscripts, d;
    
    if n = 0 then
        
        return SubscriptDigits[1];  #₀
        
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
    local string, characters, pairs, SubscriptDigits, i, character_nr, pair, nonzero_pairs;
    
    string := "";
    
    pairs := ListOfPairsOfRankAndIndex( object );
    
    nonzero_pairs := Filtered( pairs, pair -> pair[1] <> 0 );
    
    if Length( nonzero_pairs ) = 0 then
        
        string := String( 0 );
        
    elif Length( nonzero_pairs ) = 1 then
        
        character_nr := nonzero_pairs[1][2];
        string := Concatenation( String( nonzero_pairs[1][1] ), "χ", ToSubscript( character_nr ) );
        
    elif Length( nonzero_pairs ) > 1 then
        
        character_nr := nonzero_pairs[1][2];
        string := Concatenation( String( nonzero_pairs[1][1] ), "χ", ToSubscript( character_nr ) );
        
        for pair in nonzero_pairs{[ 2 .. Length( nonzero_pairs ) ]} do
            
            character_nr := pair[2];
            string := Concatenation( string, "⊕ ", String( pair[1] ), "χ", ToSubscript( character_nr )  );
            
        od;
        
    fi;
    
    return string;
    
end );

##
InstallMethod( Display,
               [ IsMorphismInSkeletalCategoryOfGroupRepresentations ],
               
  function( morphism )
    local pair;
    
    Print( "\n" );
    
    for pair in ListOfPairsOfMatrixAndIndex( morphism ) do
        
        Display( Concatenation( "Component: χ", ToSubscript( pair[2] ), "\n" ) );
        
        Display( pair[1] );
        
        Display( "\n------------------------\n" );
        
    od;
    
end );

