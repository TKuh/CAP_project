# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Implementations
#

# 1 ≤ i ≤ m = Support(a)
#
# (a⊗b)⊗c
#     │
#     │ σ((χ₁,...,χ₁,...,χₘ,...,χₘ), b) ⊗ 1𞁞
#     │    └───────┘     └───────┘
#     │    a₁ times      aₘ times
#     ↓
# (⊕ᵢ aᵢ·(χᵢ⊗b))⊗c
#     │
#     │ σ((χ₁⊗b,...,χ₁⊗b,...,χₘ⊗b,...,χₘ⊗b), c)
#     │    └───────────┘     └───────────┘
#     │      a₁ times          aₘ times
#     ↓
# ⊕ᵢ aᵢ·[(χᵢ⊗b)⊗c],
InstallGlobalFunction( SGREPS_Associator_1_Morphism_multiplicity,
  function( product_insmat, a, b, c, abc )
    local product_permcat, F_product_permcat, a_nr_support, a_support, a_components, a_model, b_model, c_model, ab, a_xi, a_xi_tensor_b, sigma_1, sigma_1_tensor_id_c, sigma_2;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    product_permcat := UnderlyingProductCategoryOfPermutationCategory( product_insmat );
    F_product_permcat := IsomorphismFromCoreToProductCategoryOfPermutationCategory( product_insmat );
    
    a_nr_support := NrSupport( a );
    a_support := Support( a );
    a_components := Components( a );
    
    ab := TensorProductOnObjects( product_insmat, a, b );
    
    # [ χ₁, χ₂, ..., χₘ ]
    a_xi := List( [ 1 .. a_nr_support ], i ->
        ObjectConstructor( product_insmat, NTuple( 3, 1, [ a_support[i] ], [ 1 ] ) ) );
    
    # a⊗b = [(χ₁ ⊕...⊕ χ₁) ⊕...⊕ (χₘ ⊕...⊕ χₘ)] ⊗ b  ⥲  (χ₁⊗b ⊕...⊕ χ₁⊗b) ⊕...⊕ (χₘ⊗b ⊕...⊕ χₘ⊗b) = ⊕ᵢ aᵢ·(χᵢ⊗b)
    sigma_1 := RightDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_insmat, ab, a_xi, b, a_components, ab );
    
    # (a⊗b)⊗c  ⥲  (⊕ᵢ aᵢ·(χᵢ⊗b))⊗c
    sigma_1_tensor_id_c := PRODUCT_OF_CATEGORY_OF_INSERTION_MATRICES_AS_SUBCAT_TensorProductOfMorphismWithIdentityWithGivenTensorProducts(
                                product_insmat,
                                abc,
                                sigma_1,
                                IdentityMorphism( product_insmat, c ),
                                abc );
    
    # [ χ₁⊗b, χ₂⊗b, ..., χₘ⊗b ]
    a_xi_tensor_b := List( a_xi, x_i -> TensorProductOnObjects( product_insmat, x_i, b ) );
    
    # (⊕ᵢ aᵢ·(χᵢ⊗b))⊗c = [(χ₁⊗b ⊕...⊕ χ₁⊗b) ⊕...⊕ (χₘ⊗b ⊕...⊕ χₘ⊗b)] ⊗ c  ⥲  ((χ₁⊗b)⊗c ⊕...⊕ (χ₁⊗b)⊗c) ⊕...⊕ ((χₘ⊗b)⊗c ⊕...⊕ (χₘ⊗b)⊗c) = ⊕ᵢ aᵢ·[(χᵢ⊗b)⊗c]
    sigma_2 := RightDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_insmat, abc, a_xi_tensor_b, c, a_components, abc );
    
    # The composition of permutations π₂·π₁ corresponds to the permutation-matrix product P₁·P₂.
    return PreCompose( product_permcat,
                       ApplyFunctor( F_product_permcat, sigma_2 ),
                       ApplyFunctor( F_product_permcat, sigma_1_tensor_id_c ) );
    
end );

# 1 ≤ i ≤ m = Support(a)
# 1 ≤ j ≤ n = Support(b)
#
# ⊕ᵢ ɑᵢ·[(χᵢ⊗b)⊗c]
#        │
#        │ ⊕ᵢ ɑᵢ·[ σ(χᵢ, (χ₁,...,χ₁,...,χₙ,...,χₙ)) ⊗ 1𞁞 ]
#        │                └───────┘     └───────┘
#        │                b₁ times      bₙ times
#        ↓
# ⊕ᵢ ɑᵢ·[ [⊕ⱼ bⱼ·(χᵢ⊗χⱼ)] ⊗ c ]
#        │
#        │ ⊕ᵢ ɑᵢ·σ((χᵢ⊗χ₁,...,χᵢ⊗χ₁,...,χᵢ⊗χₙ,...,χᵢ⊗χₙ), c)
#        │          └─────────────┘     └─────────────┘
#        │              b₁ times             bₙ times
#        ↓
# ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ (χᵢ⊗χⱼ)⊗c ] ]
InstallGlobalFunction( SGREPS_Associator_2_Morphism_multiplicity,
  function( product_insmat, a, b, c, abc )
    local product_permcat, F_product_permcat, a_nr_support, a_support, a_components, b_nr_support, b_support, b_components, b_xj, sigmas, a_sigmas, sum_a_sigmas;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    product_permcat := UnderlyingProductCategoryOfPermutationCategory( product_insmat );
    F_product_permcat := IsomorphismFromCoreToProductCategoryOfPermutationCategory( product_insmat );
    
    a_nr_support := NrSupport( a );
    a_support := Support( a );
    a_components := Components( a );
    
    b_nr_support := NrSupport( b );
    b_support := Support( b );
    b_components := Components( b );
    
    # [ χ₁, χ₂, ..., χₙ ]
    b_xj := List( [ 1 .. b_nr_support ], j ->
        ObjectConstructor( product_insmat, NTuple( 3, 1, [ b_support[j] ], [ 1 ] ) ) );
    
    # The list of composed expanding morphisms:
    # σᵢ: (χᵢ⊗b)⊗c  ⥲  ⊕ⱼ bⱼ·[ (χᵢ⊗χⱼ)⊗c ]
    sigmas := List( [ 1 .. a_nr_support ], function( i )
        local xi, xib, xibc, sigma_1, sigma_1_tensor_id_c, xixj, sigma_2;
        
        xi := ObjectConstructor( product_insmat, NTuple( 3, 1, [ a_support[i] ], [ 1 ] ) );
        xib := TensorProductOnObjects( product_insmat, xi, b );
        xibc := TensorProductOnObjects( product_insmat, xib, c );
        
        # χᵢ⊗b = [χᵢ⊗(b₁χ₁ ⊕...⊕ bₖχₖ)] = [χᵢ⊗(χ₁⊕...⊕ χ₁ ⊕...⊕ χₖ ⊕...⊕ χₖ)]  ⥲  (χᵢ⊗χ₁ ⊕...⊕ χᵢ⊗χ₁ ⊕...⊕ χᵢ⊗χₖ ⊕...⊕ χᵢ⊗χₖ) = [⊕ⱼ bⱼ·(χᵢ⊗χⱼ)]
        sigma_1 := LeftDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_insmat, xib, xi, b_xj, b_components, xib );
        
        # [χᵢ⊗b]⊗c  ⥲  [⊕ⱼ bⱼ·(χᵢ⊗χⱼ)]⊗c
        sigma_1_tensor_id_c := PRODUCT_OF_CATEGORY_OF_INSERTION_MATRICES_AS_SUBCAT_TensorProductOfMorphismWithIdentityWithGivenTensorProducts(
                                    product_insmat,
                                    xibc,
                                    sigma_1,
                                    IdentityMorphism( product_insmat, c ),
                                    xibc );
        
        xixj := List( [ 1 .. b_nr_support ], j -> TensorProductOnObjects( product_insmat, xi, b_xj[j] ) );
        
        # [⊕ⱼ bⱼ·(χᵢ⊗χⱼ)]⊗c  ⥲  ⊕ⱼ bⱼ·[ (χᵢ⊗χⱼ)⊗c ]
        sigma_2 := RightDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_insmat, xibc, xixj, c, b_components, xibc );
        
        # Error( "\033[31mDEBUGPRINT[Second expanding]\033[0m" );
        
        return PreCompose( product_permcat,
                           ApplyFunctor( F_product_permcat, sigma_1_tensor_id_c ),
                           ApplyFunctor( F_product_permcat, sigma_2 ) );
        
    end );
    
    # ɑᵢ·σᵢ
    a_sigmas := Concatenation( List( [ 1 .. a_nr_support ], i -> List( [ 1 .. a_components[i] ], j -> sigmas[i] ) ) );
    
    # ⊕ᵢ ɑᵢ·σᵢ:  ɑᵢ·[(χᵢ⊗b)⊗c]  ⥲  ɑᵢ·[ ⊕ⱼ bⱼ·[ (χᵢ⊗χⱼ)⊗c ] ]
    sum_a_sigmas := CoproductFunctorialWithGivenCoproducts( product_permcat,
                            ApplyFunctor( F_product_permcat, abc ),
                            List( a_sigmas, Source ),
                            a_sigmas,
                            List( a_sigmas, Target ),
                            ApplyFunctor( F_product_permcat, abc ) );
    
    return sum_a_sigmas;
    
end );

# 1 ≤ i ≤ m = Support(a)
# 1 ≤ j ≤ n = Support(b)
# 1 ≤ k ≤ o = Support(c)
#
# ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ (χᵢ⊗χⱼ)⊗c ] ]
#        │
#        │ ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·σ_(χᵢ⊗χⱼ, (χ₁,...,χ₁,...,χₒ,...,χₒ)) ]
#        │                          └───────┘     └───────┘
#        │                          c₁ times,     cₒ times
#        ↓
# ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ ⊕ₖ cₖ·[ (χᵢ⊗χⱼ)⊗χₖ ] ] ]
InstallGlobalFunction( SGREPS_Associator_3_Morphism_multiplicity,
  function( product_insmat, a, b, c, abc )
    local product_permcat, F_product_permcat, a_nr_support, a_support, a_components, b_nr_support, b_support, b_components, c_nr_support, c_support, c_components, c_xk, inner_factors, a_inner_factors, outer_product;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    product_permcat := UnderlyingProductCategoryOfPermutationCategory( product_insmat );
    F_product_permcat := IsomorphismFromCoreToProductCategoryOfPermutationCategory( product_insmat );
    
    a_nr_support := NrSupport( a );
    a_support := Support( a );
    a_components := Components( a );
    
    b_nr_support := NrSupport( b );
    b_support := Support( b );
    b_components := Components( b );
    
    c_nr_support := NrSupport( c );
    c_support := Support( c );
    c_components := Components( c );
    
    # [ χ₁, χ₂, ..., χₒ ]
    c_xk := List( [ 1 .. c_nr_support ], k ->
        ObjectConstructor( product_insmat, NTuple( 3, 1, [ c_support[k] ], [ 1 ] ) ) );
    
    # ⊕ⱼ bⱼ·σⱼ:  bⱼ·[(χᵢ⊗xⱼ)⊗c]  ⥲  bⱼ·[⊕ₖ cₖ·[(χᵢ⊗χⱼ)⊗χₖ]]
    inner_factors := List( [ 1 .. a_nr_support ], function( i )
        local xi, sigmas, b_sigmas, xibc, sum_b_sigmas;
        
        xi := ObjectConstructor( product_insmat, NTuple( 3, 1, [ a_support[i] ], [ 1 ] ) );
        
        # σⱼ:  (χᵢ⊗xⱼ)⊗c = [(χᵢ⊗xⱼ) ⊗ (χ₁ ⊕...⊕ χ₁ ⊕...⊕ χₒ ⊕...⊕ χₒ)]  ⥲  ((χᵢ⊗xⱼ)⊗χ₁ ⊕...⊕ (χᵢ⊗xⱼ)⊗χ₁ ⊕...⊕ (χᵢ⊗xⱼ)⊗χₒ ⊕...⊕ (χᵢ⊗xⱼ)⊗χₒ) = ⊕ₖ cₖ·[(χᵢ⊗χⱼ)⊗χₖ]
        sigmas := List( [ 1 .. b_nr_support ], function( j )
            local xj, xixj, xixjc;
            
            xj := ObjectConstructor( product_insmat, NTuple( 3, 1, [ b_support[j] ], [ 1 ] ) );
            xixj := TensorProductOnObjects( product_insmat, xi, xj );
            xixjc := TensorProductOnObjects( product_insmat, xixj, c );
            
            return LeftDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_insmat, xixjc, xixj, c_xk, c_components, xixjc );
            
        end );
        
        # bⱼ·σⱼ
        b_sigmas := Concatenation( List( [ 1 .. b_nr_support ], i ->
            List( [ 1 .. b_components[i] ], j -> sigmas[i] ) ) );
            
        xibc := TensorProductOnObjects( product_insmat, TensorProductOnObjects( product_insmat, xi, b ), c );
        
        # ⊕ⱼ bⱼ·σⱼ:  bⱼ·[(χᵢ⊗xⱼ)⊗c]  ⥲  bⱼ·[⊕ₖ cₖ·[(χᵢ⊗χⱼ)⊗χₖ]]
        sum_b_sigmas := DirectProductFunctorialWithGivenDirectProducts( product_insmat,
                            xibc,
                            List( b_sigmas, Source ),
                            b_sigmas,
                            List( b_sigmas, Target ),
                            xibc );
        
        return sum_b_sigmas;
        
    end );
    
    # The list of aᵢ-many duplications of ⊕ⱼ bⱼ·σⱼ.
    a_inner_factors := Concatenation( List( [ 1 .. a_nr_support ], i ->
        List( [ 1 .. a_components[i] ], j -> inner_factors[i] ) ) );
    
    # ⊕ᵢ ɑᵢ·[⊕ⱼ bⱼ·σⱼ]:  ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ (χᵢ⊗χⱼ)⊗c ] ]  ⥲  ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ ⊕ₖ cₖ·[ (χᵢ⊗χⱼ)⊗χₖ ] ] ]
    outer_product := DirectProductFunctorialWithGivenDirectProducts( product_insmat,
                            abc,
                            List( a_inner_factors, Source ),
                            a_inner_factors,
                            List( a_inner_factors, Target ),
                            abc );
    
    return ApplyFunctor( F_product_permcat, outer_product );
    
end );

# ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ ⊕ₖ cₖ·[ (χᵢ⊗χⱼ)⊗χₖ ] ] ]
#                   │
#                   │ ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·αᵢⱼₖ ]
#                   ↓
# ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ ⊕ₖ cₖ·[ χᵢ⊗(χⱼ⊗χₖ) ] ] ]
# 
# TODO: use abc somewhere?
InstallGlobalFunction( SGREPS_Associator_4_Morphism_multiplicity,
  function( SGReps, a, b, c, abc )
    local DS, Rows, splitting_field, unit, associator_data, a_nr_support, a_support, a_components, b_nr_support, b_support, b_components, c_nr_support, c_support, c_components, outer_factors, a_factors, a_product;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    DS := ModelingCategory( SGReps );
    
    Rows := UnderlyingAdditiveCategory( DS );
    
    splitting_field := UnderlyingSplittingField( SGReps );
    
    unit := TensorUnit( SGReps );
    
    associator_data := AssociatorData( SGReps );
    
    a_nr_support := NrSupport( a );
    a_support := Support( a );
    a_components := Components( a );
    
    b_nr_support := NrSupport( b );
    b_support := Support( b );
    b_components := Components( b );
    
    c_nr_support := NrSupport( c );
    c_support := Support( c );
    c_components := Components( c );
    
    outer_factors := List( [ 1 .. a_nr_support ], function( i )
        local xi, inner_factors, b_factors, b_sum;
        
        xi := ObjectConstructor( SGReps, NTuple( 3, 1, [ a_support[i] ], [ 1 ] ) );
        
        inner_factors := List( [ 1 .. b_nr_support ], function( j )
            local xj, factors, c_factors, c_sum;
            
            xj := ObjectConstructor( SGReps, NTuple( 3, 1, [ b_support[j] ], [ 1 ] ) );
            
            factors := List( [ 1 .. c_nr_support ], function( k )
                local xk, xixjxk, xixjxk_nr_support, xixjxk_support, xixjxk_components, morphism_list;
                
                xk := ObjectConstructor( SGReps, NTuple( 3, 1, [ c_support[k] ], [ 1 ] ) );
                
                xixjxk := TensorProductOnObjects( SGReps, TensorProductOnObjects( SGReps, xi, xj ), xk );
                
                if IsEqualForObjects( SGReps, xi, unit ) or
                   IsEqualForObjects( SGReps, xj, unit ) or
                   IsEqualForObjects( SGReps, xk, unit ) then
                    
                    return IdentityMorphism( SGReps, xixjxk );
                    
                else
                    
                    xixjxk_nr_support := NrSupport( xixjxk );
                    xixjxk_support := Support( xixjxk );
                    xixjxk_components := Components( xixjxk );
                    
                    morphism_list := List( [ 1 .. xixjxk_nr_support ], function( l )
                        local matrices, string, dimension, homalg_matrix;
                        
                        matrices := associator_data[ a_support[i] ][ b_support[j] ][ c_support[k] ];
                        
                        string := Concatenation( "[", matrices[ xixjxk_support[l] ], "]" );
                        
                        dimension := xixjxk_components[l];
                        
                        homalg_matrix := HomalgMatrix( string, dimension, dimension, splitting_field );
                        # homalg_matrix := HomalgIdentityMatrix( dimension, splitting_field ); # Wrong, only shows that the type signature problems stem from here.
                        
                        return homalg_matrix;
                        
                    end );
                    
                    return MorphismConstructor( SGReps,
                                xixjxk,
                                NTuple( 3, xixjxk_nr_support, xixjxk_support, morphism_list ),
                                xixjxk );
                    
                fi;
                
            end );
            
            c_factors := Concatenation( List( [ 1 .. c_nr_support ], k ->
                List( [ 1 .. c_components[k] ], l -> factors[k] ) ) );
                
            c_sum := DirectSumFunctorial( SGReps, c_factors );
            
            return c_sum;
            
        end );
        
        b_factors := Concatenation( List( [ 1 .. b_nr_support ], j ->
            List( [ 1 .. b_components[j] ], k -> inner_factors[j] ) ) );
            
        b_sum := DirectSumFunctorial( SGReps, b_factors );
        
        return b_sum;
        
    end );
    
    a_factors := Concatenation( List( [ 1 .. a_nr_support ], i ->
        List( [ 1 .. a_components[i] ], j -> outer_factors[i] ) ) );
    
    a_product := DirectSumFunctorial( SGReps, a_factors );
    
    return a_product;
    
end );

# 1 ≤ i ≤ m = Support(a)
# 1 ≤ j ≤ n = Support(b)
# 1 ≤ k ≤ o = Support(c)
#
# ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ ⊕ₖ cₖ·[ χᵢ⊗(χⱼ⊗χₖ) ] ] ]
#        │
#        │ ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ σ⁻¹(χᵢ, (χᵢ⊗(χⱼ⊗χ₁),...,χᵢ⊗(χⱼ⊗χ₁),...,χᵢ⊗(χⱼ⊗χₒ),...,χᵢ⊗(χⱼ⊗χₒ))) ] ]
#        │                          └───────────────────────┘     └───────────────────────┘
#        │                                   c₁ times                        cₒ times
#        ↓
# ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ χᵢ⊗(⊕ₖ cₖ·[χⱼ⊗χₖ]) ] ]
#        │
#        │ ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ 1_χᵢ ⊗  σ⁻¹(χⱼ, (χⱼ⊗χ₁,...,χⱼ⊗χ₁,...,χⱼ⊗χₖ,...,χⱼ⊗χₖ)) ] ]
#        │                                  └─────────────┘     └─────────────┘
#        │                                      c₁ times             cₒ times
#        ↓
# ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ χᵢ⊗(χⱼ⊗ (⊕ₖ cₖ·χₖ)) ] ]
#        ‖
# ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ χᵢ⊗(χⱼ⊗c) ] ]
InstallGlobalFunction( SGREPS_Associator_5_Morphism_multiplicity,
  function( product_insmat, a, b, c, abc )
    local product_permcat, F_product_permcat, a_nr_support, a_support, a_components, b_nr_support, b_support, b_components, c_nr_support, c_support, c_components, bc, c_xk, inner_factors, a_inner_factors, xibc, outer_product;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    product_permcat := UnderlyingProductCategoryOfPermutationCategory( product_insmat );
    F_product_permcat := IsomorphismFromCoreToProductCategoryOfPermutationCategory( product_insmat );
    
    a_nr_support := NrSupport( a );
    a_support := Support( a );
    a_components := Components( a );
    
    b_nr_support := NrSupport( b );
    b_support := Support( b );
    b_components := Components( b );
    
    c_nr_support := NrSupport( c );
    c_support := Support( c );
    c_components := Components( c );
    
    bc := TensorProductOnObjects( product_insmat, b, c );
    
    # [ χ₁, χ₂, ..., χₒ ]
    c_xk := List( [ 1 .. c_nr_support ], k ->
        ObjectConstructor( product_insmat, NTuple( 3, 1, [ c_support[k] ], [ 1 ] ) ) );
    
    # ⊕ⱼ bⱼ·σⱼ: ⊕ⱼ bⱼ·[⊕ₖ cₖ·[χᵢ⊗(χⱼ⊗χₖ)]]  ⥲  ⊕ⱼ bⱼ·[χᵢ⊗(⊕ₖ cₖ·[χⱼ⊗χₖ])]
    inner_factors := List( [ 1 .. a_nr_support ], function( i )
        local xi, sigmas, b_sigmas, xibc, sum_b_sigmas;
        
        xi := ObjectConstructor( product_insmat, NTuple( 3, 1, [ a_support[i] ], [ 1 ] ) );
        
        # σⱼ: ⊕ₖ cₖ·[ χᵢ⊗(χⱼ⊗χₖ) ]  ⥲  χᵢ⊗(χⱼ⊗ (⊕ₖ cₖ·χₖ)) = χᵢ⊗(χⱼ⊗c)
        sigmas := List( [ 1 .. b_nr_support ], function( j )
            local xj, xjc, xixjc, xjxk, first_left_expanding, first_left_factoring, second_left_expanding, second_left_factoring, id_xi_tensor_second_left_factoring;
            
            xj := ObjectConstructor( product_insmat, NTuple( 3, 1, [ b_support[j] ], [ 1 ] ) );
            xjc := TensorProductOnObjects( product_insmat, xj, c );
            xjxk := List( [ 1 .. c_nr_support ], k -> TensorProductOnObjects( product_insmat, xj, c_xk[k] ) );
            xixjc := TensorProductOnObjects( product_insmat, xi, xjc );
            
            # ⊕ₖ cₖ·[ χᵢ⊗(χⱼ⊗χₖ) ]  ⥲  χᵢ⊗(⊕ₖ cₖ·[χⱼ⊗χₖ])
            first_left_expanding := LeftDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_insmat, xixjc, xi, xjxk, c_components, xixjc );
            first_left_factoring := Inverse( ApplyFunctor( F_product_permcat, first_left_expanding ) );
            
            # ⊕ₖ cₖ·[χⱼ⊗χₖ]  ⥲  χⱼ⊗ (⊕ₖ cₖ·χₖ) = χⱼ⊗c
            second_left_expanding := LeftDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_insmat, xjc, xj, c_xk, c_components, xjc );
            second_left_factoring := Inverse( ApplyFunctor( F_product_permcat, second_left_expanding ) );
            
            # χᵢ⊗(⊕ₖ cₖ·[χⱼ⊗χₖ])  ⥲  χᵢ⊗(χⱼ⊗ (⊕ₖ cₖ·χₖ)) = χᵢ⊗(χⱼ⊗c)
            id_xi_tensor_second_left_factoring :=
                PRODUCT_OF_PERMUTATIONCATEGORY_AS_SUBCAT_TensorProductOfIdentityWithMorphismWithGivenTensorProducts(
                    product_permcat,
                    ApplyFunctor( F_product_permcat, xixjc ),
                    IdentityMorphism( product_permcat, ApplyFunctor( F_product_permcat, xi ) ),
                    second_left_factoring,
                    ApplyFunctor( F_product_permcat, xixjc ) );
            
            # The composition of permutations π₂·π₁ corresponds to the permutation-matrix product P₁·P₂.
            return PreCompose( product_permcat, id_xi_tensor_second_left_factoring, first_left_factoring );
            
        end );
        
        # bⱼ·σⱼ: bⱼ·[⊕ₖ cₖ·[χᵢ⊗(χⱼ⊗χₖ)]]  ⥲  bⱼ·(χᵢ⊗(χⱼ⊗ (⊕ₖ cₖ·χₖ))) = bⱼ·(χᵢ⊗(χⱼ⊗c))
        b_sigmas := Concatenation( List( [ 1 .. b_nr_support ], j ->
            List( [ 1 .. b_components[j] ], k -> sigmas[j] ) ) );
        
        xibc := TensorProductOnObjects( product_insmat, xi, bc );
        
        # ⊕ⱼ bⱼ·σⱼ: ⊕ⱼ bⱼ·[⊕ₖ cₖ·[χᵢ⊗(χⱼ⊗χₖ)]]  ⥲  ⊕ⱼ bⱼ·[χᵢ⊗(χⱼ⊗ (⊕ₖ cₖ·χₖ))] = ⊕ⱼ bⱼ·[χᵢ⊗(χⱼ⊗c)]
        sum_b_sigmas := CoproductFunctorialWithGivenCoproducts( product_permcat,
                            ApplyFunctor( F_product_permcat, xibc ),
                            List( b_sigmas, Source ),
                            b_sigmas,
                            List( b_sigmas, Target ),
                            ApplyFunctor( F_product_permcat, xibc ) );
        
        # Error( "\033[31mDEBUGPRINT[First Coproduct]\033[0m" );
        
        return sum_b_sigmas;
        
    end );
    
    # ɑᵢ·[⊕ⱼ bⱼ·σⱼ]: ɑᵢ·[⊕ⱼ bⱼ·[⊕ₖ cₖ·[χᵢ⊗(χⱼ⊗χₖ)]]]  ⥲  ɑᵢ·[⊕ⱼ bⱼ·[χᵢ⊗(χⱼ⊗ (⊕ₖ cₖ·χₖ))]] = ɑᵢ·[⊕ⱼ bⱼ·[χᵢ⊗(χⱼ⊗c)]]
    a_inner_factors := Concatenation( List( [ 1 .. a_nr_support ], i ->
        List( [ 1 .. a_components[i] ], k -> inner_factors[i] ) ) );
    
    # ⊕ᵢ ɑᵢ·[⊕ⱼ bⱼ·σⱼ]: ⊕ᵢ ɑᵢ·[⊕ⱼ bⱼ·[⊕ₖ cₖ·[χᵢ⊗(χⱼ⊗χₖ)]]]  ⥲  ⊕ᵢ ɑᵢ·[⊕ⱼ bⱼ·[χᵢ⊗(χⱼ⊗ (⊕ₖ cₖ·χₖ))]] = ⊕ᵢ ɑᵢ·[⊕ⱼ bⱼ·[χᵢ⊗(χⱼ⊗c)]]
    outer_product := CoproductFunctorialWithGivenCoproducts( product_permcat,
                        ApplyFunctor( F_product_permcat, abc ),
                        List( a_inner_factors, Source ),
                        a_inner_factors,
                        List( a_inner_factors, Target ),
                        ApplyFunctor( F_product_permcat, abc ) );
    
    # Error( "\033[31mDEBUGPRINT[Second Coproduct]\033[0m" );
    
    return outer_product;
    
end );

# 1 ≤ i ≤ m = Support(a)
# 1 ≤ j ≤ n = Support(b)
#
# ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ χᵢ⊗(χⱼ⊗c) ] ]
#        │
#        │ ⊕ᵢ ɑᵢ·[ σ⁻¹(χᵢ, (χᵢ⊗(χ₁⊗c),...,χᵢ⊗(χ₁⊗c),...,χᵢ⊗(χₙ⊗c),...,χᵢ⊗(χₙ⊗c)) ]
#        │                  └─────────────────────┘     └─────────────────────┘
#        │                         b₁ times                    bₙ times
#        ↓
# ⊕ᵢ ɑᵢ·[ χᵢ⊗ [⊕ⱼ bⱼ·(χⱼ⊗c) ]]
#        │
#        │ ⊕ᵢ ɑᵢ·[ (1_χᵢ)⊗ σ⁻¹((χ₁⊗c,...,χ₁⊗c,...,χₙ⊗c,...,χₙ⊗c), c) ]
#        │                      └───────────┘     └───────────┘
#        │                        b₁ times          bₙ times
#        ↓
# ⊕ᵢ ɑᵢ·[ χᵢ⊗((⊕ⱼ bⱼ·χⱼ)⊗c) ]
#        ‖
# ⊕ᵢ ɑᵢ·[ χᵢ⊗(b⊗c) ]
InstallGlobalFunction( SGREPS_Associator_6_Morphism_multiplicity,
  function( product_insmat, a, b, c, abc )
    local product_permcat, F_product_permcat, a_nr_support, a_support, a_components, b_nr_support, b_support, b_components, b_xj, b_xjc, bc, sigmas, a_sigmas, sum_a_sigmas;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    product_permcat := UnderlyingProductCategoryOfPermutationCategory( product_insmat );
    F_product_permcat := IsomorphismFromCoreToProductCategoryOfPermutationCategory( product_insmat );
    
    a_nr_support := NrSupport( a );
    a_support := Support( a );
    a_components := Components( a );
    
    b_nr_support := NrSupport( b );
    b_support := Support( b );
    b_components := Components( b );
    
    # [ χ₁, χ₂, ..., χₙ ]
    b_xj := List( [ 1 .. b_nr_support ], j ->
        ObjectConstructor( product_insmat, NTuple( 3, 1, [ b_support[j] ], [ 1 ] ) ) );
    
    # [ χ₁⊗c, χ₂⊗c, ..., χₙ⊗c ]
    b_xjc := List( [ 1 .. b_nr_support ], j ->
        TensorProductOnObjects( product_insmat, b_xj[j], c ) );
    
    bc := TensorProductOnObjects( product_insmat, b, c );
    
    # σᵢ: ⊕ⱼ bⱼ·[ χᵢ⊗(χⱼ⊗c) ]  ⥲  χᵢ⊗(b⊗c)
    sigmas := List( [ 1 .. a_nr_support ], function( i )
        local xi, xibc, left_expanding, left_factoring, right_expanding, right_factoring, id_c_tensor_right_factoring;
        
        xi := ObjectConstructor( product_insmat, NTuple( 3, 1, [ a_support[i] ], [ 1 ] ) );
        
        xibc := TensorProductOnObjects( product_insmat, xi, bc );
        
        # ⊕ⱼ bⱼ·[ χᵢ⊗(χⱼ⊗c) ]  ⥲  χᵢ⊗ [⊕ⱼ bⱼ·(χⱼ⊗c) ]
        left_expanding := LeftDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_insmat, xibc, xi, b_xjc, b_components, xibc );
        left_factoring := InverseForMorphisms( product_permcat, ApplyFunctor( F_product_permcat, left_expanding ) );
        
        # ⊕ⱼ bⱼ·(χⱼ⊗c)  ⥲  (⊕ⱼ bⱼ·χⱼ)⊗c = b⊗c
        right_expanding := RightDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_insmat, bc, b_xj, c, b_components, bc );
        right_factoring := InverseForMorphisms( product_permcat, ApplyFunctor( F_product_permcat, right_expanding ) );
        
        # χᵢ⊗ [⊕ⱼ bⱼ·(χⱼ⊗c) ]  ⥲  χᵢ⊗((⊕ⱼ bⱼ·χⱼ)⊗c) = χᵢ⊗(b⊗c)
        id_c_tensor_right_factoring :=
            PRODUCT_OF_PERMUTATIONCATEGORY_AS_SUBCAT_TensorProductOfIdentityWithMorphismWithGivenTensorProducts( product_permcat,
                ApplyFunctor( F_product_permcat, xibc ),
                IdentityMorphism( product_permcat, ApplyFunctor( F_product_permcat, xi ) ),
                right_factoring,
                ApplyFunctor( F_product_permcat, xibc ) );
        
        # The composition of permutations π₂·π₁ corresponds to the permutation-matrix product P₁·P₂.
        return PreCompose( product_permcat, id_c_tensor_right_factoring, left_factoring );
        
    end );
    
    # ɑᵢ·σᵢ: ɑᵢ·[⊕ⱼ bⱼ·[ χᵢ⊗(χⱼ⊗c) ]]  ⥲  ɑᵢ·[χᵢ⊗(b⊗c)]
    a_sigmas := Concatenation( List( [ 1 .. a_nr_support ], i ->
        List( [ 1 .. a_components[i] ], j -> sigmas[i] ) ) );
    
    # ⊕ᵢ ɑᵢ·σᵢ: ɑᵢ·[⊕ⱼ bⱼ·[ χᵢ⊗(χⱼ⊗c) ]]  ⥲  ɑᵢ·[χᵢ⊗(b⊗c)]
    sum_a_sigmas := CoproductFunctorialWithGivenCoproducts( product_permcat,
                        ApplyFunctor( F_product_permcat, abc ),
                        List( a_sigmas, Source ),
                        a_sigmas,
                        List( a_sigmas, Target ),
                        ApplyFunctor( F_product_permcat, abc ) );
    
    # Error( "\033[31mDEBUGPRINT[CoproductFunctorial]\033[0m" );
    
    return sum_a_sigmas;
    
end );

# 1 ≤ i ≤ m = Support(a)
# 
# ⊕ᵢ aᵢ·[ χᵢ⊗(b⊗c) ]
#     │
#     │ σ⁻¹((χ₁⊗ (b⊗c),...,χ₁⊗(b⊗c),...,χₘ⊗(b⊗c),...,χₘ⊗(b⊗c)), (b⊗c))
#     │      └────────────────────┘     └───────────────────┘
#     │             a₁ times                   aₘ times
#     ↓
# (⊕ᵢ aᵢ·χᵢ)⊗(b⊗c)
#     ‖
#  a⊗(b⊗c)
InstallGlobalFunction( SGREPS_Associator_7_Morphism_multiplicity,
  function( product_insmat, a, b, c, abc )
    local product_permcat, F_product_permcat, a_nr_support, a_support, a_components, a_xi, bc, factoring_morphism, expanding_morphism;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    product_permcat := UnderlyingProductCategoryOfPermutationCategory( product_insmat );
    F_product_permcat := IsomorphismFromCoreToProductCategoryOfPermutationCategory( product_insmat );
    
    a_nr_support := NrSupport( a );
    a_support := Support( a );
    a_components := Components( a );
    
    # [ χ₁, χ₂, ..., χₘ ]
    a_xi := List( [ 1 .. a_nr_support ], i ->
        ObjectConstructor( product_insmat, NTuple( 3, 1, [ a_support[i] ], [ 1 ] ) ) );
    
    bc := TensorProductOnObjects( product_insmat, b, c );
    
    #⊕ᵢ aᵢ·[ χᵢ⊗(b⊗c) ] = χ₁⊗(b⊗c) ⊕...⊕ χ₁⊗(b⊗c) ⊕...⊕ χₘ⊗(b⊗c) ⊕...⊕ χₘ⊗(b⊗c)  ⥲  (χ₁ ⊕...⊕ χ₁ ⊕...⊕ χₘ ⊕...⊕ χₘ)⊗(b⊗c) = (⊕ᵢ aᵢ·χᵢ)⊗(b⊗c) = a⊗(b⊗c)
    expanding_morphism := RightDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_insmat, abc, a_xi, bc, a_components, abc );
    factoring_morphism := InverseForMorphisms( product_permcat, ApplyFunctor( F_product_permcat, expanding_morphism ) );
    
    return factoring_morphism;
    
end );

InstallGlobalFunction( SGREPS_Associator_123_Morphism_multiplicity,
  function( product_insmat, a, b, c, abc )
    local product_permcat, morphism_1, morphism_2, morphism_3, morphism_123;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    product_permcat := UnderlyingProductCategoryOfPermutationCategory( product_insmat );
    
    # (a⊗b)⊗c  ⥲  ⊕ᵢ aᵢ((χᵢ⊗b)⊗c)
    morphism_1 := SGREPS_Associator_1_Morphism_multiplicity( product_insmat, a, b, c, abc );
    
    # ⊕ᵢ ɑᵢ((χᵢ⊗b)⊗c)  ⥲  ⊕ᵢ ɑᵢ ⊕ⱼ bⱼ((χᵢ⊗χⱼ)⊗c)
    morphism_2 := SGREPS_Associator_2_Morphism_multiplicity( product_insmat, a, b, c, abc );
    
    # ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ (χᵢ⊗χⱼ)⊗c ] ]  ⥲  ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ ⊕ₖ cₖ·[ (χᵢ⊗χⱼ)⊗χₖ ] ] ]
    morphism_3 := SGREPS_Associator_3_Morphism_multiplicity( product_insmat, a, b, c, abc );
    
    # The composition of permutations π₂·π₁ corresponds to the permutation-matrix product P₁·P₂.
    morphism_123 := PreComposeList( product_permcat, [ morphism_3, morphism_2, morphism_1 ] );
    
    # The composition of permutations π₂·π₁ corresponds to the permutation-matrix product P₁·P₂.
    # morphism_123 := SGREPS_FunctorFromMorphismPermutationsToMorphismMatrices( product_insmat, abc, morphism_123, abc );
    
    return morphism_123;
    
end );

InstallGlobalFunction( SGREPS_Associator_567_Morphism_multiplicity,
  function( product_insmat, a, b, c, abc )
    local product_permcat, morphism_5, morphism_6, morphism_7, morphism_567;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    product_permcat := UnderlyingProductCategoryOfPermutationCategory( product_insmat );
    
    # ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ ⊕ₖ cₖ·[ χᵢ⊗(χⱼ⊗χₖ) ] ] ]  ⥲  ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ χᵢ⊗(χⱼ⊗c) ] ]
    morphism_5 := SGREPS_Associator_5_Morphism_multiplicity( product_insmat, a, b, c, abc );
    
    # ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·[ χᵢ⊗(χⱼ⊗c) ] ]  ⥲  ⊕ᵢ ɑᵢ·[ χᵢ⊗(b⊗c) ]
    morphism_6 := SGREPS_Associator_6_Morphism_multiplicity( product_insmat, a, b, c, abc );
    
    # ⊕ᵢ aᵢ·[ χᵢ⊗(b⊗c) ]  ⥲  a⊗(b⊗c)
    morphism_7 := SGREPS_Associator_7_Morphism_multiplicity( product_insmat, a, b, c, abc );
    
    # The composition of permutations π₂·π₁ corresponds to the permutation-matrix product P₁·P₂.
    morphism_567 := PreComposeList( product_permcat, [ morphism_7, morphism_6, morphism_5 ] );
    
    # The composition of permutations π₂·π₁ corresponds to the permutation-matrix product P₁·P₂.
    # morphism_567 := SGREPS_FunctorFromMorphismPermutationsToMorphismMatrices( product_insmat, abc, morphism_567, abc );
    
    return morphism_567;
    
end );

