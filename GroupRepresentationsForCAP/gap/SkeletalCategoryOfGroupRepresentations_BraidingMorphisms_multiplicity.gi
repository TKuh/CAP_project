# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Implementations
#

# 1 ≤ i ≤ m = Support(a)
#
#    a⊗b
#     │
#     │ σ((χ₁,...,χ₁,...,χₘ,...,χₘ), b)
#     │    └───────┘     └───────┘
#     │    a₁ times      aₘ times
#     ↓
# ⊕ᵢ aᵢ·(χᵢ⊗b)
InstallGlobalFunction( SGREPS_Braiding_1_Morphism_multiplicity,
  function( product_insmat, a, b, ab )
    local a_nr_support, a_support, a_components, a_xi;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    a_nr_support := NrSupport( a );
    a_support := Support( a );
    a_components := Components( a );
    
    # [ χ₁, χ₂, ..., χₘ ]
    a_xi := List( [ 1 .. a_nr_support ], i ->
        ObjectConstructor( product_insmat, NTuple( 3, 1, [ a_support[i] ], [ 1 ] ) ) );
    
    return RightDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_insmat, ab, a_xi, b, Components( a ), ab );
    
end );

# 1 ≤ i ≤ m = Support(a)
# 1 ≤ j ≤ n = Support(b)
#
#   ⊕ᵢ ɑᵢ·(χᵢ⊗b)
#        │
#        │ ⊕ᵢ ɑᵢ·[ σ(χᵢ, (χ₁,...,χ₁,...,χₙ,...,χₙ)) ]
#        │                └───────┘     └───────┘
#        │                b₁ times      bₙ times
#        ↓
# ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·(χᵢ⊗χⱼ) ]
InstallGlobalFunction( SGREPS_Braiding_2_Morphism_multiplicity,
  function( product_insmat, a, b, ab )
    local a_nr_support, a_support, a_components, b_nr_support, b_support, b_components, b_xj, sigmas, a_sigmas;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    a_nr_support := NrSupport( a );
    a_support := Support( a );
    a_components := Components( a );
    
    b_nr_support := NrSupport( b );
    b_support := Support( b );
    b_components := Components( b );
    
    # [ χ₁, χ₂, ..., χₙ ]
    b_xj := List( [ 1 .. b_nr_support ], j ->
        ObjectConstructor( product_insmat, NTuple( 3, 1, [ b_support[j] ], [ 1 ] ) ) );
    
    
    sigmas := List( [ 1 .. a_nr_support ], function( i )
        local xi, xib;
        
        xi := ObjectConstructor( product_insmat, NTuple( 3, 1, [ a_support[i] ], [ 1 ] ) );
        
        xib := TensorProductOnObjects( product_insmat, xi, b );
        
        return LeftDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_insmat, xib, xi, b_xj, b_components, xib );
        
    end );
    
    # The list of aᵢ-many duplications of σᵢ.
    a_sigmas := Concatenation( List( [ 1 .. a_nr_support ], i ->
        List( [ 1 .. a_components[i] ], j -> sigmas[i] ) ) );
    
    return DirectProductFunctorialWithGivenDirectProducts( product_insmat,
                ab,
                List( a_sigmas, Source ),
                a_sigmas,
                List( a_sigmas, Target ),
                ab );
    
end );

# 1 ≤ i ≤ m = Support(a)
# 1 ≤ j ≤ n = Support(b)
#
# ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·(χᵢ⊗χⱼ) ]
#        │
#        │ ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·ɣ(χᵢ,χⱼ) ]
#        ↓
# ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·(χⱼ⊗χᵢ) ]
InstallGlobalFunction( SGREPS_Braiding_3_Morphism_multiplicity,
  function( sgreps, a, b, ab )
    local a_nr_support, a_support, a_components, b_nr_support, b_support, b_components, b_gammas, ab_gammas;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    a_nr_support := NrSupport( a );
    a_support := Support( a );
    a_components := Components( a );
    
    b_nr_support := NrSupport( b );
    b_support := Support( b );
    b_components := Components( b );
    
    b_gammas := List( [ 1 .. a_nr_support ], function( i )
        local xi, gamma_ij, b_gamma_ij;
        
        xi := ObjectConstructor( sgreps, NTuple( 3, 1, [ a_support[i] ], [ 1 ] ) );
        
        gamma_ij := List( [ 1 .. b_nr_support ], function( j )
            local xj;
            
            xj := ObjectConstructor( sgreps, NTuple( 3, 1, [ b_support[j] ], [ 1 ] ) );
            
            # TODO:
            # return SGREPS_BraidingOnIrreduciblesWithGivenTensorProducts
            return SGREPS_BraidingOnIrreducibles_new( sgreps, xi, xj );
            
        end );
        
        # The list of bⱼ-many duplications of ɣᵢⱼ.
        b_gamma_ij := Concatenation( List( [ 1 .. b_nr_support ], j ->
            List( [ 1 .. b_components[j] ], k -> gamma_ij[j] ) ) );
        
        return DirectSumFunctorial( sgreps, b_gamma_ij );

    end );
    
    # The list of aᵢ-many duplications of [⊕ⱼ bⱼ·ɣᵢⱼ].
    ab_gammas := Concatenation( List( [ 1 .. a_nr_support ], i ->
        List( [ 1 .. a_components[i] ], j -> b_gammas[i] ) ) );
    
    return DirectSumFunctorialWithGivenDirectSums( sgreps,
                ab,
                List( ab_gammas, Source ),
                ab_gammas,
                List( ab_gammas, Target ),
                ab );
    
end );

# 1 ≤ i ≤ m = Support(a)
# 1 ≤ j ≤ n = Support(b)
#
# ⊕ᵢ ɑᵢ·[ ⊕ⱼ bⱼ·(χⱼ⊗χᵢ) ]
#        │
#        │ ⊕ᵢ ɑᵢ·[ σ⁻¹((χ₁,...,χ₁,...,χₙ,...,χₙ), χᵢ) ]
#        │              └───────┘     └───────┘
#        │              b₁ times      bₙ times
#        ↓
# ⊕ᵢ ɑᵢ·(b⊗χᵢ)
InstallGlobalFunction( SGREPS_Braiding_4_Morphism_multiplicity,
  function( product_insmat, a, b, ab )
    local product_permcat, F_product_permcat, a_nr_support, a_support, a_components, b_nr_support, b_support, b_components, b_xj, sigmas, a_sigmas;
    
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
    
    sigmas := List( [ 1 .. a_nr_support ], function( i )
        local xi, bxi, right_expanding;
        
        xi := ObjectConstructor( product_insmat, NTuple( 3, 1, [ a_support[i] ], [ 1 ] ) );
        bxi := TensorProductOnObjects( product_insmat, b, xi );
        
        right_expanding := RightDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_insmat,
                                bxi,
                                b_xj,
                                xi,
                                b_components,
                                bxi );
        
        return InverseForMorphisms( product_permcat, ApplyFunctor( F_product_permcat, right_expanding ) );
        
    end );
    
    # The list of aᵢ-many duplications of σᵢ.
    a_sigmas := Concatenation( List( [ 1 .. a_nr_support ], i ->
        List( [ 1 .. a_components[i] ], j -> sigmas[i] ) ) );
    
    return CoproductFunctorialWithGivenCoproducts( product_permcat,
                ApplyFunctor( F_product_permcat, ab ),
                List( a_sigmas, Source ),
                a_sigmas,
                List( a_sigmas, Target ),
                ApplyFunctor( F_product_permcat, ab ) );
    
end );

# 1 ≤ i ≤ m = Support(a)
#
# ⊕ᵢ ɑᵢ·(b⊗χᵢ)
#      │
#      │ σ⁻¹(b, (χ₁,...,χ₁,...,χₘ,...,χₘ))
#      │         └───────┘     └───────┘
#      │         a₁ times      aₘ times
#      ↓
# b⊗(⊕ᵢ ɑᵢ·χᵢ)
#      ‖
#     b⊗a
InstallGlobalFunction( SGREPS_Braiding_5_Morphism_multiplicity,
  function( product_insmat, a, b, ab )
    local product_permcat, F_product_permcat, a_nr_support, a_support, a_components, a_xi, left_expanding;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    product_permcat := UnderlyingProductCategoryOfPermutationCategory( product_insmat );
    F_product_permcat := IsomorphismFromCoreToProductCategoryOfPermutationCategory( product_insmat );
    
    a_nr_support := NrSupport( a );
    a_support := Support( a );
    a_components := Components( a );
    
    # [ χ₁, χ₂, ..., χₘ ]
    a_xi := List( [ 1 .. a_nr_support ], i ->
        ObjectConstructor( product_insmat, NTuple( 3, 1, [ a_support[i] ], [ 1 ] ) ) );
    
    left_expanding := LeftDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_insmat,
                            ab,
                            b,
                            a_xi,
                            a_components,
                            ab );
    
    return InverseForMorphisms( product_permcat, ApplyFunctor( F_product_permcat, left_expanding ) );
    
end );

InstallGlobalFunction( SGREPS_Braiding_12_Morphism_multiplicity,
  function( product_insmat, a, b, ab )
    local product_permcat, F_product_permcat, morphism_1, morphism_2, morphism_12;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    product_permcat := UnderlyingProductCategoryOfPermutationCategory( product_insmat );
    F_product_permcat := IsomorphismFromCoreToProductCategoryOfPermutationCategory( product_insmat );
    
    morphism_1 := SGREPS_Braiding_1_Morphism_multiplicity( product_insmat, a, b, ab );
    
    morphism_2 := SGREPS_Braiding_2_Morphism_multiplicity( product_insmat, a, b, ab );
    
    # The composition of permutations π₂·π₁ corresponds to the permutation-matrix product P₁·P₂.
    morphism_12 := PreCompose( product_permcat,
                               ApplyFunctor( F_product_permcat, morphism_2 ),
                               ApplyFunctor( F_product_permcat, morphism_1 ) );
    
    # return SGREPS_FunctorFromMorphismPermutationsToMorphismMatrices( product_insmat, ab, morphism_12, ab );
    return morphism_12;
    
end );

InstallGlobalFunction( SGREPS_Braiding_45_Morphism_multiplicity,
  function( product_insmat, a, b, ba )
    local product_permcat, F_product_permcat, morphism_4, morphism_5, morphism_45;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    product_permcat := UnderlyingProductCategoryOfPermutationCategory( product_insmat );
    F_product_permcat := IsomorphismFromCoreToProductCategoryOfPermutationCategory( product_insmat );
    
    morphism_4 := SGREPS_Braiding_4_Morphism_multiplicity( product_insmat, a, b, ba );
    
    morphism_5 := SGREPS_Braiding_5_Morphism_multiplicity( product_insmat, a, b, ba );
    
    # The composition of permutations π₂·π₁ corresponds to the permutation-matrix product P₁·P₂.
    morphism_45 := PreCompose( product_permcat, morphism_5, morphism_4 );
    
    # return SGREPS_FunctorFromMorphismPermutationsToMorphismMatrices( product_insmat, ba, morphism_45, ba );
    return morphism_45;
    
end );

# TODO: SGREPS_BraidingOnIrreduciblesWithGivenTensorProducts
InstallGlobalFunction( SGREPS_BraidingOnIrreducibles_new,
  function( sgreps, xi, xj )
    local xixj, unit, DS, Rows, splitting_field, xixj_nr_support, xixj_support, xixj_components, exterior_power, components;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    xixj := TensorProductOnObjects( sgreps, xi, xj );
    
    unit := TensorUnit( sgreps );
    
    if IsEqualForObjects( sgreps, unit, xi ) or
       IsEqualForObjects( sgreps, unit, xj ) then
        
        return IdentityMorphism( sgreps, xixj );
        
    elif not IsEqualForObjects( sgreps, xi, xj ) then
        
        # Case xᵢ ≠ xⱼ: Sebastian's PhD. thesis construction I.3.42.
        
        # ɣ(xᵢ,xⱼ) = id
        return IdentityMorphism( sgreps, xixj );
        
    else
        
        # Case xᵢ = xⱼ: Sebastian's PhD. thesis Theorem I.3.44.
        
        DS := ModelingCategory( sgreps );
        Rows := UnderlyingAdditiveCategory( DS );
        
        splitting_field := UnderlyingSplittingField( sgreps );
        
        xixj_nr_support := NrSupport( xixj );
        xixj_support := Support( xixj );
        xixj_components := Components( xixj );
        
        exterior_power := SecondExteriorPowerOfSimpleObject( sgreps, xi );
        
        components := List( [ 1 .. xixj_nr_support ], function( i )
            local nr_minus_1, nr_1, diagonal;
            
            nr_minus_1 := Component( exterior_power, xixj_support[i] );
            
            nr_1 := xixj_components[i] - nr_minus_1;
            
            diagonal := Concatenation( List( [ 1 .. nr_1 ], i -> 1 ), List( [ 1 .. nr_minus_1 ], i -> -1 ) );
            
            return HomalgDiagonalMatrix( diagonal, splitting_field );
            
        end );
        
        return MorphismConstructor( sgreps, xixj, NTuple( 3, xixj_nr_support, xixj_support, components ), xixj );
        
    fi;
    
end );

