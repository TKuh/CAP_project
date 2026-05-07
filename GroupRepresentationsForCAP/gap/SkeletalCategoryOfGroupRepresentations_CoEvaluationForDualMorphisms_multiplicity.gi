# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Implementations
#

# Sebastian's PhD. thesis Lemma I.3.54 and Construction I.3.55.
# Note: there are typos with the duals, they have to be swapped.
# 
# 1 ≤ i ≤ m = Support(a)
# 1 ≤ j ≤ m = Support(a)
# 
# 1·χᵤ → a⊗aᵛ = (⨁ᵢ aᵢχᵢ)⊗(⨁ⱼ aⱼχⱼ)ᵛ
# 
# 
# Since the unit is 1 = 1·χᵤ in SGReps, we only
# need to care about the matrix at the support
# of the trivial character.
# All other matrices will be a 0x? matrix.
# 
# In the first morphism box, Rows( Diag(...) ) translates
# categorically into UniversalMorphismIntoDirectSum(...)
# where one needs to keep track of the zeros which the Diag
# introduces. Our code does this implicitly by using
# the coevaluations for duals in the category of rows.
InstallGlobalFunction( SGREPS_CoevaluationForDual_1_Morphism_multiplicity,
  function( SGReps, unit, a, aav )
    local DS, Rows, unit_support, unit_character_nr, unit_rows, a_nr_support, a_support, a_components, aav_nr_support, aav_support, aav_components, diagonal, coevaluations, aav_support_unit_position, diagonal_sum, morphism_unit, morphisms, matrices, morphism;
    
    #% TODO CAP_JIT_RESOLVE_FUNCTION
    
    DS := ModelingCategory( SGReps );
    Rows := UnderlyingAdditiveCategory( DS );
    
    unit_support := Support( unit );
    unit_character_nr := unit_support[1];
    
    unit_rows := TensorUnit( Rows );
    
    # a = (⨁ᵢ aᵢχᵢ)
    a_nr_support := NrSupport( a );
    a_support := Support( a );
    a_components := List( [ 1 .. a_nr_support ], i ->
        ObjectConstructor( Rows, Components( a )[i] ) );
        
    # a⊗aᵛ = (⨁ᵢ aᵢχᵢ)⊗(⨁ⱼ aⱼχⱼ)ᵛ
    aav_nr_support := NrSupport( aav );
    aav_support := Support( aav );
    aav_components := List( [ 1 .. aav_nr_support ], i ->
        ObjectConstructor( Rows, Components( aav )[i] ) );
        
    # [ a₁⊗a₁ᵛ, ..., aₘ⊗aₘᵛ ]
    diagonal := List( [ 1 .. a_nr_support ], i ->
        TensorProductOnObjects( Rows, a_components[i], DualOnObjects( Rows, a_components[i] ) ) );
        
    # coev_aᵢ: 1 → aᵢ⊗aᵢᵛ = aᵢ·aᵢ
    coevaluations := List( [ 1 .. a_nr_support ], i ->
        CoevaluationForDualWithGivenTensorProduct( Rows, unit_rows, a_components[i], diagonal[i] ) );
        
    # The sum (⨁ᵢ aᵢ⊗aᵢᵛ) = (𝚺ᵢ aᵢ·aᵢ) is the coefficient of the trivial character χᵤ in a⊗aᵛ:
    # 
    # ⟨a⊗aᵛ,χᵤ⟩ = ⟨⨁ᵢ⨁ⱼ aᵢχᵢ⊗aⱼχⱼᵛ,χᵤ⟩
    #           = 𝚺ᵢ𝚺ⱼ aᵢ·aⱼ·⟨χᵢ⊗χⱼᵛ,χᵤ⟩
    #           = 𝚺ᵢ𝚺ⱼ aᵢ·aⱼ·⟨χᵢ,χⱼ⟩
    #           = 𝚺ᵢ aᵢ·aᵢ
    aav_support_unit_position := SafeUniquePosition( aav_support, unit_character_nr );
    diagonal_sum := aav_components[ aav_support_unit_position ];
    
    #                  1
    #                 ╱⏐╲
    #                ╱ ⏐ ╲
    #               ╱  ⏐  ╲
    #              ╱   ⏐   ╲
    #         coev_a₁ ... coev_aₘ
    #            ╱     ⏐     ╲
    #           ╱      ⏐      ╲
    #          ╱       ⏐       ╲
    #         ↓        ↓        ↓
    #       a₁⊗a₁ᵛ    ...     aₘ⊗aₘᵛ
    #         ‖        ‖        ‖
    #       a₁·a₁     ...     aₘ·aₘ
    # 
    morphism_unit := UniversalMorphismIntoDirectSumWithGivenDirectSum( Rows,
                            diagonal,
                            unit_rows,
                            coevaluations,
                            diagonal_sum );
                            
    # Construct zero morphisms for all supported components of a⊗aᵛ.
    morphisms := List( [ 1 .. aav_nr_support ], i ->
        ZeroMorphism( Rows, ZeroObject( Rows ), aav_components[i] ) );
        
    # Replace the zero morphism at component χᵤ.
    # χᵤ is guaranteed to exist in a⊗aᵛ (see the above computation).
    morphisms[ aav_support_unit_position ] := morphism_unit;
    
    matrices := List( [ 1 .. aav_nr_support ], i -> UnderlyingMatrix( morphisms[i] ) );
    
    morphism := MorphismConstructor( SGReps,
                                     unit,
                                     NTuple( 3, aav_nr_support, aav_support, matrices ),
                                     aav );
                                     
    return morphism;
    
end );

# 1 ≤ i ≤ m = Support(a)
#
# ⊕ᵢ ɑᵢ·[ ⊕ⱼ aⱼ·(χᵢ⊗χⱼᵛ) ]
#        │
#        │ ⊕ᵢ ɑᵢ·[ σ⁻¹(χᵢ, (χ₁ᵛ,...,χ₁ᵛ,...,χₘᵛ,...,χₘᵛ)) ]
#        │                  └─────────┘     └─────────┘
#        │                   a₁ times        aₘ times
#        ↓
#   ⊕ᵢ ɑᵢ·(χᵢ⊗aᵛ)
InstallGlobalFunction( SGREPS_CoevaluationForDual_2_Morphism_multiplicity,
  function( product_kron_comon, a, av, aav )
    local product_permcat, F_product_permcat, a_nr_support, a_support, a_components, av_nr_support, av_support, av_components, av_xi, sigmas, a_sigmas;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    product_permcat := UnderlyingProductCategoryOfPermutationCategory( product_kron_comon );
    F_product_permcat := IsomorphismFromCoreToProductCategoryOfPermutationCategory( product_kron_comon );
    
    a_nr_support := NrSupport( a );
    a_support := Support( a );
    a_components := Components( a );
    
    av_nr_support := NrSupport( av );
    av_support := Support( av );
    av_components := Components( av );
    
    # [ χ₁ᵛ, χ₂ᵛ, ..., χₙᵛ ]
    av_xi := List( [ 1 .. av_nr_support ], i ->
        ObjectConstructor( product_kron_comon, NTuple( 3, 1, [ av_support[i] ], [ 1 ] ) ) );
    
    sigmas := List( [ 1 .. a_nr_support ], function( i )
        local xi, xiav, left_expanding;
        
        xi := ObjectConstructor( product_kron_comon, NTuple( 3, 1, [ a_support[i] ], [ 1 ] ) );
        xiav := TensorProductOnObjects( product_kron_comon, xi, av );
        
        left_expanding := LeftDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_kron_comon, xiav, xi, av_xi, av_components, xiav );
        
        return InverseForMorphisms( product_permcat, ApplyFunctor( F_product_permcat, left_expanding ) );
        
    end );
    
    # The list of aᵢ-many duplications of σᵢ.
    a_sigmas := Concatenation( List( [ 1 .. a_nr_support ], i ->
        List( [ 1 .. a_components[i] ], j -> sigmas[i] ) ) );
    
    return CoproductFunctorialWithGivenCoproducts( product_permcat,
                ApplyFunctor( F_product_permcat, aav ),
                List( a_sigmas, Source ),
                a_sigmas,
                List( a_sigmas, Target ),
                ApplyFunctor( F_product_permcat, aav ) );
    
end );

# 1 ≤ i ≤ m = Support(a)
#
# ⊕ᵢ ɑᵢ·(χᵢ⊗aᵛ)
#     │
#     │ σ⁻¹((χ₁,...,χ₁,...,χₘ,...,χₘ), aᵛ)
#     │      └───────┘     └───────┘
#     │      a₁ times      aₘ times
#     ↓
# (⊕ᵢ ɑᵢ·χᵢ)⊗aᵛ
#     ‖
#    a⊗aᵛ
InstallGlobalFunction( SGREPS_CoevaluationForDual_3_Morphism_multiplicity,
  function( product_kron_comon, a, av, aav )
    local product_permcat, F_product_permcat, a_nr_support, a_support, a_components, a_xi, right_expanding;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    product_permcat := UnderlyingProductCategoryOfPermutationCategory( product_kron_comon );
    F_product_permcat := IsomorphismFromCoreToProductCategoryOfPermutationCategory( product_kron_comon );
    
    a_nr_support := NrSupport( a );
    a_support := Support( a );
    a_components := Components( a );
    
    # [ χ₁, χ₂, ..., χₙ ]
    a_xi := List( [ 1 .. a_nr_support ], i ->
        ObjectConstructor( product_kron_comon, NTuple( 3, 1, [ a_support[i] ], [ 1 ] ) ) );
    
    right_expanding := RightDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_kron_comon,
                            aav,
                            a_xi,
                            av,
                            a_components,
                            aav );
    
    return InverseForMorphisms( product_permcat, ApplyFunctor( F_product_permcat, right_expanding ) );
    
end );

InstallGlobalFunction( SGREPS_CoevaluationForDual_23_Morphism_multiplicity,
  function( product_kron_comon, a, av, aav )
    local product_permcat, morphism_2, morphism_3, morphism_23;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    product_permcat := UnderlyingProductCategoryOfPermutationCategory( product_kron_comon );
    
    morphism_2 := SGREPS_CoevaluationForDual_2_Morphism_multiplicity( product_kron_comon, a, av, aav );
    
    morphism_3 := SGREPS_CoevaluationForDual_3_Morphism_multiplicity( product_kron_comon, a, av, aav );
    
    morphism_23 := PreCompose( product_permcat, morphism_3, morphism_2 );
    
    return morphism_23;
    
end );

# 1 ≤ i ≤ m = Support(a)
#
#    aᵛ⊗a
#      ‖
# aᵛ⊗(⊕ᵢ ɑᵢ·χᵢ)
#      │
#      │ σ(aᵛ, (χ₁,...,χ₁,...,χₘ,...,χₘ))
#      │        └───────┘     └───────┘
#      │        a₁ times      aₘ times
#      ↓
# ⊕ᵢ ɑᵢ·(aᵛ⊗χᵢ)
InstallGlobalFunction( SGREPS_EvaluationForDual_1_Morphism_multiplicity,
  function( product_kron_comon, ava, av, a )
    local product_permcat, F_product_permcat, a_nr_support, a_support, a_components, a_xi, left_expanding;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    product_permcat := UnderlyingProductCategoryOfPermutationCategory( product_kron_comon );
    F_product_permcat := IsomorphismFromCoreToProductCategoryOfPermutationCategory( product_kron_comon );
    
    a_nr_support := NrSupport( a );
    a_support := Support( a );
    a_components := Components( a );
    
    # [ χ₁, χ₂, ..., χₙ ]
    a_xi := List( [ 1 .. a_nr_support ], i ->
        ObjectConstructor( product_kron_comon, NTuple( 3, 1, [ a_support[i] ], [ 1 ] ) ) );
    
    left_expanding := LeftDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_kron_comon,
                            ava,
                            av,
                            a_xi,
                            a_components,
                            ava );
    
    return ApplyFunctor( F_product_permcat, left_expanding );
    
end );

# 1 ≤ i ≤ m = Support(a)
#
# (⊕ᵢ ɑᵢ·(aᵛ⊗χᵢ))
#        │
#        │ ⊕ᵢ ɑᵢ·[ σ((χ₁ᵛ,...,χ₁ᵛ,...,χₘᵛ,...,χₘᵛ), χᵢ) ]
#        │            └─────────┘     └─────────┘
#        │             a₁ times        aₘ times
#        ↓
# ⊕ᵢ ɑᵢ·[ ⊕ⱼ aⱼ·(χᵢᵛ⊗χⱼ) ]
InstallGlobalFunction( SGREPS_EvaluationForDual_2_Morphism_multiplicity,
  function( product_kron_comon, ava, av, a )
    local product_permcat, F_product_permcat, a_nr_support, a_support, a_components, av_nr_support, av_support, av_components, av_xi, sigmas, a_sigmas, direct_product;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    product_permcat := UnderlyingProductCategoryOfPermutationCategory( product_kron_comon );
    F_product_permcat := IsomorphismFromCoreToProductCategoryOfPermutationCategory( product_kron_comon );
    
    a_nr_support := NrSupport( a );
    a_support := Support( a );
    a_components := Components( a );
    
    av_nr_support := NrSupport( av );
    av_support := Support( av );
    av_components := Components( av );
    
    # [ χ₁ᵛ, χ₂ᵛ, ..., χₙᵛ ]
    av_xi := List( [ 1 .. av_nr_support ], i ->
        ObjectConstructor( product_kron_comon, NTuple( 3, 1, [ av_support[i] ], [ 1 ] ) ) );
    
    sigmas := List( [ 1 .. a_nr_support ], function( i )
        local xi, avxi;
        
        xi := ObjectConstructor( product_kron_comon, NTuple( 3, 1, [ a_support[i] ], [ 1 ] ) );
        avxi := TensorProductOnObjects( product_kron_comon, av, xi );
        
        return RightDistributivityExpandingWithGivenMultiplicitiesAndObjects( product_kron_comon,
                    avxi,
                    av_xi,
                    xi,
                    av_components,
                    avxi );
        
    end );
    
    # The list of aᵢ-many duplications of σᵢ.
    a_sigmas := Concatenation( List( [ 1 .. a_nr_support ], i ->
        List( [ 1 .. a_components[i] ], j -> sigmas[i] ) ) );
    
    direct_product := DirectProductFunctorialWithGivenDirectProducts( product_kron_comon,
                            ava,
                            List( a_sigmas, Source ),
                            a_sigmas,
                            List( a_sigmas, Target ),
                            ava );
    
    return ApplyFunctor( F_product_permcat, direct_product );
    
end );

# Sebastian's PhD. thesis Construction I.3.53.
# Note: there are typos with the duals, they have to be swapped.
InstallGlobalFunction( SGREPS_ExtractScalarForEvaluationFromCoevaluation,
  function( sgreps, a )
    local id_a, av, index_of_trivial_character, naive_morphism, L, automorphism, morphism;
    
    id_a := IdentityMorphism( a );
    
    av := DualOnObjects( sgreps, a );
    index_of_trivial_character := SGREPS_IndexOfTrivialCharacter( sgreps );
    
    # n: aᵛ⊗a → (aᵛ⊗a)ᵤ = 1
    naive_morphism :=
      ComponentProjectionMorphism( sgreps,
          TensorProductOnObjects( sgreps, av, a ),
          index_of_trivial_character );
    
    # TODO: use WithGiven versions
    
    # α: a → 1⊗a → (a⊗aᵛ)⊗a → a⊗(aᵛ⊗a) → a⊗(aᵛ⊗a)ᵤ = a⊗1 → a
    L := [ LeftUnitorInverse( sgreps, a ),
           TensorProductOnMorphisms( sgreps, CoevaluationForDual( sgreps, a ), id_a ),
           AssociatorLeftToRight( sgreps, a, av, a ),
           TensorProductOnMorphisms( sgreps, id_a, naive_morphism ),
           RightUnitor( sgreps, a ) ];
    
    automorphism := PreComposeList( sgreps, a, L, a );
    
    # (id_aᵛ⊗α)·n: aᵛ⊗a → 1
    morphism :=
        PreCompose( sgreps,
            TensorProductOnMorphisms( sgreps,
                IdentityMorphism( sgreps, av ),
                InverseForMorphisms( sgreps, automorphism ) ),
            naive_morphism );
    
    # (id_aᵛ⊗α · n)ᵤ
    morphism := Component( morphism, index_of_trivial_character );
    
    # `morphism` is only supported at χᵤ with a 1x1 matrix.
    return UnderlyingMatrix( Components( morphism )[1] )[1][1];
    
end );

# Sebastian's PhD. thesis Lemma I.3.54 and Construction I.3.55.
# Note: there are typos with the duals, they have to be swapped.
# 
# 1 ≤ i ≤ m = Support(a)
# 1 ≤ j ≤ m = Support(a)
# 
# ⊕ᵢ ɑᵢ·[ ⊕ⱼ aⱼ·(χᵢᵛ⊗χⱼ) ] → 1·χᵤ
# 
# 
# Since the unit is 1 = 1·χᵤ in SGReps, we only
# need to care about the matrix at the support
# of the trivial character.
# All other matrices will be of dimensions 0x?.
# 
# In the first morphism box, Cols( Diag(...) ) translates
# categorically into UniversalMorphismFromDirectSum(...)
# where one needs to keep track of the zeros which the Diag
# introduces. Our code does this implicitly by using
# the evaluations for duals in the category of rows.
InstallGlobalFunction( SGREPS_EvaluationForDual_3_Morphism_multiplicity,
  function( SGReps, ava, a, unit )
    local DS, Rows, unit_support, unit_character_nr, unit_rows, a_nr_support, a_support, a_components, ava_nr_support, ava_support, ava_components, diagonal, evaluation_scalar, evaluations, ava_support_unit_position, diagonal_sum, morphism_unit, morphisms, matrices, morphism;
    
    #% TODO CAP_JIT_RESOLVE_FUNCTION
    
    DS := ModelingCategory( SGReps );
    Rows := UnderlyingAdditiveCategory( DS );
    
    unit_support := Support( unit );
    unit_character_nr := unit_support[1];
    
    unit_rows := TensorUnit( Rows );
    
    # a = (⨁ᵢ aᵢχᵢ)
    a_nr_support := NrSupport( a );
    a_support := Support( a );
    a_components := List( [ 1 .. a_nr_support ], i ->
        ObjectConstructor( Rows, Components( a )[i] ) );
    
    # aᵛ⊗a = (⨁ᵢ aᵢχᵢ)ᵛ⊗(⨁ⱼ aⱼχⱼ)
    ava_nr_support := NrSupport( ava );
    ava_support := Support( ava );
    ava_components := List( [ 1 .. ava_nr_support ], i ->
        ObjectConstructor( Rows, Components( ava )[i] ) );
    
    # [ a₁ᵛ⊗a₁, ..., aₘᵛ⊗aₘ ]
    diagonal := List( [ 1 .. a_nr_support ], i ->
        TensorProductOnObjects( Rows, DualOnObjects( Rows, a_components[i] ), a_components[i] ) );
    
    evaluation_scalar := SGREPS_ExtractScalarForEvaluationFromCoevaluation( a );
    
    # ev_aᵢ: aᵢ·aᵢ = aᵢ⊗aᵢᵛ → 1
    evaluations := List( [ 1 .. a_nr_support ], i ->
        MultiplyWithElementOfCommutativeSemiringForMorphisms(
            evaluation_scalar,
            EvaluationForDualWithGivenTensorProduct( Rows, diagonal[i], a_components[i], unit_rows ) ) );
    
    # The sum (⨁ᵢ aᵢᵛ⊗aᵢ) = (𝚺ᵢ aᵢ·aᵢ) is the coefficient of the trivial character χᵤ in aᵛ⊗a:
    # 
    # ⟨aᵛ⊗a,χᵤ⟩ = ⟨⨁ᵢ⨁ⱼ aᵢχᵢᵛ⊗aⱼχⱼ,χᵤ⟩
    #           = 𝚺ᵢ𝚺ⱼ aᵢ·aⱼ·⟨χᵢᵛ⊗χⱼ,χᵤ⟩
    #           = 𝚺ᵢ𝚺ⱼ aᵢ·aⱼ·⟨χᵢ,χⱼ⟩
    #           = 𝚺ᵢ aᵢ·aᵢ
    ava_support_unit_position := SafeUniquePosition( ava_support, unit_character_nr );
    diagonal_sum := ava_components[ ava_support_unit_position ];
    
    #                  1
    #                 ↗↑↖
    #                ╱ ⏐ ╲
    #               ╱  ⏐  ╲
    #              ╱   ⏐   ╲
    #           ev_a₁ ... ev_aₘ
    #            ╱     ⏐     ╲
    #           ╱      ⏐      ╲
    #          ╱       ⏐       ╲
    #      a₁ᵛ⊗a₁     ...    aₘᵛ⊗aₘ
    #         ‖        ‖        ‖
    #       a₁·a₁     ...     aₘ·aₘ
    # 
    morphism_unit := UniversalMorphismFromDirectSumWithGivenDirectSum( Rows,
                            diagonal,
                            unit_rows,
                            evaluations,
                            diagonal_sum );
    
    # Construct zero morphisms for all supported components of aᵛ⊗a.
    morphisms := List( [ 1 .. ava_nr_support ], i ->
        ZeroMorphism( Rows, ava_components[i], ZeroObject( Rows ) ) );
    
    # Replace the zero morphism at component χᵤ.
    # χᵤ is guaranteed to exist in a⊗aᵛ (see the above computation).
    morphisms[ ava_support_unit_position ] := morphism_unit;
    
    matrices := List( [ 1 .. ava_nr_support ], i -> UnderlyingMatrix( morphisms[i] ) );
    
    morphism := MorphismConstructor( SGReps,
                                     ava,
                                     NTuple( 3, ava_nr_support, ava_support, matrices ),
                                     unit );
    
    return morphism;
    
end );

InstallGlobalFunction( SGREPS_EvaluationForDual_12_Morphism_multiplicity,
  function( product_kron_comon, ava, av, a )
    local product_permcat, morphism_1, morphism_2, morphism_12;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    product_permcat := UnderlyingProductCategoryOfPermutationCategory( product_kron_comon );
    
    morphism_1 := SGREPS_EvaluationForDual_1_Morphism_multiplicity( product_kron_comon, ava, av, a );
    
    morphism_2 := SGREPS_EvaluationForDual_2_Morphism_multiplicity( product_kron_comon, ava, av, a );
    
    morphism_12 := PreCompose( product_permcat, morphism_2, morphism_1 );
    
    return morphism_12;
    
end );

