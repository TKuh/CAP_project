#! @Chapter Examples and tests

#! @Section Tests

#! @Example

#! #@if String({}->1-[1-1]) = "function (  ) return 1 - [ (1 - 1) ]; end"

LoadPackage( "GroupRepresentationsForCAP", false );
#! true

# ReadPackageOnce( "GroupRepresentationsForCAP",
#     "gap/SkeletalCategoryOfGroupRepresentations_CompilerLogic.gi" );
# true

CapJitAddTypeSignature( "Union", [ IsList ], function ( input_types )
    
    # TODO: checks?
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

QQ := HomalgFieldOfRationalsInSingular( );;

precompile_SkeletalCategoryOfGroupRepresentations := function( group, homalg_field, name )
    
    CapJitPrecompileCategoryAndCompareResult(
        { group, homalg_field } ->
            SkeletalCategoryOfGroupRepresentations(
                group,
                homalg_field
                : no_precompiled_code := true,
                  product_pwp_no_precompiled_code := false,
                  pwp_no_precompiled_code := false ),
        [ group, homalg_field ],
        "GroupRepresentationsForCAP",
        Concatenation(
            "SkeletalCategoryOfGroupRepresentations_",
            name,
            "_precompiled"
        ) :
        # operations := "primitive",
        # operations := [ "TensorUnit" ],
        operations := [ # "IsEqualForObjects",
                        # "IsEqualForMorphisms",
                        # "IsCongruentForMorphisms",
                        # "IsWellDefinedForObjects",
                        # "IsWellDefinedForMorphisms",
                        # "ObjectConstructor",
                        # "MorphismConstructor",
                        # "ObjectDatum",
                        # "MorphismDatum",
                        # "IdentityMorphism",
                        # "PreCompose",
                        # "ZeroMorphism",
                        # "IsZeroForMorphisms",
                        # "AdditionForMorphisms",
                        # "SumOfMorphisms",
                        # "AdditiveInverseForMorphisms",
                        # "SubtractionForMorphisms",
                        # "ZeroObject",
                        # "MultiplyWithElementOfCommutativeRingForMorphisms",
                        # "DirectSum",
                        # "DirectSumFunctorial",
                        # "DirectSumFunctorialWithGivenDirectSums",
                        # "ProjectionInFactorOfDirectSumWithGivenDirectSum",
                        # "InjectionOfCofactorOfDirectSumWithGivenDirectSum",
                        # "UniversalMorphismIntoDirectSumWithGivenDirectSum",
                        # "UniversalMorphismFromDirectSumWithGivenDirectSum",
                        # "KernelObject",
                        # "KernelEmbeddingWithGivenKernelObject",
                        # "Lift",
                        # "CokernelObject",
                        # "CokernelProjectionWithGivenCokernelObject",
                        # "Colift",
                        # "TensorUnit",
                        # "LeftUnitorWithGivenTensorProduct",
                        # "RightUnitorWithGivenTensorProduct",
                        # "TensorProductOnObjects",
                        # "TensorProductOnMorphismsWithGivenTensorProducts",
                        # "AssociatorLeftToRightWithGivenTensorProducts", # ✗
                        # "BraidingWithGivenTensorProducts", # ✗
                        # "LeftDistributivityExpandingWithGivenObjects",
                        # "LeftDistributivityFactoringWithGivenObjects",
                        "RightDistributivityExpandingWithGivenObjects",
                        # "RightDistributivityExpanding",
                        # "RightDistributivityFactoringWithGivenObjects",
                        # "DualOnObjects",
                        # "DualOnMorphisms",
                        # "CoevaluationForDualWithGivenTensorProduct", # ✗
                        # "EvaluationForDualWithGivenTensorProduct", # ✗
                      ],
        number_of_objectified_objects_in_data_structure_of_object := 1,
        number_of_objectified_morphisms_in_data_structure_of_object := 0,
        number_of_objectified_objects_in_data_structure_of_morphism := 2,
        number_of_objectified_morphisms_in_data_structure_of_morphism := 1
    ); end;;

S4 := SymmetricGroup( 4 );;
A4 := AlternatingGroup( 4 );;

# CapJitEnableStepByStepCompilation();

# CapJitSetDebugLevel(1);

# CapJitCompiledFunction( SGREPS_Associator_1_Morphism );
# CapJitCompiledFunction( SGREPS_Associator_2_Morphism );
# CapJitCompiledFunction( SGREPS_Associator_3_Morphism );
# CapJitCompiledFunction( SGREPS_Associator_4_Morphism );
# CapJitCompiledFunction( SGREPS_Associator_5_Morphism );
# CapJitCompiledFunction( SGREPS_Associator_6_Morphism );
# CapJitCompiledFunction( SGREPS_Associator_7_Morphism );
# CapJitCompiledFunction( SGREPS_Associator_123_Morphism );
# CapJitCompiledFunction( SGREPS_Associator_567_Morphism );

precompile_SkeletalCategoryOfGroupRepresentations( S4, QQ, "S4_Q" );;
# precompile_SkeletalCategoryOfGroupRepresentations( A4, QQ, "A4_Q" );;

# SkeletalCategoryOfGroupRepresentations( S4, QQ )!.precompiled_functions_added;
#! true

#! #@fi

#! @EndExample
