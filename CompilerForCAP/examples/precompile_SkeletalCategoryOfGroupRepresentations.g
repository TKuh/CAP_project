#! @Chapter Examples and tests

#! @Section Tests

#! @Example

#! #@if String({}->1-[1-1]) = "function (  ) return 1 - [ (1 - 1) ]; end"

LoadPackage( "GroupRepresentationsForCAP", false );
#! true

ReadPackage( "GroupRepresentationsForCAP",
    "gap/SkeletalCategoryOfGroupRepresentations_CompilerLogic.gi" );
#! true


QQ := HomalgFieldOfRationalsInSingular( );;

precompile_SkeletalCategoryOfGroupRepresentations := function( group, homalg_field, name )
    
    CapJitPrecompileCategoryAndCompareResult(
        { group, homalg_field } ->
            SkeletalCategoryOfGroupRepresentations( group, homalg_field ),
        [ group, homalg_field ],
        "GroupRepresentationsForCAP",
        Concatenation(
            "SkeletalCategoryOfGroupRepresentations_",
            name
        ) :
        # operations := "primitive",
        operations := [ "IsEqualForObjects",
                        # "IsEqualForMorphisms",
                        # "IsCongruentForMorphisms",
                        # "ObjectConstructor",
                        # "MorphismConstructor",
                        # "ObjectDatum",
                        # "MorphismDatum",
                        # "IdentityMorphism",
                        # "PreCompose", #⛌
                        # "ZeroMorphism",
                        # "IsZeroForMorphisms",
                        # "AdditionForMorphisms",
                        # "SumOfMorphisms",
                        # "ZeroObject",
                        # "DirectSum",
                        # "DirectSumFunctorial",
                        # "DirectSumFunctorialWithGivenDirectSums",
                        "TensorProductOnObjects",
                        "TensorProductOnMorphismsWithGivenTensorProducts",
                      ],
        number_of_objectified_objects_in_data_structure_of_object := 1,
        number_of_objectified_morphisms_in_data_structure_of_object := 0,
        number_of_objectified_objects_in_data_structure_of_morphism := 2,
        number_of_objectified_morphisms_in_data_structure_of_morphism := 1
    ); end;;

S4 := SymmetricGroup( 4 );;

# CapJitEnableStepByStepCompilation();

# CapJitSetDebugLevel(1);

precompile_SkeletalCategoryOfGroupRepresentations( S4, QQ, "S4_Q" );;

# SkeletalCategoryOfGroupRepresentations( S4, QQ )!.precompiled_functions_added;
#! true

#! #@fi

#! @EndExample
