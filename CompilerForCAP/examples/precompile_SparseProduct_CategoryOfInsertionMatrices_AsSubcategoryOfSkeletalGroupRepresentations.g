#! @Chapter Examples and tests

#! @Section Tests

#! @Example

#! #@if String({}->1-[1-1]) = "function (  ) return 1 - [ (1 - 1) ]; end"

LoadPackage( "GroupRepresentationsForCAP", false );
#! true

CapJitAddTypeSignature( "Union", [ IsList ], function ( input_types )
    
    Assert( 0,
        input_types[1].element_type.filter = IsList and
        input_types[1].element_type.element_type.filter = IsBigInt );
        
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

precompile_SparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations := function( irreducible_characters, name )
    
    CapJitPrecompileCategoryAndCompareResult(
        { irreducible_characters } ->
            SparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations( irreducible_characters
               : no_precompiled_code := true,
                 pwp_no_precompiled_code := false ),
        [ irreducible_characters ],
        "GroupRepresentationsForCAP",
        Concatenation( "SparseProduct_CategoryOfInsertionMatrices_AsSubcategoryOfSkeletalGroupRepresentations_", name, "_precompiled" )
        : operations := [ # "IsEqualForObjects",
                          # "IsEqualForMorphisms",
                          # "SimplifyEndo", # x
                          # "IsCongruentForMorphisms", # x
                          # "IsWellDefinedForObjects",
                          # "IsWellDefinedForMorphismsWithGivenSourceAndRange", # x
                          # "IsWellDefinedForMorphisms", # x
                          # "ObjectConstructor",
                          # "MorphismConstructor",
                          # "ObjectDatum",
                          # "MorphismDatum",
                          # "IdentityMorphism",
                          # "PreCompose", # x
                          # "TerminalObject",
                          # "IsTerminal",
                          # "UniversalMorphismIntoTerminalObjectWithGivenTerminalObject",
                          # "DirectProduct",
                          # "ProjectionInFactorOfDirectProductWithGivenDirectProduct",
                          # "UniversalMorphismIntoDirectProductWithGivenDirectProduct",
                          # "DirectProductFunctorialWithGivenDirectProducts",
                          # "TensorProductOnObjects",
                          # "TensorProductOnMorphismsWithGivenTensorProducts",
                          "RightDistributivityExpandingWithGivenObjects",
                          ],
          # : operations := "",
          number_of_objectified_objects_in_data_structure_of_object := 1,
          number_of_objectified_morphisms_in_data_structure_of_object := 0,
          number_of_objectified_objects_in_data_structure_of_morphism := 2,
          number_of_objectified_morphisms_in_data_structure_of_morphism := 1 );
          
end;;

# CapJitEnableStepByStepCompilation();

# CapJitSetDebugLevel( 1 );

character_table_S4 := CharacterTable( SymmetricGroup( 4 ) );
irreducible_characters_S4 := Irr( character_table_S4 );

precompile_SparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations( irreducible_characters_S4, "S4" );;

SparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations( irreducible_characters_S4 )!.precompiled_functions_added;
#! true

#! #@fi

#! @EndExample
