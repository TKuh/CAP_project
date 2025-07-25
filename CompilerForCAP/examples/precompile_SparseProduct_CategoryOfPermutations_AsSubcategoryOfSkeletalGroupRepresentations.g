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

precompile_SparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations := function( irreducible_characters, name )
    
    CapJitPrecompileCategoryAndCompareResult(
        { irreducible_characters } ->
            SparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations( irreducible_characters
               : no_precompiled_code := true,
                 cat_of_perms_no_precompiled_code := false ),
        [ irreducible_characters ],
        "GroupRepresentationsForCAP",
        Concatenation( "SparseProduct_CategoryOfPermutations_AsSubcategoryOfSkeletalGroupRepresentations_", name, "_precompiled" )
        : operations := [
              "IsEqualForObjects",
              "IsEqualForMorphisms",
              "IsCongruentForMorphisms",
              "IsWellDefinedForObjects",
              "IsWellDefinedForMorphisms",
              "ObjectConstructor",
              "MorphismConstructor",
              "ObjectDatum",
              "MorphismDatum",
              "IdentityMorphism",
              "PreCompose",
              "InverseForMorphisms", #x
              "DirectProduct",
              "DirectProductFunctorialWithGivenDirectProducts",
              "TensorProductOnObjects",
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

precompile_SparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations( irreducible_characters_S4, "S4" );;

# CapJitCompiledFunction( PRODUCT_OF_CATEGORY_OF_PERMUTATIONS_AS_SUBCAT_TensorProductProductOfMorphismWithIdentityWithGivenTensorProducts );;

SparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations( irreducible_characters_S4 )!.precompiled_functions_added;
#! true

#! #@fi

#! @EndExample
