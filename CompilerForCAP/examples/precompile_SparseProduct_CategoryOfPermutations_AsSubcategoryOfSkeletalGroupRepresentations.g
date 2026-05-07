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

precompile_SubcategoryOfSkeletalCategoryOfGroupRepresentationsOfSparseProductOfPermutationCategory := function( irreducible_characters, name )
    
    CapJitPrecompileCategoryAndCompareResult(
        { irreducible_characters } ->
            SubcategoryOfSkeletalCategoryOfGroupRepresentationsOfSparseProductOfPermutationCategory( irreducible_characters
               : no_precompiled_code := true ),
        [ irreducible_characters ],
        "GroupRepresentationsForCAP",
        Concatenation( "Subcategory_SkeletalCategoryOfGroupRepresentations_", name, "_SparseProduct_PermutationCategory_precompiled" )
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
              "Coproduct",
              "CoproductFunctorialWithGivenCoproducts",
              # "TensorProductOnObjects",
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

precompile_SubcategoryOfSkeletalCategoryOfGroupRepresentationsOfSparseProductOfPermutationCategory( irreducible_characters_S4, "S4" );;

# CapJitCompiledFunction( PRODUCT_OF_CATEGORY_OF_PERMUTATIONS_AS_SUBCAT_TensorProductProductOfMorphismWithIdentityWithGivenTensorProducts );;

SubcategoryOfSkeletalCategoryOfGroupRepresentationsOfSparseProductOfPermutationCategory( irreducible_characters_S4 )!.precompiled_functions_added;
#! true

#! #@fi

#! @EndExample
