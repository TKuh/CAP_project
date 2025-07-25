#! @Chapter Examples and tests

#! @Section Tests

#! @Example

#! #@if String({}->1-[1-1]) = "function (  ) return 1 - [ (1 - 1) ]; end"

LoadPackage( "LinearClosuresForCAP", false );
#! true
# ReadPackage( "AdditiveClosuresForCAP",
#     "gap/CategoryOfRows_as_AdditiveClosure_RingAsCategory_CompilerLogic.gi" );

homalg_field := DummyHomalgField( );;
# commutative_homalg_ring := DummyCommutativeHomalgRing( );;
# homalg_ring := DummyHomalgRing( );;

DummyHomalgFieldElementFilter := RingElementFilter( homalg_field );;

# CapJitAddTypeSignature( "IsZero", [ DummyHomalgFieldElementFilter ], IsBool );

# CapJitAddTypeSignature( "Sum", [ IsList, DummyHomalgFieldElementFilter ], function ( input_types )
#
#     return CapJitDataTypeOfElementOfRing( homalg_field );
#
# end );

# QQ := HomalgFieldOfRationalsInSingular( );;
# QQxy := QQ * "x,y";;
# EQQxy := KoszulDualRing( QQxy );;

precompile_CoproductOfCategoryOfRowsWithSparseDatastructure := function( homalg_ring, name )
    
    CapJitPrecompileCategoryAndCompareResult(
        homalg_ring ->
            CoproductOfCategoryOfRowsWithSparseDatastructure(
                CategoryOfRows( homalg_ring : FinalizeCategory := true ), 5 ),
        [ homalg_ring ],
        "LinearClosuresForCAP",
        Concatenation(
            "CoproductOfCategoryOfRowsWithSparseDatastructure_",
            name
        ) :
        # operations := "primitive",
        operations := [ "IsEqualForObjects",
                        "IsEqualForMorphisms",
                        "IsCongruentForMorphisms",
                        "ObjectConstructor",
                        "MorphismConstructor",
                        "ObjectDatum",
                        "MorphismDatum",
                        "IdentityMorphism",
                        "PreCompose", #⛌
                        "ZeroMorphism",
                        "IsZeroForMorphisms",
                        "AdditionForMorphisms",
                        "SumOfMorphisms",
                        "AdditiveInverseForMorphisms",
                        "SubtractionForMorphisms", #⛌
                        "ZeroObject",
                        "DirectSum",
                        # "DirectSumFunctorial", #⛌
                        "DirectSumFunctorialWithGivenDirectSums", #⛌
                        "UniversalMorphismIntoDirectSumWithGivenDirectSum",
                        "UniversalMorphismFromDirectSumWithGivenDirectSum",
                        "MultiplyWithElementOfCommutativeRingForMorphisms",
                      ],
        number_of_objectified_objects_in_data_structure_of_object := 2,
        number_of_objectified_morphisms_in_data_structure_of_object := 0,
        number_of_objectified_objects_in_data_structure_of_morphism := 2,
        number_of_objectified_morphisms_in_data_structure_of_morphism := 2
    ); end;;

precompile_CoproductOfCategoryOfRowsWithSparseDatastructure( homalg_field, "Field" );;
# precompile_CategoryOfRows( commutative_homalg_ring, "CommutativeRing" );;
# precompile_CategoryOfRows( EQQxy, "HomalgExteriorRingOverField" );;
# precompile_CategoryOfRows( homalg_ring, "ArbitraryRing" );;

CoproductOfCategoryOfRowsWithSparseDatastructure( CategoryOfRows( homalg_field ), 5 )!.precompiled_functions_added;
#! true

# CategoryOfRows( commutative_homalg_ring )!.precompiled_functions_added;
# #! true
# CategoryOfRows( EQQxy )!.precompiled_functions_added;
# #! true
# CategoryOfRows( homalg_ring )!.precompiled_functions_added;
# #! true

#! #@fi

#! @EndExample
