#! @Chapter Examples and tests

#! @Section Tests

#! @Example

#! #@if String({}->1-[1-1]) = "function (  ) return 1 - [ (1 - 1) ]; end"

LoadPackage( "LinearClosuresForCAP", false );
#! true
ReadPackage( "AdditiveClosuresForCAP",
    "gap/CategoryOfRows_as_AdditiveClosure_RingAsCategory_CompilerLogic.gi" );
#! true

homalg_field := DummyHomalgField( );;
# commutative_homalg_ring := DummyCommutativeHomalgRing( );;
# homalg_ring := DummyHomalgRing( );;

DummyHomalgFieldElementFilter := RingElementFilter( homalg_field );;

CapJitAddTypeSignature( "IsZero", [ DummyHomalgFieldElementFilter ], IsBool );

CapJitAddTypeSignature( "Sum", [ IsList, DummyHomalgFieldElementFilter ], function ( input_types )
    
    return CapJitDataTypeOfElementOfRing( homalg_field );
    
end );

# QQ := HomalgFieldOfRationalsInSingular( );;
# QQxy := QQ * "x,y";;
# EQQxy := KoszulDualRing( QQxy );;

precompile_AdditiveClosureOfObjectFiniteCategory := function( homalg_ring, name )
    
    CapJitPrecompileCategoryAndCompareResult(
        homalg_ring ->
            AdditiveClosureOfObjectFiniteCategory(
                LinearClosure( homalg_ring,
                    FiniteSkeletalDiscreteCategory( 3 : FinalizeCategory := true )
                    : FinalizeCategory := true ) ),
        [ homalg_ring ],
        "AdditiveClosuresForCAP",
        Concatenation(
            "AdditiveClosureOfObjectFiniteCategory_LinearClosure_over_",
            name,
            "_DiscreteCategory_precompiled"
        ) :
        # operations := "primitive",
        operations := [ "IsEqualForObjects",
                        "IsEqualForMorphisms",  #⛌
                        "IsWellDefinedForObjects",
                        # "IsWellDefinedForMorphisms",  # Infinite recursion. The reason seems to be the block around IsWellDefinedForMorphismsWithGivenSourceAndRange
                        "IsCongruentForMorphisms",  #⛌
                        "IdentityMorphism",  #⛌
                        "PreCompose",
                        "ObjectDatum",
                        "ObjectConstructor",
                        "MorphismDatum",
                        "MorphismConstructor",
                        "ZeroMorphism",
                        "IsZeroForMorphisms",
                        "AdditionForMorphisms",
                        "SumOfMorphisms",
                        "AdditiveInverseForMorphisms",
                        "SubtractionForMorphisms",
                        "ZeroObject",
                        "DirectSum",
                        "UniversalMorphismIntoDirectSumWithGivenDirectSum",
                        "UniversalMorphismFromDirectSumWithGivenDirectSum",
                        "ComponentOfMorphismIntoDirectSum",
                        "ComponentOfMorphismFromDirectSum",
                        "MultiplyWithElementOfCommutativeRingForMorphisms",
                      ],
        number_of_objectified_objects_in_data_structure_of_object := 1,
        number_of_objectified_morphisms_in_data_structure_of_object := 0,
        number_of_objectified_objects_in_data_structure_of_morphism := 2,
        number_of_objectified_morphisms_in_data_structure_of_morphism := 2
    ); end;;

precompile_AdditiveClosureOfObjectFiniteCategory( homalg_field, "Field" );;
# precompile_CategoryOfRows( commutative_homalg_ring, "CommutativeRing" );;
# precompile_CategoryOfRows( EQQxy, "HomalgExteriorRingOverField" );;
# precompile_CategoryOfRows( homalg_ring, "ArbitraryRing" );;

# CategoryOfRows( homalg_field )!.precompiled_functions_added;
# #! true

# CategoryOfRows( commutative_homalg_ring )!.precompiled_functions_added;
# #! true
# CategoryOfRows( EQQxy )!.precompiled_functions_added;
# #! true
# CategoryOfRows( homalg_ring )!.precompiled_functions_added;
# #! true

#! #@fi

#! @EndExample
