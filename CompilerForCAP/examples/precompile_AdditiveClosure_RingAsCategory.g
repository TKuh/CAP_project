#! @Chapter Examples and tests

#! @Section Tests

#! @Example

#! #@if String({}->1-[1-1]) = "function (  ) return 1 - [ (1 - 1) ]; end"

LoadPackage( "AdditiveClosuresForCAP", false );
#! true
ReadPackage( "AdditiveClosuresForCAP",
    "gap/CategoryOfRows_as_AdditiveClosure_RingAsCategory_CompilerLogic.gi");
#! true

homalg_field := DummyHomalgField( );;
# commutative_homalg_ring := DummyCommutativeHomalgRing( );;
# homalg_ring := DummyHomalgRing( );;

# QQ := HomalgFieldOfRationalsInSingular( );;
# QQxy := QQ * "x,y";;
# EQQxy := KoszulDualRing( QQxy );;

precompile_AdditiveClosure_RingAsCatgory := function( homalg_ring, name )
    
    CapJitPrecompileCategoryAndCompareResult(
        homalg_ring -> AdditiveClosure(
            RING_AS_CATEGORY( homalg_ring : FinalizeCategory := true )
        ),
        [ homalg_ring ],
        "AdditiveClosuresForCAP",
        Concatenation(
            "AdditiveClosure_RingAsCategory_",
            name,
            "_precompiled"
        ) :
        operations := "primitive",
        number_of_objectified_objects_in_data_structure_of_object := 1,
        number_of_objectified_morphisms_in_data_structure_of_object := 0,
        number_of_objectified_objects_in_data_structure_of_morphism := 2,
        number_of_objectified_morphisms_in_data_structure_of_morphism := 2
    ); end;;

precompile_AdditiveClosure_RingAsCatgory( homalg_field, "Field" );;
# precompile_AdditiveClosure_RingAsCatgory( commutative_homalg_ring, "CommutativeRing" );;
# precompile_AdditiveClosure_RingAsCatgory( EQQxy, "HomalgExteriorRingOverField" );;
# precompile_AdditiveClosure_RingAsCatgory( homalg_ring, "ArbitraryRing" );;

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
