# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Implementations
#

# Read precompiled categories
# ReadPackage( "AdditiveClosuresForCAP", "gap/precompiled_categories/SparseProductOfCartesianCategory_Rows_Field.gi" );

####################################
##
## Constructors
##
####################################

##
InstallMethod( SparseProductOfCartesianCategory,
               [ IsBigInt, IsCapCategory ],
               
  FunctionWithNamedArguments(
  [
    [ "FinalizeCategory", true ],
  ],
  function( CAP_NAMED_ARGUMENTS, nr_factors, cartesian_cat )
    local name, object_datum_type, morphism_datum_type, sparse_product, compare_morphisms, object_datum, object_constructor, morphism_datum, morphism_constructor, SubscriptDigits, ToSubscript;
    
    Assert( 0, nr_factors > 0 );
    
    ##
    name := Concatenation( "𝚷( ", String( nr_factors ), ", ", Name( cartesian_cat ), " )" );
    
    ##
    object_datum_type :=
        CapJitDataTypeOfNTupleOf( 3,
            IsBigInt,
            CapJitDataTypeOfListOf( IsBigInt ),
            CapJitDataTypeOfListOf( CapJitDataTypeOfObjectOfCategory( cartesian_cat ) ) );
    
    ##
    morphism_datum_type := CapJitDataTypeOfNTupleOf( 3,
            IsBigInt,
            CapJitDataTypeOfListOf( IsBigInt ),
            CapJitDataTypeOfListOf( CapJitDataTypeOfMorphismOfCategory( cartesian_cat ) ) );
    
    ##
    sparse_product :=
        CreateCapCategoryWithDataTypes(
            name,
            IsSparseProductOfCartesianCategory,
            IsObjectInSparseProductOfCartesianCategory,
            IsMorphismInSparseProductOfCartesianCategory,
            IsCapCategoryTwoCell,
            object_datum_type,
            morphism_datum_type,
            fail );
    
    SetUnderlyingCartesianCategory( sparse_product, cartesian_cat );
    
    SetNrFactors( sparse_product, nr_factors );
    
    sparse_product!.compiler_hints :=
        rec( category_attribute_names :=
            [ "NrFactors",
              "UnderlyingCartesianCategory" ] );
    
    SetIsCartesianCategory( cartesian_cat, true );
    
    if HasIsSkeletalCategory( cartesian_cat )and IsSkeletalCategory( cartesian_cat ) then
        
        SetIsSkeletalCategory( sparse_product, true );
        
    fi;
    
    INSTALL_FUNCTIONS_FOR_SPARSE_DIRECT_PRODUCT_OF_CARTESIAN_CATEGORY( sparse_product );
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        
        Finalize( sparse_product );
        
    fi;
    
    return sparse_product;
    
end ) );

####################################
##
## Basic operations
##
####################################

InstallGlobalFunction( INSTALL_FUNCTIONS_FOR_SPARSE_DIRECT_PRODUCT_OF_CARTESIAN_CATEGORY,
  
  function( sparse_product )
    local compare_morphisms, cartesian_cat;
    
    ##
    AddObjectDatum( sparse_product,
      function( sparse_product, object )
        
        return TripleOfNrSupportListOfSupportListOfObjects( object );
        
    end );
    
    ##
    AddObjectConstructor( sparse_product,
      function( sparse_product, triple )
        local cartesian_cat, nr_support, support, objects;
        
        cartesian_cat := UnderlyingCartesianCategory( sparse_product );
        
        nr_support := triple[1];
        support := triple[2];
        objects := triple[3];
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, 0 <= nr_support and nr_support <= NrFactors( sparse_product ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( support ) = nr_support );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( objects ) = nr_support );
        
        # The supporting integers must be between
        # 1 and NrFactors( sparse_product ).
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( [ 1 .. nr_support ], i ->
            1 <= support[i] and support[i] <= NrFactors( sparse_product ) ) );
        
        # The supporting integers must be strictly increasing.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( [ 1 .. nr_support - 1 ], i ->
            support[i] < support[i+1] ) );
        
        # Assert( 0, ForAll( objects, object -> not IsTerminal( cartesian_cat, object ) ) );
        
        return CreateCapCategoryObjectWithAttributes( sparse_product,
                       TripleOfNrSupportListOfSupportListOfObjects, triple );
                       
    end );
    
    ##
    AddMorphismDatum( sparse_product,
      function( sparse_product, morphism )
        
        return TripleOfNrSupportListOfSupportListOfMorphisms( morphism );
        
    end );
    
    ##
    AddMorphismConstructor( sparse_product,
      function( sparse_product, S, triple, T )
        local cartesian_cat, nr_support, support, morphisms, source_nr_support, source_support, source_components, target_nr_support, target_support, target_components, i, current_support, rows_morphism, source, target, s, terminal_object, terminal_morphism, t;
        
        cartesian_cat := UnderlyingCartesianCategory( sparse_product );
        
        nr_support := triple[1];
        support := triple[2];
        morphisms := triple[3];
        
        source_nr_support := NrSupport( S );
        source_support := Support( S );
        source_components := Components( S );
        
        target_nr_support := NrSupport( T );
        target_support := Support( T );
        target_components := Components( T );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, 0 <= nr_support and nr_support <= NrFactors( sparse_product ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( support ) = nr_support );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( morphisms ) = nr_support );
        
        # The supporting integers must be between
        # 1 and NrFactors( sparse_product ).
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( [ 1 .. nr_support ], i ->
            1 <= support[i] and support[i] <= NrFactors( sparse_product ) ) );
        
        # The supporting integers must be strictly increasing.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( [ 1 .. nr_support - 1 ], i ->
            support[i] < support[i+1] ) );
        
        # For all morphisms in 'morphisms',
        # the source and target at a support must be equal to the objects
        # in 'S' and 'T' at the same support.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        for i in [ 1.. nr_support ] do
            
            current_support := support[i];
            
            rows_morphism := morphisms[i];
            
            source := Source( rows_morphism );
            target := Target( rows_morphism );
            
            Assert( 0, IsEqualForObjects( cartesian_cat, source, Component( S, current_support ) ) and
                       IsEqualForObjects( cartesian_cat, target, Component( T, current_support ) ) );
                       
        od;
        
        # For any object s in 'S' there must be a morphism m
        # at the same support with Source( m ) = s.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        for i in [ 1.. source_nr_support ] do
            
            current_support := source_support[i];
            
            s := source_components[i];
            
            terminal_object := TerminalObject( cartesian_cat );
            terminal_morphism := UniversalMorphismIntoTerminalObjectWithGivenTerminalObject(
                                        cartesian_cat,
                                        terminal_object,
                                        terminal_object );
            
            # Get the morphism at support i or a nx0 morphism.
            rows_morphism := [ [ terminal_morphism ], morphisms{ Positions( support, current_support ) } ][ 1 + BooleanToInteger( current_support in support ) ][1];
            
            source := Source( rows_morphism );
            
            Assert( 0, IsEqualForObjects( cartesian_cat, s, source ) );
            
        od;
        
        # For any object t in 'T' there must be a morphism m
        # at the same support with Target( m ) = t.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        for i in [ 1.. target_nr_support ] do
            
            current_support := target_support[i];
            
            t := target_components[i];
            
            terminal_object := TerminalObject( cartesian_cat );
            terminal_morphism := UniversalMorphismIntoTerminalObjectWithGivenTerminalObject(
                                        cartesian_cat,
                                        terminal_object,
                                        terminal_object );
            
            # Get the morphism at support i or a nx0 morphism.
            rows_morphism := [ [ terminal_morphism ], morphisms{ Positions( support, current_support ) } ][ 1 + BooleanToInteger( current_support in support ) ][1];
            
            target := Target( rows_morphism );
            
            Assert( 0, IsEqualForObjects( cartesian_cat, t, target ) );
            
        od;
        
        return CreateCapCategoryMorphismWithAttributes(
                    sparse_product,
                    S,
                    T,
                    TripleOfNrSupportListOfSupportListOfMorphisms, triple );
                    
    end );
    
    ##
    AddIsWellDefinedForObjects( sparse_product,
      function( sparse_product, object )
        local cartesian_cat, nr_support, support, components;
        
        cartesian_cat := UnderlyingCartesianCategory( sparse_product );
        
        nr_support := NrSupport( object );
        support := Support( object );
        components := Components( object );
        
        if nr_support <> Length( support ) or nr_support <> Length( components ) then
            
            return false;
            
        elif not ForAll( support, n ->
            1 <= n and n <= NrFactors( sparse_product ) ) then
            
            return false;
            
        # All support must be strictly increasing.
        elif not ForAll( [ 1 .. nr_support - 1 ], n -> support[n] < support[n+1] ) then
            
            return false;
            
        elif not ForAll( [ 1 .. nr_support ], n -> IsWellDefinedForObjects( cartesian_cat, components[n] ) ) then
            
            return false;
            
        # The terminal object is not allowed in this datastructure.
        elif ForAny( [ 1 .. nr_support ], n -> IsTerminal( cartesian_cat, components[n] ) ) then
            
            return false;
            
        else
            
            return true;
            
        fi;
        
    end );
    
    ##
    AddIsWellDefinedForMorphisms( sparse_product,
      function( sparse_product, morphism )
        local cartesian_cat, nr_support, support, components, source, target;
        
        cartesian_cat := UnderlyingCartesianCategory( sparse_product );
        
        nr_support := NrSupport( morphism );
        support := Support( morphism );
        components := Components( morphism );
        
        source := Source( morphism );
        target := Target( morphism );
        
        if nr_support <> Length( support ) or nr_support <> Length( components ) then
            
            return false;
            
        elif not ForAll( [ 1 .. nr_support ], i ->
            1 <= support[i] and support[i] <= NrFactors( sparse_product ) ) then
            
            return false;
            
        # 0x0 components are not allowed in this sparse datastructure.
        elif ForAny( [ 1 .. nr_support ], i ->
            IsTerminal( cartesian_cat, Source( components[i] ) ) and
            IsTerminal( cartesian_cat, Target( components[i] ) ) ) then
            
            return false;
            
        # All support must be strictly increasing.
        elif not ForAll( [ 1 .. nr_support - 1 ], i -> support[i] < support[i+1] ) then
            
            return false;
            
        elif not ForAll( [ 1 .. nr_support ], i ->
            # IsWellDefinedForMorphismsWithGivenSourceAndRange( cartesian_cat,
            IsWellDefinedForMorphisms( cartesian_cat,
                # Component( source, i ),
                components[i] ) )
                # Component( target, i ) ) )
        then
            
            return false;
            
        else
            
            return true;
            
        fi;
        
    end );
    
    ##
    AddIsEqualForObjects( sparse_product,
      function( sparse_product, object_1, object_2 )
        local cartesian_cat, nr_support_1, nr_support_2, support_1, support_2, components_1, components_2;
        
        cartesian_cat := UnderlyingCartesianCategory( sparse_product );
        
        nr_support_1 := NrSupport( object_1 );
        support_1 := Support( object_1 );
        components_1 := Components( object_1 );
        
        nr_support_2 := NrSupport( object_2 );
        support_2 := Support( object_2 );
        components_2 := Components( object_2 );
        
        return nr_support_1 = nr_support_2 and support_1 = support_2 and
            ForAll( [ 1 .. nr_support_1 ], i ->
                IsEqualForObjects( cartesian_cat, components_1[i], components_2[i] ) );
                
    end );
    
    compare_morphisms :=
      function( sparse_product, morphism_1, morphism_2, comparison_function )
        local cartesian_cat, nr_support_1, nr_support_2, support_1, support_2, components_1, components_2;
        #% CAP_JIT_RESOLVE_FUNCTION
        
        cartesian_cat := UnderlyingCartesianCategory( sparse_product );
        
        nr_support_1 := NrSupport( morphism_1 );
        support_1 := Support( morphism_1 );
        components_1 := Components( morphism_1 );
        
        nr_support_2 := NrSupport( morphism_2 );
        support_2 := Support( morphism_2 );
        components_2 := Components( morphism_2 );
        
        return nr_support_1 = nr_support_2 and support_1 = support_2 and
            ForAll( [ 1 .. nr_support_1 ], i ->
                comparison_function( cartesian_cat, components_1[i], components_2[i] ) );
                
    end;
    
    ##
    AddIsEqualForMorphisms( sparse_product,
      function( sparse_product, morphism_1, morphism_2 )
        
        return compare_morphisms( sparse_product, morphism_1, morphism_2, IsEqualForMorphisms );
        
    end );
    
    ##
    AddIsCongruentForMorphisms( sparse_product,
      function( sparse_product, morphism_1, morphism_2 )
        
        return compare_morphisms( sparse_product, morphism_1, morphism_2, IsCongruentForMorphisms );
        
    end );
    
    ##
    AddIdentityMorphism( sparse_product,
      function( sparse_product, object )
        local cartesian_cat, nr_support, support, components, identity_morphisms;
        
        cartesian_cat := UnderlyingCartesianCategory( sparse_product );
        
        nr_support := NrSupport( object );
        support := Support( object );
        components := Components( object );
        
        identity_morphisms :=
            List( [ 1 .. nr_support ], n ->
               IdentityMorphism( cartesian_cat, components[n] ) );
        
        return MorphismConstructor( sparse_product,
                    object,
                    NTuple( 3, nr_support, support, identity_morphisms ),
                    object );
                    
    end );
    
    ##
    AddPreCompose( sparse_product,
      function( sparse_product, morphism_1, morphism_2 )
        local cartesian_cat, support_1, support_2, support, nr_support, precomposed_morphisms;
        
        cartesian_cat := UnderlyingCartesianCategory( sparse_product );
        
        support_1 := Support( morphism_1 );
        support_2 := Support( morphism_2 );
        
        support := Union2( support_1, support_2 );
        
        nr_support := Length( support );
        
        precomposed_morphisms :=
            List( [ 1 .. nr_support ], n ->
                PreCompose( cartesian_cat, Component( morphism_1, support[n] ), Component( morphism_2, support[n] ) ) );
        
        return MorphismConstructor( sparse_product,
                    Source( morphism_1 ),
                    NTuple( 3, nr_support, support, precomposed_morphisms ),
                    Target( morphism_2 ) );
                    
    end );
    
    ##
    AddTerminalObject( sparse_product,
      function( sparse_product )
        
        return ObjectConstructor(sparse_product,
                    NTuple( 3,
                        0,
                        CapJitTypedExpression( [ ], { } -> CapJitDataTypeOfListOf( IsBigInt ) ),
                        CapJitTypedExpression( [ ], cat ->
                            CapJitDataTypeOfListOf( CapJitDataTypeOfObjectOfCategory( UnderlyingCartesianCategory( cat ) ) ) ) ) );
                            
    end );
    
    ##
    AddUniversalMorphismIntoTerminalObjectWithGivenTerminalObject( sparse_product,
      function( sparse_product, object, terminal_object )
        local cartesian_cat, nr_support, support, terminal_morphisms;
        
        cartesian_cat := UnderlyingCartesianCategory( sparse_product );
        
        nr_support := NrSupport( object );
        support := Support( object );
        
        terminal_morphisms :=
            List( [ 1 .. nr_support ], i ->
                UniversalMorphismIntoTerminalObjectWithGivenTerminalObject( cartesian_cat, Component( object, support[i] ), Component( terminal_object, support[i] ) ) );
                
        return MorphismConstructor( sparse_product,
                    object,
                    NTuple( 3, Length( support ), support, terminal_morphisms ),
                    terminal_object );
                    
    end );
    
    ##
    AddIsTerminal( sparse_product,
      function( sparse_product, object )
        local cartesian_cat, nr_support, components;
        
        cartesian_cat := UnderlyingCartesianCategory( sparse_product );
        
        nr_support := NrSupport( object );
        components := Components( object );
        
        return ForAll( [ 1 .. nr_support ], i -> IsTerminal( cartesian_cat, components[i] ) );
        
    end );
    
    ##
    AddDirectProduct( sparse_product,
      function( sparse_product, diagram )
        local cartesian_cat, support, nr_support, sums;
        
        cartesian_cat := UnderlyingCartesianCategory( sparse_product );
        
        support := Union( List( diagram, obj -> Support( obj ) ) );
        
        nr_support := Length( support );
        
        # Due to calling 'Component' below for all support, we might sum over many zeros.
        sums := List( [ 1 .. nr_support ], n ->
            DirectProduct( cartesian_cat, List( diagram, obj -> Component( obj, support[n] ) ) ) );
            
        return ObjectConstructor( sparse_product, NTuple( 3, nr_support, support, sums ) );
        
    end );
    
    ##
    AddProjectionInFactorOfDirectProductWithGivenDirectProduct( sparse_product,
      function( sparse_product, objects, projection_number, direct_sum_object )
        local cartesian_cat, nr_support, support, morphisms;
        
        cartesian_cat := UnderlyingCartesianCategory( sparse_product );
        
        nr_support := NrSupport( direct_sum_object );
        support := Support( direct_sum_object );
        
        morphisms :=
            List( [ 1 .. nr_support ], function( i )
                local objects_list;
                
                objects_list := List( objects, obj -> Component( obj, support[i] ) );
                
                return ProjectionInFactorOfDirectProductWithGivenDirectProduct( cartesian_cat,
                            objects_list,
                            projection_number,
                            Component( direct_sum_object, support[i] ) );
                            
            end );
            
        return MorphismConstructor( sparse_product,
                    direct_sum_object,
                    NTuple( 3,
                        NrSupport( direct_sum_object ),
                        support,
                        morphisms ),
                    objects[ projection_number ] );
                    
    end );
    
    ##
    AddUniversalMorphismIntoDirectProductWithGivenDirectProduct( sparse_product,
      function( sparse_product, target_diagram, test_object, morphisms, direct_product )
        local cartesian_cat, support_test_object, support_direct_product, support, nr_support, list_of_universal_mors;
        
        cartesian_cat := UnderlyingCartesianCategory( sparse_product );
        
        support_test_object := Support( test_object );
        
        support_direct_product := Support( direct_product );
        
        support := Union2( support_test_object, support_direct_product );
        
        nr_support := Length( support );
        
        list_of_universal_mors :=
            List( [ 1 .. nr_support ], n ->
                UniversalMorphismIntoDirectProductWithGivenDirectProduct( cartesian_cat,
                    List( target_diagram, s -> Component( s, support[n] ) ),
                    Component( test_object, support[n] ),
                    List( morphisms, morphism -> Component( morphism, support[n] ) ),
                    Component( direct_product, support[n] ) ) );
                    
        return MorphismConstructor( sparse_product,
                    test_object,
                    NTuple( 3, nr_support, support, list_of_universal_mors ),
                    direct_product );
                    
    end );
    
    ##
    AddDirectProductFunctorialWithGivenDirectProducts( sparse_product,
      function( cat, direct_product_source, source_diagram, morphism_diagram, target_diagram, direct_product_target )
        local cartesian_cat, support, nr_support, products;
        
        cartesian_cat := UnderlyingCartesianCategory( sparse_product );
        
        support := Union( List( morphism_diagram, mor -> Support( mor ) ) );
        
        nr_support := Length( support );
        
        # Due to calling 'Component' below for all supports, we might sum over many zeros.
        products := List( [ 1 .. nr_support ], n ->
            DirectProductFunctorialWithGivenDirectProducts( cartesian_cat,
                Component( direct_product_source, support[n] ),
                List( source_diagram, source -> Component( source, support[n] ) ),
                List( morphism_diagram, morphism -> Component( morphism, support[n] ) ),
                List( target_diagram, target -> Component( target, support[n] ) ),
                Component( direct_product_target, support[n] ) ) );
                
        return MorphismConstructor( sparse_product,
                    direct_product_source,
                    NTuple( 3, nr_support, support, products ),
                    direct_product_target );
                    
    end );
    
end );

####################################
##
## Attributes
##
####################################

InstallMethodForCompilerForCAP( NrSupport,
                                [ IsObjectInSparseProductOfCartesianCategory ],
                                
  function( object )
    
    return TripleOfNrSupportListOfSupportListOfObjects( object )[1];
    
end );

InstallMethodForCompilerForCAP( NrSupport,
                                [ IsMorphismInSparseProductOfCartesianCategory ],
                                
  function( morphism )
    
    return TripleOfNrSupportListOfSupportListOfMorphisms( morphism )[1];
    
end );

InstallMethodForCompilerForCAP( Support,
                                [ IsObjectInSparseProductOfCartesianCategory ],
                                
  function( object )
    
    return TripleOfNrSupportListOfSupportListOfObjects( object )[2];
    
end );

InstallMethodForCompilerForCAP( Support,
                                [ IsMorphismInSparseProductOfCartesianCategory ],
                                
  function( morphism )
    
    return TripleOfNrSupportListOfSupportListOfMorphisms( morphism )[2];
    
end );

InstallMethodForCompilerForCAP( Components,
                                [ IsObjectInSparseProductOfCartesianCategory ],
                                
  function( object )
    
    return TripleOfNrSupportListOfSupportListOfObjects( object )[3];
    
end );

InstallMethodForCompilerForCAP( Components,
                                [ IsMorphismInSparseProductOfCartesianCategory ],
                                
  function( morphism )
    
    return TripleOfNrSupportListOfSupportListOfMorphisms( morphism )[3];
    
end );

####################################
##
## Operations
##
####################################

InstallMethodForCompilerForCAP( Component,
                                [ IsObjectInSparseProductOfCartesianCategory, IsBigInt ],
                                
  function( object, i )
    local cartesian_cat, terminal_object, support, objects;
    
    #% CAP_JIT_DROP_NEXT_STATEMENT
    Assert( 0, 1 <= i and i <= NrFactors( CapCategory( object ) ) );
    
    cartesian_cat := UnderlyingCartesianCategory( CapCategory( object ) );
    
    terminal_object := TerminalObject( cartesian_cat );
    
    support := Support( object );
    
    objects := Components( object );
    
    return [ [ terminal_object ], objects{ Positions( support, i ) } ][ 1 + BooleanToInteger( i in support ) ][1];
    
end );

InstallMethodForCompilerForCAP( Component,
                                [ IsMorphismInSparseProductOfCartesianCategory, IsBigInt ],
                                
  function( morphism, i )
    local cartesian_cat, terminal_object, terminal_morphism, support, morphisms;
    
    #% CAP_JIT_DROP_NEXT_STATEMENT
    Assert( 0, 1 <= i and i <= NrFactors( CapCategory( morphism ) ) );
    
    cartesian_cat := UnderlyingCartesianCategory( CapCategory( morphism ) );
    
    terminal_object := TerminalObject( cartesian_cat );
    
    terminal_morphism :=
        UniversalMorphismIntoTerminalObjectWithGivenTerminalObject(
            cartesian_cat,
            terminal_object,
            terminal_object );
            
    support := Support( morphism );
    
    morphisms := Components( morphism );
    
    return [ [ terminal_morphism ], morphisms{ Positions( support, i ) } ][ 1 + BooleanToInteger( i in support ) ][1];
    
end );

##
InstallMethodForCompilerForCAP( \[\],
                                [ IsObjectInSparseProductOfCartesianCategory, IsInt ],
                                
  function( object, i )
    
    return Component( object, i );
    
end );

##
InstallMethodForCompilerForCAP( \[\],
                                [ IsMorphismInSparseProductOfCartesianCategory, IsInt ],
                                
  function( morphism, i )
    
    return Component( morphism, i );
    
end );

####################################
##
## View & Display
##
####################################

InstallMethod( DisplayString,
               [ IsObjectInSparseProductOfCartesianCategory ],
               
  object -> String( TripleOfNrSupportListOfSupportListOfObjects( object ) )
  
);

InstallMethod( DisplayString,
               [ IsMorphismInSparseProductOfCartesianCategory ],
               
  morphism -> String( TripleOfNrSupportListOfSupportListOfMorphisms( morphism ) )
  
);

