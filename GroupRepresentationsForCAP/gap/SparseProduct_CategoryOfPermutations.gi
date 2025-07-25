# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Implementations
#

# Read precompiled categories
# ReadPackage( "GroupRepresentationsForCAP", "gap/precompiled_categories/" );

####################################
##
## Constructors
##
####################################

##
InstallMethod( SparseProductOfCategoryOfPermutations,
               [ IsBigInt, IsCapCategory ],
               
  FunctionWithNamedArguments(
  [
    [ "FinalizeCategory", true ],
  ],
  function( CAP_NAMED_ARGUMENTS, nr_factors, cat_of_perms )
    local name, object_datum_type, morphism_datum_type, sparse_product, compare_morphisms, object_datum, object_constructor, morphism_datum, morphism_constructor, SubscriptDigits, ToSubscript;
    
    Assert( 0, nr_factors > 0 );
    
    ##
    name := Concatenation( "𝚷( ", String( nr_factors ), ", ", Name( cat_of_perms ), " )" );
    
    ##
    object_datum_type :=
        CapJitDataTypeOfNTupleOf( 3,
            IsBigInt,
            CapJitDataTypeOfListOf( IsBigInt ),
            CapJitDataTypeOfListOf( CapJitDataTypeOfObjectOfCategory( cat_of_perms ) ) );
    
    ##
    morphism_datum_type := CapJitDataTypeOfNTupleOf( 3,
            IsBigInt,
            CapJitDataTypeOfListOf( IsBigInt ),
            CapJitDataTypeOfListOf( CapJitDataTypeOfMorphismOfCategory( cat_of_perms ) ) );
    
    ##
    sparse_product :=
        CreateCapCategoryWithDataTypes(
            name,
            IsSparseProductOfCategoryOfPermutations,
            IsObjectInSparseProductOfCategoryOfPermutations,
            IsMorphismInSparseProductOfCategoryOfPermutations,
            IsCapCategoryTwoCell,
            object_datum_type,
            morphism_datum_type,
            fail );
    
    SetUnderlyingCategoryOfPermutations( sparse_product, cat_of_perms );
    
    SetNrFactors( sparse_product, nr_factors );
    
    sparse_product!.compiler_hints :=
        rec( category_attribute_names :=
            [ "NrFactors",
              "UnderlyingCategoryOfPermutations" ] );
    
    SetIsSkeletalCategory( sparse_product, true );
    
    INSTALL_FUNCTIONS_FOR_SPARSE_DIRECT_PRODUCT_OF_CATEGORY_OF_PERMUTATIONS( sparse_product );
    
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

InstallGlobalFunction( INSTALL_FUNCTIONS_FOR_SPARSE_DIRECT_PRODUCT_OF_CATEGORY_OF_PERMUTATIONS,
  
  function( sparse_product )
    local compare_morphisms, cat_of_perms;
    
    ##
    AddObjectDatum( sparse_product,
      function( sparse_product, object )
        
        return TripleOfNrSupportListOfSupportListOfObjects( object );
        
    end );
    
    ##
    AddObjectConstructor( sparse_product,
      function( sparse_product, triple )
        local cat_of_perms, nr_support, support, objects;
        
        cat_of_perms := UnderlyingCategoryOfPermutations( sparse_product );
        
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
        
        # Assert( 0, ForAll( objects, object -> not IsTerminal( cat_of_perms, object ) ) );
        
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
        local cat_of_perms, nr_support, support, morphisms, source_nr_support, source_support, source_components, target_nr_support, target_support, target_components, i, current_support, rows_morphism, source, target, s, zero, empty_permutation_morphism, t;
        
        cat_of_perms := UnderlyingCategoryOfPermutations( sparse_product );
        
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
            
            Assert( 0, IsEqualForObjects( cat_of_perms, source, Component( S, current_support ) ) and
                       IsEqualForObjects( cat_of_perms, target, Component( T, current_support ) ) );
                       
        od;
        
        # For any object s in 'S' there must be a morphism m
        # at the same support with Source( m ) = s.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        for i in [ 1.. source_nr_support ] do
            
            current_support := source_support[i];
            
            s := source_components[i];
            
            zero := ObjectConstructor( cat_of_perms, 0 );
            
            empty_permutation_morphism := MorphismConstructor( cat_of_perms, zero, (), zero );
            
            # Get the morphism at support i or a nx0 morphism.
            rows_morphism := [ [ empty_permutation_morphism ], morphisms{ Positions( support, current_support ) } ][ 1 + BooleanToInteger( current_support in support ) ][1];
            
            source := Source( rows_morphism );
            
            Assert( 0, IsEqualForObjects( cat_of_perms, s, source ) );
            
        od;
        
        # For any object t in 'T' there must be a morphism m
        # at the same support with Target( m ) = t.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        for i in [ 1.. target_nr_support ] do
            
            current_support := target_support[i];
            
            t := target_components[i];
            
            zero := ObjectConstructor( cat_of_perms, 0 );
            
            empty_permutation_morphism := MorphismConstructor( cat_of_perms, zero, (), zero );
            
            # Get the morphism at support i or a nx0 morphism.
            rows_morphism := [ [ empty_permutation_morphism ], morphisms{ Positions( support, current_support ) } ][ 1 + BooleanToInteger( current_support in support ) ][1];
            
            target := Target( rows_morphism );
            
            Assert( 0, IsEqualForObjects( cat_of_perms, t, target ) );
            
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
        local cat_of_perms, nr_support, support, components;
        
        cat_of_perms := UnderlyingCategoryOfPermutations( sparse_product );
        
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
            
        elif not ForAll( [ 1 .. nr_support ], n -> IsWellDefinedForObjects( cat_of_perms, components[n] ) ) then
            
            return false;
            
        # An object with cardinality 0 is not allowed in this sparse datastructure.
        elif ForAny( [ 1 .. nr_support ], n -> Cardinality( components[n] ) = 0 ) then
            
            return false;
            
        else
            
            return true;
            
        fi;
        
    end );
    
    ##
    AddIsWellDefinedForMorphisms( sparse_product,
      function( sparse_product, morphism )
        local cat_of_perms, nr_support, support, components, source, target;
        
        cat_of_perms := UnderlyingCategoryOfPermutations( sparse_product );
        
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
            Cardinality( Source( components[i] ) ) = 0 and
            Cardinality( Target( components[i] ) ) = 0 ) then
            
            return false;
            
        # All support must be strictly increasing.
        elif not ForAll( [ 1 .. nr_support - 1 ], i -> support[i] < support[i+1] ) then
            
            return false;
            
        elif not ForAll( [ 1 .. nr_support ], i ->
            # IsWellDefinedForMorphismsWithGivenSourceAndRange( cat_of_perms,
            IsWellDefinedForMorphisms( cat_of_perms,
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
        local cat_of_perms, nr_support_1, nr_support_2, support_1, support_2, components_1, components_2;
        
        cat_of_perms := UnderlyingCategoryOfPermutations( sparse_product );
        
        nr_support_1 := NrSupport( object_1 );
        support_1 := Support( object_1 );
        components_1 := Components( object_1 );
        
        nr_support_2 := NrSupport( object_2 );
        support_2 := Support( object_2 );
        components_2 := Components( object_2 );
        
        return nr_support_1 = nr_support_2 and support_1 = support_2 and
            ForAll( [ 1 .. nr_support_1 ], i ->
                IsEqualForObjects( cat_of_perms, components_1[i], components_2[i] ) );
                
    end );
    
    compare_morphisms :=
      function( sparse_product, morphism_1, morphism_2, comparison_function )
        local cat_of_perms, nr_support_1, nr_support_2, support_1, support_2, components_1, components_2;
        #% CAP_JIT_RESOLVE_FUNCTION
        
        cat_of_perms := UnderlyingCategoryOfPermutations( sparse_product );
        
        nr_support_1 := NrSupport( morphism_1 );
        support_1 := Support( morphism_1 );
        components_1 := Components( morphism_1 );
        
        nr_support_2 := NrSupport( morphism_2 );
        support_2 := Support( morphism_2 );
        components_2 := Components( morphism_2 );
        
        return nr_support_1 = nr_support_2 and support_1 = support_2 and
            ForAll( [ 1 .. nr_support_1 ], i ->
                comparison_function( cat_of_perms, components_1[i], components_2[i] ) );
                
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
        local cat_of_perms, nr_support, support, components, identity_morphisms;
        
        cat_of_perms := UnderlyingCategoryOfPermutations( sparse_product );
        
        nr_support := NrSupport( object );
        support := Support( object );
        components := Components( object );
        
        identity_morphisms :=
            List( [ 1 .. nr_support ], n ->
               IdentityMorphism( cat_of_perms, components[n] ) );
        
        return MorphismConstructor( sparse_product,
                    object,
                    NTuple( 3, nr_support, support, identity_morphisms ),
                    object );
                    
    end );
    
    ##
    AddPreCompose( sparse_product,
      function( sparse_product, morphism_1, morphism_2 )
        local cat_of_perms, nr_support, support, components_1, components_2, precomposed_morphisms, object;
        
        cat_of_perms := UnderlyingCategoryOfPermutations( sparse_product );
        
        nr_support := NrSupport( morphism_1 );
        support := Support( morphism_1 );
        
        components_1 := Components( morphism_1 );
        components_2 := Components( morphism_2 );
        
        precomposed_morphisms :=
            List( [ 1 .. nr_support ], n ->
                PreCompose( cat_of_perms, components_1[n], components_2[n] ) );
        
        object := Source( morphism_1 );
        
        return MorphismConstructor( sparse_product,
                    object,
                    NTuple( 3, nr_support, support, precomposed_morphisms ),
                    object );
                    
    end );
    
    AddInverseForMorphisms( sparse_product,
      function( sparse_product, alpha )
        local cat_of_perms, nr_support, support, components, inverse_morphisms;
        
        cat_of_perms := UnderlyingCategoryOfPermutations( sparse_product );
        
        nr_support := NrSupport( alpha );
        support := Support( alpha );
        components := Components( alpha );
        
        inverse_morphisms :=
            List( [ 1 .. nr_support ], i ->
                InverseForMorphisms( cat_of_perms, components[i] ) );
        
        return MorphismConstructor( sparse_product,
                                    Source( alpha ),
                                    NTuple( 3, nr_support, support, inverse_morphisms ),
                                    Target( alpha ) );
        
    end );
    
    ##
    AddDirectProduct( sparse_product,
      function( sparse_product, diagram )
        local cat_of_perms, support, nr_support, sums;
        
        cat_of_perms := UnderlyingCategoryOfPermutations( sparse_product );
        
        support := Union( List( diagram, obj -> Support( obj ) ) );
        
        nr_support := Length( support );
        
        # Due to calling 'Component' below for all support, we might sum over many zeros.
        sums := List( [ 1 .. nr_support ], n ->
            DirectProduct( cat_of_perms, List( diagram, obj -> Component( obj, support[n] ) ) ) );
            
        return ObjectConstructor( sparse_product, NTuple( 3, nr_support, support, sums ) );
        
    end );
    
    ##
    AddDirectProductFunctorialWithGivenDirectProducts( sparse_product,
      function( cat, direct_product_source, source_diagram, morphism_diagram, target_diagram, direct_product_target )
        local cat_of_perms, support, nr_support, products;
        
        cat_of_perms := UnderlyingCategoryOfPermutations( sparse_product );
        
        support := Union( List( morphism_diagram, mor -> Support( mor ) ) );
        
        nr_support := Length( support );
        
        # Due to calling 'Component' below for all supports, we might sum over many zeros.
        products := List( [ 1 .. nr_support ], n ->
            DirectProductFunctorialWithGivenDirectProducts( cat_of_perms,
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
                                [ IsObjectInSparseProductOfCategoryOfPermutations ],
                                
  function( object )
    
    return TripleOfNrSupportListOfSupportListOfObjects( object )[1];
    
end );

InstallMethodForCompilerForCAP( NrSupport,
                                [ IsMorphismInSparseProductOfCategoryOfPermutations ],
                                
  function( morphism )
    
    return TripleOfNrSupportListOfSupportListOfMorphisms( morphism )[1];
    
end );

InstallMethodForCompilerForCAP( Support,
                                [ IsObjectInSparseProductOfCategoryOfPermutations ],
                                
  function( object )
    
    return TripleOfNrSupportListOfSupportListOfObjects( object )[2];
    
end );

InstallMethodForCompilerForCAP( Support,
                                [ IsMorphismInSparseProductOfCategoryOfPermutations ],
                                
  function( morphism )
    
    return TripleOfNrSupportListOfSupportListOfMorphisms( morphism )[2];
    
end );

InstallMethodForCompilerForCAP( Components,
                                [ IsObjectInSparseProductOfCategoryOfPermutations ],
                                
  function( object )
    
    return TripleOfNrSupportListOfSupportListOfObjects( object )[3];
    
end );

InstallMethodForCompilerForCAP( Components,
                                [ IsMorphismInSparseProductOfCategoryOfPermutations ],
                                
  function( morphism )
    
    return TripleOfNrSupportListOfSupportListOfMorphisms( morphism )[3];
    
end );

####################################
##
## Operations
##
####################################

InstallMethodForCompilerForCAP( Component,
                                [ IsObjectInSparseProductOfCategoryOfPermutations, IsBigInt ],
                                
  function( object, i )
    local cat_of_perms, zero, support, objects;
    
    #% CAP_JIT_DROP_NEXT_STATEMENT
    Assert( 0, 1 <= i and i <= NrFactors( CapCategory( object ) ) );
    
    cat_of_perms := UnderlyingCategoryOfPermutations( CapCategory( object ) );
    
    zero := ObjectConstructor( cat_of_perms, 0 );
    
    support := Support( object );
    
    objects := Components( object );
    
    return [ [ zero ], objects{ Positions( support, i ) } ][ 1 + BooleanToInteger( i in support ) ][1];
    
end );

InstallMethodForCompilerForCAP( Component,
                                [ IsMorphismInSparseProductOfCategoryOfPermutations, IsBigInt ],
                                
  function( morphism, i )
    local cat_of_perms, zero, empty_permutation_list, empty_permutation_morphism, support, morphisms;
    
    #% CAP_JIT_DROP_NEXT_STATEMENT
    Assert( 0, 1 <= i and i <= NrFactors( CapCategory( morphism ) ) );
    
    cat_of_perms := UnderlyingCategoryOfPermutations( CapCategory( morphism ) );
    
    zero := ObjectConstructor( cat_of_perms, 0 );
    
    empty_permutation_list := CapJitTypedExpression( [ ], { } -> CapJitDataTypeOfListOf( IsBigInt ) );
    
    empty_permutation_morphism := MorphismConstructor( cat_of_perms, zero, PermList( empty_permutation_list ), zero );
    
    support := Support( morphism );
    
    morphisms := Components( morphism );
    
    return [ [ empty_permutation_morphism ], morphisms{ Positions( support, i ) } ][ 1 + BooleanToInteger( i in support ) ][1];
    
end );

##
InstallMethodForCompilerForCAP( \[\],
                                [ IsObjectInSparseProductOfCategoryOfPermutations, IsInt ],
                                
  function( object, i )
    
    return Component( object, i );
    
end );

##
InstallMethodForCompilerForCAP( \[\],
                                [ IsMorphismInSparseProductOfCategoryOfPermutations, IsInt ],
                                
  function( morphism, i )
    
    return Component( morphism, i );
    
end );

####################################
##
## View & Display
##
####################################

InstallMethod( DisplayString,
               [ IsObjectInSparseProductOfCategoryOfPermutations ],
               
  object -> String( TripleOfNrSupportListOfSupportListOfObjects( object ) )
  
);

InstallMethod( DisplayString,
               [ IsMorphismInSparseProductOfCategoryOfPermutations ],
               
  morphism -> String( TripleOfNrSupportListOfSupportListOfMorphisms( morphism ) )
  
);

##
InstallMethod( Display,
               [ IsMorphismInSparseProductOfCategoryOfPermutations ],
               
  function( morphism )
    local length, support, components, components_source, i, cardinality, permutation;
    
    length := NrSupport( morphism );
    support := Support( morphism );
    components := Components( morphism );
    
    components_source := Components( Source( morphism ) );
    
    for i in [ 1 .. length ] do
        
        cardinality := Cardinality( components_source[i] );
        
        permutation := UnderlyingPermutation( components[i] );
        
        Print( Concatenation( "Component: (", String( support[i] ), ")\n" ) );
        
        Print( "\n" );
        
        Print( cardinality, " ⱶ", String( permutation ), "→ ", cardinality );
        
        Print( "\n------------------------\n" );
        
    od;
    
end );

