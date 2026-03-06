# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Implementations
#

# Read precompiled categories
ReadPackage( "GroupRepresentationsForCAP", "gap/precompiled_categories/CategoryOfInsertionMatrices_precompiled.gi" );

####################################
##
## Constructors
##
####################################

##
InstallMethod( CategoryOfInsertionMatrices,
               [],
               
  FunctionWithNamedArguments(
  [
    [ "overhead", true ],
    [ "no_precompiled_code", false ],
    [ "FinalizeCategory", true ],
  ],
  function( CAP_NAMED_ARGUMENTS )
    local object_datum_type, morphism_datum_type, name, ins_mat, permcat, compare_morphisms, object_datum, object_constructor, morphism_datum, morphism_constructor, F_perms, SubscriptDigits, ToSubscript;
    
    ##
    name := "CategoryOfInsertionMatrices";
    
    ##
    object_datum_type := IsBigInt;
    
    ##
    morphism_datum_type :=
        CapJitDataTypeOfNTupleOf( 2,
            IsBigInt,
            CapJitDataTypeOfListOf(
                CapJitDataTypeOfNTupleOf( 2,
                    IsBigInt,
                    IsBigInt ) ) );
    
    ##
    ins_mat :=
        CreateCapCategoryWithDataTypes(
            name,
            IsCategoryOfInsertionMatrices,
            IsObjectInCategoryOfInsertionMatrices,
            IsMorphismInCategoryOfInsertionMatrices,
            IsCapCategoryTwoCell,
            object_datum_type,
            morphism_datum_type,
            fail
            : overhead := CAP_NAMED_ARGUMENTS.overhead );
    
    ins_mat!.supports_empty_limits := true;
    
    SetIsSkeletalCategory( ins_mat, true );
    
    SetIsCartesianCategory( ins_mat, true );
    
    permcat := PermutationCategory(
                        : overhead := CAP_NAMED_ARGUMENTS.overhead,
                          no_precompiled_code := CAP_NAMED_ARGUMENTS.no_precompiled_code );
    
    SetUnderlyingPermutationCategory( ins_mat, permcat );
    
    ins_mat!.compiler_hints :=
        rec( category_attribute_names :=
            [ "PermutationCategory",
              "IsomorphismFromCoreToPermutationCategory" ] );
    
    # This is a workhorse category -> no logic and caching only via IsIdenticalObj
    CapCategorySwitchLogicOff( ins_mat );
    
    ##
    AddObjectDatum( ins_mat,
      function( ins_mat, object )
        
        return NumberElements( object );
        
    end );
    
    ##
    AddObjectConstructor( ins_mat,
      function( ins_mat, nr_elements )
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, 0 <= nr_elements );
        
        return CreateCapCategoryObjectWithAttributes( ins_mat,
                       NumberElements, nr_elements );
                       
    end );
    
    ##
    AddMorphismDatum( ins_mat,
      function( ins_mat, morphism )
        
        return NrBlockColumnsAndListOfBlockColumns( morphism );
        
    end );
    
    ##
    AddMorphismConstructor( ins_mat,
      function( ins_mat, S, nr_blockcols_list_of_blockcolumns, T )
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, nr_blockcols_list_of_blockcolumns[1] = Length( nr_blockcols_list_of_blockcolumns[2] ) );
                
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( nr_blockcols_list_of_blockcolumns[2], col -> 1 <= col[1] and 1 <= col[2] ) );
                
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( nr_blockcols_list_of_blockcolumns[2], col -> col[1] <= col[2] ) );
        
        # S must "give" enough rows.
        #                                       ┌           ┐
        #                                       │0 0 0 ┆ 0 0│
        #                                       │1 0 0 ┆ 0 0│
        # Example: [ 6, [ [1,3], [3,4] ], 5 ] ≙ │0 1 0 ┆ 0 0│
        #                                       │0 0 1 ┆ 1 0│
        #                                       │0 0 0 ┆ 0 1│
        #                                       │0 0 0 ┆ 0 0│
        #                                       └           ┘
        #
        # So S must be greater or equal to 4 = Max( 1, 3, 4 ).
        #
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0,
            ForAll( nr_blockcols_list_of_blockcolumns[2], pair ->
                pair[1] <= NumberElements( S ) and
                pair[2] <= NumberElements( S ) ) );
                
        # T must match the number of columns.
        #
        #                                       ┌           ┐
        #                                       │0 0 0 ┆ 0 0│
        #                                       │1 0 0 ┆ 0 0│
        # Example: [ 6, [ [1,3], [3,4] ], 5 ] ≙ │0 1 0 ┆ 0 0│
        #                                       │0 0 1 ┆ 1 0│
        #                                       │0 0 0 ┆ 0 1│
        #                                       │0 0 0 ┆ 0 0│
        #                                       └           ┘
        #
        # So the we get [3-1+1]+[4-3+1] = 5 columns.
        #
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, NumberElements( T ) = Sum( List( nr_blockcols_list_of_blockcolumns[2], col -> col[2] - col[1] + 1 ) ) );
        
        return CreateCapCategoryMorphismWithAttributes(
                    ins_mat,
                    S,
                    T,
                    NrBlockColumnsAndListOfBlockColumns, nr_blockcols_list_of_blockcolumns );
                    
    end );
    
    ##
    AddIsWellDefinedForObjects( ins_mat,
      function( ins_mat, object )
        
        return 0 <= NumberElements( object );
        
    end );
    
    ##
    # AddIsWellDefinedForMorphismsWithGivenSourceAndRange( ins_mat,
      # function( ins_mat, source, morphism, target )
    AddIsWellDefinedForMorphisms( ins_mat,
      function( ins_mat, morphism )
        local nr_blockcols, blockcols, source, target, nr_elements_source;
        
        nr_blockcols := NrBlockColumns( morphism );
        blockcols := ListOfBlockColumns( morphism );
        
        source := Source( morphism );
        target := Target( morphism );
        
        nr_elements_source := NumberElements( source );
        
        if not nr_blockcols = Length( blockcols ) then
            
            return fail;
            
        elif not ForAll( [ 1 .. nr_blockcols ], i -> 1 <= blockcols[i][1] and 1 <= blockcols[i][2] ) then
            
            return false;
            
        elif not ForAll( [ 1 .. nr_blockcols ], i -> blockcols[i][1] <= blockcols[i][2] ) then
            
            return false;
            
        elif not ForAll( [ 1 .. nr_blockcols ], i ->
            blockcols[i][1] <= nr_elements_source and
            blockcols[i][2] <= nr_elements_source )
        then
            
            return false;
            
        elif not NumberElements( target ) = Sum( List( [ 1 .. nr_blockcols ], i -> blockcols[i][2] - blockcols[i][1] + 1 ) ) then
            
            return false;
            
        else
            
            return true;
            
        fi;
        
    end );
    
    ##
    AddIsEqualForObjects( ins_mat,
      function( ins_mat, object_1, object_2 )
        
        return NumberElements( object_1 ) = NumberElements( object_2 );
        
    end );
    
    ##
    AddIsEqualForMorphisms( ins_mat,
      function( ins_mat, morphism_1, morphism_2 )
        
        return NrBlockColumnsAndListOfBlockColumns( morphism_1 ) = NrBlockColumnsAndListOfBlockColumns( morphism_2 );
        
    end );
    
    ##
    AddIsCongruentForMorphisms( ins_mat,
      function( ins_mat, morphism_1, morphism_2 )
        local simplified_morphism_1, simplified_morphism_2;
        
        simplified_morphism_1 := SimplifyMorphism( morphism_1, 2 );
        simplified_morphism_2 := SimplifyMorphism( morphism_2, 2 );
        
        return IsEqualForMorphisms( simplified_morphism_1, simplified_morphism_2 );
        
    end );
    
    AddSimplifyMorphism( ins_mat,
      function( ins_mat, phi, i )
        local nr_blockcols, blockcols, merge_consecutive_pairs, simplified_list_of_columns;
        
        nr_blockcols := NrBlockColumns( phi );
        blockcols := ListOfBlockColumns( phi );
        
        if nr_blockcols = 0 then
            
            return phi;
            
        else
            
            merge_consecutive_pairs :=
                function( accumulator, next_pair )
                    local previous_pair;
                    
                    previous_pair := Last( accumulator );
                    
                    # Two consecutive pairs [[n-1, n], [n+1, m]] become [[n-1, m]].
                    if next_pair[1] = previous_pair[2] + 1 then
                        
                        return Concatenation( accumulator{[ 1 .. Length( accumulator ) - 1 ]},
                                              [ [ previous_pair[1], next_pair[2] ] ] );
                        
                    else
                        
                        return Concatenation( accumulator, [ next_pair ] );
                        
                    fi;
                    
                end;
                
            simplified_list_of_columns :=
                Iterated(
                    blockcols{[ 2 .. nr_blockcols ]},
                    merge_consecutive_pairs,
                    [ blockcols[1] ] );
            
            return MorphismConstructor( ins_mat,
                        Source( phi ),
                        Pair( Length( simplified_list_of_columns ), simplified_list_of_columns ),
                        Target( phi ) );
            
        fi;
        
    end );
    
    ##
    AddIdentityMorphism( ins_mat,
      function( ins_mat, object )
        local nr_elements, datum;
        
        nr_elements := NumberElements( object );
        
        datum := [
            Pair( BigInt( 1 ), [ Pair( BigInt( 1 ), nr_elements ) ] ),
            Pair( BigInt( 0 ), CapJitTypedExpression( [ ], { } ->
                CapJitDataTypeOfListOf( CapJitDataTypeOfNTupleOf( 2, IsBigInt, IsBigInt ) ) ) ) ];
                
        datum := datum[ 1 + BooleanToInteger( nr_elements = 0 ) ];
        
        return MorphismConstructor( ins_mat, object, datum, object );
        
    end );
    
    ##
    AddPreCompose( ins_mat,
      function( ins_mat, morphism_1, morphism_2 )
        
        
        
    end );
    
    ##
    AddTerminalObject( ins_mat,
      function( ins_mat )
        
        return ObjectConstructor( ins_mat, BigInt( 0 ) );
        
    end );
    
    ##
    AddIsTerminal( ins_mat,
      function( ins_mat, object )
        
        return NumberElements( object ) = BigInt( 0 );
        
    end );
    
    ##
    AddUniversalMorphismIntoTerminalObjectWithGivenTerminalObject( ins_mat,
      function( ins_mat, object, t )
        
        return MorphismConstructor( ins_mat,
                    object,
                    Pair( BigInt( 0 ), CapJitTypedExpression( [ ], { } -> CapJitDataTypeOfListOf( CapJitDataTypeOfNTupleOf( 2, IsBigInt, IsBigInt ) ) ) ),
                    t );
                    
    end );
    
    ##
    AddDirectProduct( ins_mat,
      function( ins_mat, objects )
        local nr_objects, sum;
        
        nr_objects := Length( objects );
        
        sum := Sum( List( [ 1 .. nr_objects ], i -> NumberElements( objects[i] ) ) );
        
        return ObjectConstructor( ins_mat, sum );
        
    end );
    
    ##
    AddProjectionInFactorOfDirectProductWithGivenDirectProduct( ins_mat,
      function( ins_mat, objects, projection_number, direct_product )
        local dim_pre, dim_post, dim_factor, datum;
        
        dim_pre := Sum( List( objects{ [ 1 .. projection_number - 1 ] }, c -> NumberElements( c ) ) );
        
        dim_post := Sum( List( objects{ [ projection_number + 1 .. Length( objects ) ] }, c -> NumberElements( c ) ) );
        
        dim_factor := NumberElements( objects[ projection_number ] );
        
        datum := [ Pair( BigInt( 1 ), [ Pair( dim_pre + 1, dim_pre + dim_factor ) ] ),
                   Pair( BigInt( 0 ), CapJitTypedExpression( [ ], { } -> CapJitDataTypeOfListOf( CapJitDataTypeOfNTupleOf( 2, IsBigInt, IsBigInt ) ) ) ) ];
        
        datum := datum[ 1 + BooleanToInteger( dim_factor = 0 ) ];
        
        return MorphismConstructor( ins_mat, direct_product, datum, objects[ projection_number ] );
        
    end );
    
    ##
    AddUniversalMorphismIntoDirectProductWithGivenDirectProduct( ins_mat,
      function( ins_mat, target_diagram, test_object, morphisms, product )
        local nr_morphisms, nr_blockcols, blockcols;
        
        nr_morphisms := Length( morphisms );
        
        nr_blockcols := Sum( List( [ 1 .. nr_morphisms ], i -> NrBlockColumns( morphisms[i] ) ) );
        
        blockcols := Concatenation( List( [ 1 .. nr_morphisms ], i -> ListOfBlockColumns( morphisms[i] ) ) );
        
        return MorphismConstructor( ins_mat, test_object, Pair( nr_blockcols, blockcols ), product );
        
    end );
    
    ##
    AddDirectProductFunctorialWithGivenDirectProducts( ins_mat,
      function( ins_mat, source, source_diagram, morphisms, target_diagram, target )
        local nr_morphisms, nr_blockcols, blockcols;
        
        nr_morphisms := Length( morphisms );
        
        nr_blockcols := Sum( List( [ 1 .. nr_morphisms ], i -> NrBlockColumns( morphisms[i] ) ) );
        
        # TODO: example
        blockcols :=
            Concatenation( List( [ 1 .. nr_morphisms ], function( i )
                local offset;
                
                offset := Sum( List( [ 1 .. i - 1 ], j -> NumberElements( source_diagram[j] ) ) );
                
                return List( ListOfBlockColumns( morphisms[i] ), col ->
                            Pair( col[1] + offset, col[2] + offset ) );
                
            end ) );
            
        return MorphismConstructor( ins_mat, source, Pair( nr_blockcols, blockcols ), target );
        
    end );
    
    AddTensorUnit( ins_mat,
      function( ins_mat )
        
        return ObjectConstructor( ins_mat, BigInt( 1 ) );
        
    end );
    
    AddLeftUnitorWithGivenTensorProduct( ins_mat,
      function( ins_mat, object, tensor_product )
        
        return IdentityMorphism( ins_mat, object );
        
    end );
    
    AddRightUnitorWithGivenTensorProduct( ins_mat,
      function( ins_mat, object, tensor_product )
        
        return IdentityMorphism( ins_mat, object );
        
    end );
    
    ##
    AddTensorProductOnObjects( ins_mat,
      function( ins_mat, a, b )
        local product;
        
        product :=  NumberElements( a ) * NumberElements( b );
        
        return ObjectConstructor( ins_mat, product );
        
    end );
    
    ##
    AddTensorProductOnMorphismsWithGivenTensorProducts( ins_mat,
      function( ins_mat, source, alpha, beta, target )
        local alpha_blockcols, alpha_nr_cols, alpha_nr_blockcols, beta_blockcols, beta_nr_blockcols, beta_nr_rows, nr_blockcols, tensored_blockcols;
        
        alpha_nr_blockcols := NrBlockColumns( alpha );
        alpha_nr_cols := NumberElements( Target( alpha ) );
        alpha_blockcols := ListOfBlockColumns( alpha );
        
        beta_nr_blockcols := NrBlockColumns( beta );
        beta_blockcols := ListOfBlockColumns( beta );
        beta_nr_rows := NumberElements( Source( beta ) );
        
        # TODO: example
        nr_blockcols :=
            Sum( List( [ 1 .. alpha_nr_blockcols ], i ->
                 alpha_blockcols[i][2] - alpha_blockcols[i][1] + BigInt( 1 ) ) ) *
            beta_nr_blockcols;
        
        tensored_blockcols :=
            Concatenation( List( [ 1 .. alpha_nr_blockcols ], i ->
                Concatenation( List( [ alpha_blockcols[i][1] .. alpha_blockcols[i][2] ], j ->
                    List( [ 1 .. beta_nr_blockcols ], k ->
                        Pair( beta_blockcols[k][1] + ( beta_nr_rows * (j-1) ),
                              beta_blockcols[k][2] + ( beta_nr_rows * (j-1) ) ) ) ) ) ) );
        
        return MorphismConstructor( ins_mat, source, Pair( nr_blockcols, tensored_blockcols ), target );
        
    end );
    
    F_perms := CapFunctor( Concatenation( "Functor from ", Name( ins_mat ), " to ", Name( permcat ) ),
                           ins_mat,
                           permcat );
    
    AddObjectFunction( F_perms,
      function( object )
        local permcat;
        
        permcat := UnderlyingPermutationCategory( CapCategory( object ) );
        
        return ObjectConstructor( permcat, NumberElements( object ) );
        
    end );
    
    AddMorphismFunction( F_perms,
      function( source, morphism, target )
        local permcat, nr_blockcols, blockcols, list_perm, permutation;
        
        permcat := UnderlyingPermutationCategory( CapCategory( morphism ) );
        
        # `morphism` must be an isomorphism.
        Assert( 0, IsEqualForObjects( permcat, source, target ) );
        
        nr_blockcols := NrBlockColumns( morphism );
        blockcols := ListOfBlockColumns( morphism );
        
        list_perm := List( [ 1 .. nr_blockcols ], function( i )
            local blockcol;
            
            blockcol := blockcols[i];
            
            # Example: if blockcol[i] = [ a, a ] then return [ a ],
            #          if blockcol[i] = [ a, b ] then return [ a .. b ].
            return [ [ blockcol[1] .. blockcol[2] ], [ blockcol[1] ] ][ BooleanToInteger( blockcol[1] = blockcol[2] ) + 1 ];
            
        end );
        
        permutation := PermList( Concatenation( list_perm ) );
        
        return MorphismConstructor( permcat, source, permutation, target );
        
    end );
    
    SetIsomorphismFromCoreToPermutationCategory( ins_mat, F_perms );
    
    if CAP_NAMED_ARGUMENTS.no_precompiled_code <> true then
        
        ADD_FUNCTIONS_FOR_CategoryOfInsertionMatrices_precompiled( ins_mat );
        
    fi;
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        
        Finalize( ins_mat );
        
    fi;
    
    return ins_mat;
    
end ) );

####################################
##
## Attributes
##
####################################

InstallMethodForCompilerForCAP( NrBlockColumns,
                                [ IsMorphismInCategoryOfInsertionMatrices ],
                                
  function( morphism )
    
    return NrBlockColumnsAndListOfBlockColumns( morphism )[1];
    
end );

InstallMethodForCompilerForCAP( ListOfBlockColumns,
                                [ IsMorphismInCategoryOfInsertionMatrices ],
                                
  function( morphism )
    
    return NrBlockColumnsAndListOfBlockColumns( morphism )[2];
    
end );

####################################
##
## Functors
##
####################################

##
InstallMethod( FunctorInsertionMatricesToCategoryOfRows,
               [ IsCapCategory, IsCapCategory ],
               
  function( ins_mat, rows )
    local homalg_ring, functor;
    
    Assert( 0, IsCategoryOfRows( rows) );
    
    homalg_ring := UnderlyingRing( rows );
    
    functor := CapFunctor( Concatenation( "Functor from ", Name( ins_mat ), " to ", Name( rows ) ), ins_mat, rows );
    
    AddObjectFunction( functor,
      function( object )
        
        return ObjectConstructor( rows, NumberElements( object ) );
        
    end );
    
    AddMorphismFunction( functor,
      function( source, morphism, target )
        local nr_rows, nr_cols, block_cols, matrix;
        
        nr_rows := RankOfObject( source );
        nr_cols := RankOfObject( target );
        
        block_cols := ListOfBlockColumns( morphism );
        
        # Blocks are of the form:
        # ┌   ┐
        # │0ₘₙ│
        # │1ₙ │
        # │0ₗₙ│
        # └   ┘
        block_cols := List( block_cols, function( block )
            local cols;
            
            cols := block[2] - block[1] + 1;
            
            return UnionOfRows( homalg_ring, cols, [
                         HomalgZeroMatrix( block[1] - 1, cols, homalg_ring ),
                         HomalgIdentityMatrix( cols, homalg_ring ),
                         HomalgZeroMatrix( nr_rows - block[2], cols, homalg_ring ) ] );
                         
        end );
        
        matrix := UnionOfColumns( homalg_ring, nr_rows, block_cols );
        
        return AsCategoryOfRowsMorphism( rows, matrix );
        
    end );
    
    return functor;
    
end );

####################################
##
## Global functions
##
####################################

## TODO: turn this into a CAP operation?
InstallGlobalFunction( CATEGORY_OF_INSERTION_MATRICES_TensorProductOfMorphismWithIdentityWithGivenTensorProducts,
  function( ins_mat, source, morphism, id, target )
    local morphism_nr_blockcols, morphism_nr_cols, morphism_blockcols, id_nr_blockcols, id_blockcols, id_nr_rows, nr_blockcols, tensored_blockcols;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    morphism_nr_blockcols := NrBlockColumns( morphism );
    morphism_nr_cols := NumberElements( Target( morphism ) );
    morphism_blockcols := ListOfBlockColumns( morphism );
    
    id_nr_blockcols := NrBlockColumns( id );
    id_blockcols := ListOfBlockColumns( id );
    id_nr_rows := NumberElements( Source( id ) );
    
    # We assume that the identity morphism <id> is normalized.
    Assert( 0, id_nr_blockcols <= 1 );
    
    
    # The Kronecker product of a matrix `m` with an identity matrix
    # diagonally duplicates the block-columns of `m`.
    #
    #                         ┌                          ┐
    #                         │             ┌────┐       │
    #                         │  0·I₃  0·I₃ │1·I₃│ 0·I₃  │
    #                         │             └────┘       │
    #  ┌       ┐              │                   ┌────┐ │
    #  │0 0 1 0│   ┌     ┐    │  0·I₃  0·I₃  0·I₃ │1·I₃│ │
    #  │0 0 0 1│   │1 0 0│    │                   └────┘ │
    #  │1 0 0 0│ ⨂ │0 1 0│  = │ ┌────┐                   │
    #  │0 1 0 0│   │0 0 1│    │ │1·I₃│ 0·I₃  0·I₃ 0·I₃   │
    #  │0 0 0 0│   └     ┘    │ └────┘                   │
    #  └       ┘              │       ┌────┐             │
    #                         │ 0·I₃  │1·I₃│ 0·I₃ 0·I₃   │
    #                         │       └────┘             │
    #                         │ 0·I₃   0·I₃  0·I₃ 0·I₃   │
    #                         └                          ┘
    #
    #                         ┌                                                ┐
    #                         │  0,  0,  0,  0,  0,  0,  1,  0,  0,  0,  0,  0 │
    #                         │  0,  0,  0,  0,  0,  0,  0,  1,  0,  0,  0,  0 │
    #                         │  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0,  0 │
    #                         │  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0,  0 │
    #                         │  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1,  0 │
    #                         │  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  1 │
    #                      =  │  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 │
    #                         │  0,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 │
    #                         │  0,  0,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0 │
    #                         │  0,  0,  0,  1,  0,  0,  0,  0,  0,  0,  0,  0 │
    #                         │  0,  0,  0,  0,  1,  0,  0,  0,  0,  0,  0,  0 │
    #                         │  0,  0,  0,  0,  0,  1,  0,  0,  0,  0,  0,  0 │
    #                         │  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 │
    #                         │  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 │
    #                         │  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0 │
    #                         └                                                ┘
    #
    # Example: morphism_blockcols = [ [ 3, 4 ], [ 1, 2 ] ]
    #                id_blockcols = [ [ 1, 3 ] ]
    #
    # So we return
    #
    # [ [ 7, 12 ]   = [ [ 1 + (3*(3-1)), 3 + (3*(4-1)) ],
    #   [ 1, 6  ] ] =   [ 1 + (3*(1-1)), 3 + (3*(2-1)) ] ]
    tensored_blockcols :=
        Concatenation( List( [ 1 .. id_nr_blockcols ], n ->
            List( [ 1 .. morphism_nr_blockcols ], i ->
                Pair( id_blockcols[n][1] + ( id_nr_rows * ( morphism_blockcols[i][1] - 1 ) ),
                      id_blockcols[n][2] + ( id_nr_rows * ( morphism_blockcols[i][2] - 1 ) ) ) ) ) );
    
    return MorphismConstructor( ins_mat,
                source,
                Pair( morphism_nr_blockcols * id_nr_blockcols, tensored_blockcols ),
                target );
    
end );

## TODO: turn this into a CAP operation?
InstallGlobalFunction( CATEGORY_OF_INSERTION_MATRICES_TensorProductOfIdentityWithMorphismWithGivenTensorProducts,
  function( ins_mat, source, id, morphism, target )
    local morphism_nr_blockcols, morphism_nr_rows, morphism_nr_cols, morphism_blockcols, id_nr_blockcols, id_blockcols, id_nr_rows, nr_blockcols, blockcols;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    morphism_nr_blockcols := NrBlockColumns( morphism );
    morphism_nr_rows := NumberElements( Source( morphism ) );
    morphism_nr_cols := NumberElements( Target( morphism ) );
    morphism_blockcols := ListOfBlockColumns( morphism );
    
    id_nr_blockcols := NrBlockColumns( id );
    id_blockcols := ListOfBlockColumns( id );
    id_nr_rows := NumberElements( Source( id ) );
    
    # We assume that the identity morphism <id> is normalized.
    Assert( 0, id_nr_blockcols <= 1 );
    
    # The Kronecker product of an identity matrix with a matrix `m`
    # yields a block-diagonal matrix whose blocks are `m`
    # and whose number of blocks is equal to the number of
    # rows of the identity matrix.
    # I.e., it is a specialized DirectProductFunctorial.
    #
    #                        ┌                        ┐
    #                        │0 0 1 0                 │
    #                        │0 0 0 1                 │
    #                        │1 0 0 0                 │
    #            ┌       ┐   │0 1 0 0                 │
    #  ┌     ┐   │0 0 1 0│   │0 0 0 0                 │
    #  │1 0 0│   │0 0 0 1│   │        0 0 1 0         │
    #  │0 1 0│ ⨂ │1 0 0 0│ = │        0 0 0 1         │
    #  │0 0 1│   │0 1 0 0│   │        1 0 0 0         │
    #  └     ┘   │0 0 0 0│   │        0 1 0 0         │
    #            └       ┘   │        0 0 0 0         │
    #                        │                0 0 1 0 │
    #                        │                0 0 0 1 │
    #                        │                1 0 0 0 │
    #                        │                0 1 0 0 │
    #                        │                0 0 0 0 │
    #                        └                        ┘
    
    blockcols := Concatenation( List( [ 1 .. id_nr_rows ], function( i )
        local offset;
        
        offset := Sum( List( [ 1 .. i - 1 ], j -> morphism_nr_rows ) );
        
        return List( morphism_blockcols, col ->
                    Pair( col[1] + offset, col[2] + offset ) );
        
    end ) );

    nr_blockcols := id_nr_rows * morphism_nr_blockcols;
    
    return MorphismConstructor( ins_mat, source, Pair( nr_blockcols, blockcols ), target );
    
end );

InstallGlobalFunction( CATEGORY_OF_INSERTION_MATRICES_RowDownwardShift,
  function( ins_mat, morphism, shift_size )
    local nr_blockcols, block_cols, shifted_blocks;
    
    #% CAP_JIT_RESOLVE_FUNCTION
    
    nr_blockcols := NrBlockColumns( morphism );
    block_cols := ListOfBlockColumns( morphism );
    
    shifted_blocks := List( [ 1 .. nr_blockcols ], function( i )
        local block_size, shifted_block_start, shifted_block;
        
        block_size := block_cols[i][2] - block_cols[i][1] + 1;
        
        shifted_block_start := block_cols[i][1] + block_size + ( block_size * ( shift_size - 1 ) );
        
        shifted_block := Pair( shifted_block_start, shifted_block_start + block_size - 1 );
        
        return shifted_block;
        
    end );
    
    return MorphismConstructor( ins_mat,
                                Source( morphism ),
                                Pair( nr_blockcols, shifted_blocks ),
                                Target( morphism ) );
    
end );

####################################
##
## View & Display
##
####################################

InstallMethod( DisplayString,
               [ IsObjectInCategoryOfInsertionMatrices ],
               
  object -> String( NumberElements( object ) )
  
);

InstallMethod( DisplayString,
               [ IsMorphismInCategoryOfInsertionMatrices ],
               
  object -> String( NrBlockColumnsAndListOfBlockColumns( object ) )
  
);

