# SPDX-License-Identifier: GPL-2.0-or-later
# AdditiveClosuresForCAP: Additive closures for pre-abelian categories
#
# Implementations
#

####################################
##
## Constructors
##
####################################

##
InstallMethod( CoproductOfCategoryOfRowsWithSparseDatastructure,
               [ IsCategoryOfRows, IsInt ],
               
  FunctionWithNamedArguments(
  [
    [ "FinalizeCategory", true ],
  ],
  function( CAP_NAMED_ARGUMENTS, Rows, nr_summands )
    local homalg_ring, D, L, AC_disc, object_datum_type, object_datum, object_constructor, morphism_datum, morphism_datum_type, morphism_constructor, modeling_tower_object_constructor, modeling_tower_object_datum, modeling_tower_morphism_constructor, modeling_tower_morphism_datum, SubscriptDigits, ToSubscript, name, Coproduct;
    
    Assert( 0, nr_summands > 0 );
    
    homalg_ring := UnderlyingRing( Rows );
    
    if nr_summands = 1 then
        
        return Rows;
        
    fi;
    
    D := FiniteSkeletalDiscreteCategory( [ 1 .. nr_summands ] : FinalizeCategory := true );
    
    L := LinearClosure( homalg_ring, D : FinalizeCategory := true );
    
    AC_disc := AdditiveClosureOfObjectFiniteDisconnectedCategory( L : FinalizeCategory := false );
    
    Finalize( AC_disc );
    
    ####################################
    # Reinterpretation
    ####################################
    
    ##
    object_datum_type :=
        CapJitDataTypeOfListOf(
            CapJitDataTypeOfNTupleOf( 2,
                CapJitDataTypeOfObjectOfCategory( Rows ),
                IsBigInt ) );
    
    ##
    object_datum := { coproduct, obj } -> ListOfPairsOfObjectAndIndex( obj );
    
    ##
    object_constructor :=
      function( coproduct, list_of_pairs_of_object_and_index )
        
        # For all pairs [ RowsMorphism, index ] the 'index' must be
        # between 1 and NrOfSummandsOfCoproduct( coproduct ).
        Assert( 0, ForAll( list_of_pairs_of_object_and_index, pair ->
            1 <= pair[2] and pair[2] <= NrOfSummandsOfCoproduct( coproduct ) ) );
        
        # For all pairs [ RowsMorphism, index ] the 'index' must be strictly increasing.
        Assert( 0, ForAll( [ 1 .. Length( list_of_pairs_of_object_and_index ) - 1 ], i ->
            list_of_pairs_of_object_and_index[i][2] < list_of_pairs_of_object_and_index[i+1][2] ) );
        
        return CreateCapCategoryObjectWithAttributes( coproduct,
                       ListOfPairsOfObjectAndIndex, list_of_pairs_of_object_and_index );
        
    end;
    
    ##
    morphism_datum_type :=
        CapJitDataTypeOfListOf(
            CapJitDataTypeOfNTupleOf( 2,
                CapJitDataTypeOfMorphismOfCategory( Rows ),
                IsBigInt ) );
    
    ##
    morphism_datum := { coproduct, phi } -> ListOfPairsOfMorphismAndIndex( phi );
    
    ##
    morphism_constructor :=
      function( coproduct, S, list_of_pairs_of_morphism_and_index, T )
        
        # For all pairs [ RowsMorphism, index ] the 'index' must be
        # between 1 and NrOfSummandsOfCoproduct( coproduct ).
        Assert( 0, ForAll( list_of_pairs_of_morphism_and_index, pair ->
            1 <= pair[2] and pair[2] <= NrOfSummandsOfCoproduct( coproduct ) ) );
        
        # For all pairs [ RowsMorphism, index ] the 'index' must be strictly increasing.
        Assert( 0, ForAll( [ 1 .. Length( list_of_pairs_of_morphism_and_index ) - 1 ], i ->
            list_of_pairs_of_morphism_and_index[i][2] < list_of_pairs_of_morphism_and_index[i+1][2] ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        CAP_INTERNAL_coproduct_morphism_constructor_sanity_check( coproduct, S, list_of_pairs_of_morphism_and_index, T );
        
        return CreateCapCategoryMorphismWithAttributes(
                    coproduct,
                    S,
                    T,
                    ListOfPairsOfMorphismAndIndex, list_of_pairs_of_morphism_and_index );
        
    end;
    
    ####################################
    # Modeling
    ####################################
    
    ## From the raw object data to the object in the modeling category.
    modeling_tower_object_constructor :=
      function( coproduct, list_of_pairs_of_object_and_index )
        local AC_disc, multiplicities;
        
        AC_disc := ModelingCategory( coproduct );
        
        multiplicities :=
            CAP_INTERNAL_coproduct_sparse_object_list_to_dense_list( coproduct, list_of_pairs_of_object_and_index );
        
        return ObjectConstructor( AC_disc, [ Sum( multiplicities ), multiplicities ] );
        
    end;
    
    ## From the object in the modeling category to the raw object data.
    modeling_tower_object_datum :=
      function( coproduct, object )
        local multiplicities, list_of_pairs_of_object_and_index;
        
        multiplicities := Multiplicities( object );
        
        list_of_pairs_of_object_and_index :=
            CAP_INTERNAL_coproduct_dense_object_list_to_sparse_list( coproduct, multiplicities );
        
        return list_of_pairs_of_object_and_index;
        
    end;
    
    ## From the raw morphism data to the morphism in the modeling category.
    modeling_tower_morphism_constructor :=
      function( coproduct, S, list_of_pairs_of_morphism_and_index, T )
        local AC_disc, L, D, underlying_disconnected_objects, pairs_listlist_with_index, pair, row, obj_D, obj_L, id_obj_D, nr_matrices, dense_list_of_matrices;
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( list_of_pairs_of_morphism_and_index, pair ->
            RankOfObject( Source( pair[1] ) ) = Multiplicities( S )[ pair[2] ] ) );

        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( list_of_pairs_of_morphism_and_index, pair ->
            RankOfObject( Target( pair[1] ) ) = Multiplicities( T )[ pair[2] ] ) );
        
        AC_disc := ModelingCategory( coproduct );
        
        L := UnderlyingCategory( AC_disc );
        
        D := UnderlyingCategory( L );
        
        underlying_disconnected_objects := SetOfObjectsOfCategory( D );
        
        # Turn all Homalg matrices into listlist's.
        pairs_listlist_with_index :=
            List( list_of_pairs_of_morphism_and_index, pair ->
                [ EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair[1] ) ), pair[2] ] );
        
        # For all matrices as listlist's turn the entries 'c' into coefficients: c*IdentityMorphism.
        pairs_listlist_with_index :=
            List( pairs_listlist_with_index, pair ->
                [ List( pair[1], row ->
                    List( row,
                        function( c )
                            obj_D := underlying_disconnected_objects[ pair[2] ];
                            
                            id_obj_D := IdentityMorphism( D, obj_D );
                            
                            obj_L := LinearClosureObject( L, obj_D );
                            
                            return LinearClosureMorphismNC( L, obj_L, [ c ], [ id_obj_D ], obj_L );
                            
                        end ) ),
                  pair[2] ] );
        
        dense_list_of_matrices := CAP_INTERNAL_coproduct_sparse_matrices_list_to_dense_list( coproduct, pairs_listlist_with_index );
        
        nr_matrices := NrOfSummandsOfCoproduct( coproduct );
        
        # Replace the entries for empty matrices of the form nx0, with n > 0,
        # from [ ] to [ [], [], ..., [] ] in 'dense_list'.
        # This is required by the modeling additive closure
        # to represent nx0 matrices.
        dense_list_of_matrices :=
            List( [ 1 .. nr_matrices ],
                function( i )
                    local nr_rows, nr_cols;
                    
                    nr_rows := Multiplicities( S )[i];
                    nr_cols := Multiplicities( T )[i];
                    
                    # Check if we have an nx0 matrix.
                    if  nr_rows > 0 and nr_cols = 0 then
                        
                        # Return an nx0 matrix.
                        return ListWithIdenticalEntries( nr_rows, [] );
                        
                    fi;
                    
                    # We do not need to care about 0xn matrices,
                    # since these have the form '[ ]',
                    # and this is already the case by construction of 'dense_list_of_matrices'.
                    
                    return dense_list_of_matrices[i];
                    
        end );
        
        # Check that all matrices as listlist's still have the correct dimensions.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0,
            ForAllWithKeys( dense_list_of_matrices, { i, matrix } ->
                Length( matrix ) = Multiplicities( S )[i] and
                ForAll( matrix, row -> Length( row ) = Multiplicities( T )[i] ) ) );
        
        return MorphismConstructor( AC_disc, S, dense_list_of_matrices, T );
        
    end;
    
    # From the morphism in the modeling category to the raw morphism data.
    modeling_tower_morphism_datum :=
      function ( coproduct, morphism )
        local Rows, underlying_ring, source_multiplicities, target_multiplicities, sparse_list, list_of_pairs_of_morphism_and_index;
        
        Rows := UnderlyingCategoryOfRows( coproduct );
        
        underlying_ring := UnderlyingRing( coproduct );
        
        source_multiplicities := Multiplicities( Source( morphism ) );
        target_multiplicities := Multiplicities( Target( morphism ) );
        
        sparse_list := CAP_INTERNAL_coproduct_dense_matrices_list_to_sparse_list( coproduct, ListOfMatrices( morphism ) );
        
        # For each pair, convert the matrix into a morphism in the category of rows.
        list_of_pairs_of_morphism_and_index :=
            List( sparse_list,
                function( pair )
                    local matrix, nr_rows, nr_cols, homalg_matrix, morphism;
                    
                    matrix := pair[1];
                    
                    # All entries are of the form: c_1*IdentityMorphism( L, i ) + ... + c_n*IdentityMorphism( L, i )
                    # with the same identity morphism.
                    # Because LinearClosure has a lazy datastructure, we need to sum over all the coefficients c_i ourself.
                    matrix :=
                        List( matrix,
                            row -> List( row, entry -> Sum( CoefficientsList( entry ) ) ) );
                    
                    nr_rows := source_multiplicities[ pair[2] ];
                    nr_cols := target_multiplicities[ pair[2] ];
                    
                    homalg_matrix := HomalgMatrixListList( matrix,
                                                           nr_rows,
                                                           nr_cols,
                                                           underlying_ring );
                    
                    morphism := CategoryOfRowsMorphism( CategoryOfRowsObject( Rows, nr_rows ),
                                                        homalg_matrix,
                                                        CategoryOfRowsObject( Rows, nr_cols ) );
                    
                    return [ morphism, pair[2] ];
                    
        end );
        
        return list_of_pairs_of_morphism_and_index;
        
    end;
    
    name := Concatenation( "⊕ ( ", "CategoryOfRows( ", RingName( homalg_ring ), " ), ", String( nr_summands ), " )" );
    
    Coproduct :=
        ReinterpretationOfCategory( AC_disc,
            rec( name := name,
                 category_filter := IsCoproductOfCategoryOfRowsWithSparseDatastructure,
                 category_object_filter := IsObjectInCoproductOfCategoryOfRowsWithSparseDatastructure,
                 category_morphism_filter := IsMorphismInCoproductOfCategoryOfRowsWithSparseDatastructure,
                 object_constructor := object_constructor,
                 object_datum := object_datum,
                 morphism_constructor := morphism_constructor,
                 morphism_datum := morphism_datum,
                 modeling_tower_object_constructor := modeling_tower_object_constructor,
                 modeling_tower_object_datum := modeling_tower_object_datum,
                 modeling_tower_morphism_constructor := modeling_tower_morphism_constructor,
                 modeling_tower_morphism_datum := modeling_tower_morphism_datum,
                 only_primitive_operations := true, )
            : FinalizeCategory := false );
    
    if IsFieldForHomalg( homalg_ring ) then
        
        SetIsAbelianCategory( Coproduct, true );
        
    fi;
    
    SetUnderlyingRing( Coproduct, homalg_ring );
    
    SetNrOfSummandsOfCoproduct( Coproduct, nr_summands );
    
    SetUnderlyingCategoryOfRows( Coproduct, Rows );
    
    Coproduct!.compiler_hints.category_attribute_names := [
        "UnderlyingRing",
        "NrOfSummandsOfCoproduct",
        "UnderlyingCategoryOfRows",
    ];
    
    # Coproduct!.compiler_hints.source_and_range_attributes_from_morphism_attribute := rec(
    #     object_attribute_name := "SumOfRanksAndRanks",
    #     morphism_attribute_name := "ListOfMatrices",
    # );
    
    ####################################
    ## Abelian structure
    ####################################
    
    if IsFieldForHomalg( homalg_ring ) then
        
        AddKernelObject( Coproduct,
          function( Coproduct, morphism )
            local Rows, kernel_objects;
            
            Rows := UnderlyingCategoryOfRows( Coproduct );
            
            # Take the kernel object of all morphisms.
            kernel_objects :=
                List( ListOfPairsOfMorphismAndIndex( morphism ), pair ->
                    [ KernelObject( pair[1] ), pair[2] ] );
            
            # Remove possible zero objects.
            kernel_objects :=
                Filtered( kernel_objects, pair -> not IsZeroForObjects( Rows, pair[1] ) );
            
            return ObjectConstructor( Coproduct, kernel_objects );
            
        end );
        
        ##
        AddKernelEmbeddingWithGivenKernelObject( Coproduct,
          function( Coproduct, morphism, kernel_object )
            local Rows, kernel_embeddings;
            
            Rows := UnderlyingCategoryOfRows( Coproduct );
            
            # Compute the kernel embedding of all morphisms.
            kernel_embeddings :=
                List( ListOfPairsOfMorphismAndIndex( morphism ), pair ->
                    [ KernelEmbeddingWithGivenKernelObject( Rows, pair[1], Component( kernel_object, pair[2] ) ),
                      pair[2] ] );
            
            # Remove possible zero morphisms.
            kernel_embeddings :=
                Filtered( kernel_embeddings, pair -> not IsZeroForMorphisms( Rows, pair[1] ) );
            
            return MorphismConstructor( Coproduct, kernel_object, kernel_embeddings, Source( morphism ) );
            
        end );
        
        ##
        AddCokernelObject( Coproduct,
          function( Coproduct, morphism )
            local Rows, cokernel_objects;
            
            Rows := UnderlyingCategoryOfRows( Coproduct );
            
            # Take the cokernel object of all morphisms.
            cokernel_objects :=
                List( ListOfPairsOfMorphismAndIndex( morphism ), pair ->
                    [ CokernelObject( pair[1] ), pair[2] ] );
            
            # Remove possible zero objects.
            cokernel_objects :=
                Filtered( cokernel_objects, pair -> not IsZeroForObjects( Rows, pair[1] ) );
            
            return ObjectConstructor( Coproduct, cokernel_objects );
            
        end );
        
        ##
        AddCokernelProjectionWithGivenCokernelObject( Coproduct,
          function( Coproduct, morphism, cokernel_object )
            local Rows, cokernel_projections;
            
            Rows := UnderlyingCategoryOfRows( Coproduct );
            
            # Compute the cokernel projections of all morphisms.
            cokernel_projections :=
                List( ListOfPairsOfMorphismAndIndex( morphism ), pair ->
                      [ CokernelProjectionWithGivenCokernelObject( Rows, pair[1], Component( cokernel_object, pair[2] ) ),
                      pair[2] ] );
            
            # Remove possible zero morphisms.
            cokernel_projections :=
                Filtered( cokernel_projections, pair -> not IsZeroForMorphisms( Rows, pair[1] ) );
            
            return MorphismConstructor( Coproduct, Target( morphism ), cokernel_projections, cokernel_object );
            
        end );
        
    fi;
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        
        Finalize( Coproduct );
        
    fi;
    
    return Coproduct;
    
end ) );

####################################
##
## Attributes
##
####################################

InstallMethodForCompilerForCAP( Component,
                                [ IsObjectInCoproductOfCategoryOfRowsWithSparseDatastructure, IsBigInt ],
                                
  function( object, i )
    local component, Rows;
    
    Assert( 0, 1 <= i and i <= NrOfSummandsOfCoproduct( CapCategory( object ) ) );
    
    component := First( ListOfPairsOfObjectAndIndex( object ), pair -> pair[2] = i );
    
    if component = fail then
        
        Rows := UnderlyingCategoryOfRows( CapCategory( object ) );
        
        return ZeroObject( Rows );
        
    fi;
    
    return component[1];
    
end );

InstallMethodForCompilerForCAP( Component,
                                [ IsMorphismInCoproductOfCategoryOfRowsWithSparseDatastructure, IsBigInt ],
                                
  function( morphism, i )
    local component, Rows, source, target;
    
    Assert( 0, 1 <= i and i <= NrOfSummandsOfCoproduct( CapCategory( morphism ) ) );
    
    component := First( ListOfPairsOfMorphismAndIndex( morphism ), pair -> pair[2] = i );
    
    if component = fail then
        
        Rows := UnderlyingCategoryOfRows( CapCategory( morphism ) );
        
        source := Component( Source( morphism ), i );
        target := Component( Target( morphism ), i );
        
        return ZeroMorphism( Rows, source, target );
        
    fi;
    
    return component[1];
    
end );

####################################
##
## Operations
##
####################################

##
InstallMethodForCompilerForCAP( \[\],
                                [ IsObjectInCoproductOfCategoryOfRowsWithSparseDatastructure, IsInt ],
                                
  function( object, i )
    
    return Component( object, i );
    
end );

##
InstallMethodForCompilerForCAP( \[\],
                                [ IsMorphismInCoproductOfCategoryOfRowsWithSparseDatastructure, IsInt ],
                                
  function( morphism, i )
    
    return Component( morphism ,i );
    
end );

InstallOtherMethod( \/,
                   [ IsList, IsCoproductOfCategoryOfRowsWithSparseDatastructure ],
                  
  function( list, coproduct )
    local Rows, list_of_pairs_of_object_and_index, source_list, target_list, list_of_pairs_of_morphism_and_index, source, target;
    
    Rows := UnderlyingCategoryOfRows( coproduct );
    
    # List of integers?
    if ForAll( list, i -> IsBigInt( i ) ) and Length( list ) = NrOfSummandsOfCoproduct( coproduct ) then
        
        list_of_pairs_of_object_and_index :=
            ListWithKeys( list, { index, element } -> [ CategoryOfRowsObject( Rows, element ), index ] );
        
        # Only keep the non-zero entries.
        list_of_pairs_of_object_and_index :=
            Filtered( list_of_pairs_of_object_and_index, pair -> RankOfObject( pair[1] ) > 0 );
        
        return ObjectConstructor( coproduct, list_of_pairs_of_object_and_index );
        
    # List of matrices?
    elif ForAll( list, m -> IsHomalgMatrix( m ) ) and Length( list ) = NrOfSummandsOfCoproduct( coproduct ) then
        
        list_of_pairs_of_morphism_and_index :=
            ListWithKeys( list, { index, matrix } -> [ AsCategoryOfRowsMorphism( Rows, matrix ), index ] );
        
        source_list := List( list_of_pairs_of_morphism_and_index, pair ->
            [ Source( pair[1] ), pair[2] ] );
        
        target_list := List( list_of_pairs_of_morphism_and_index, pair ->
            [ Target( pair[1] ), pair[2] ] );
        
        source := ObjectConstructor( coproduct, source_list );
        target := ObjectConstructor( coproduct, target_list );
        
        # Now only keep the non-zero morphisms.
        # Needs to be done after constructing 'source' and 'range', otherwise we lose information.
        list_of_pairs_of_morphism_and_index :=
            Filtered( list_of_pairs_of_morphism_and_index, pair -> IsZeroForMorphisms( Rows, pair[1] ) = false );
        
        return MorphismConstructor( coproduct, source, list_of_pairs_of_morphism_and_index, target );
        
    # List of pairs of integers?
    elif ForAll( list, pair -> IsBigInt( pair[1] ) and IsBigInt( pair[2] ) ) then
        
        list_of_pairs_of_object_and_index := List( list, pair -> [ CategoryOfRowsObject( Rows, pair[1] ), pair[2] ] );
        
        return ObjectConstructor( coproduct, list_of_pairs_of_object_and_index );
        
    # List of pairs of matrices?
    elif ForAll( list, pair -> IsHomalgMatrix( pair[1] ) and IsBigInt( pair[2] ) ) then
        
        source_list := List( list, pair -> [ CategoryOfRowsObject( Rows, NrRows( pair[1] ) ), pair[2] ] );
        target_list := List( list, pair -> [ CategoryOfRowsObject( Rows, NrCols( pair[1] ) ), pair[2] ] );
        
        source := ObjectConstructor( coproduct, source_list );
        target := ObjectConstructor( coproduct, target_list );
        
        list_of_pairs_of_morphism_and_index := List( list, pair -> [ AsCategoryOfRowsMorphism( Rows, pair[1] ), pair[2] ] );
        
        return MorphismConstructor( coproduct, source, list_of_pairs_of_morphism_and_index, target );
        
    else
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "wrong format for <list>\n" );
        
    fi;
    
end );

####################################
##
## Global functions
##
####################################

InstallGlobalFunction( CAP_INTERNAL_coproduct_morphism_constructor_sanity_check,
  function( coproduct, S, list_of_pairs_of_morphism_and_index, T )
    local Rows, pair, rows_morphism, source_rows_mor, target_rows_mor, index, source_rows_pair, target_rows_pair, morphism_pair;
    
    Rows := UnderlyingCategoryOfRows( coproduct );
    
    # For all pairs [ RowsMorphism, index ], if RowsMorphism has a non-zero
    # source or target, there must exist a pair
    # [ SourceRows, index ] or [ TargetRows, index ] in 'S' or 'T'.
    #% CAP_JIT_DROP_NEXT_STATEMENT
    for pair in list_of_pairs_of_morphism_and_index do
        
        rows_morphism := pair[1];
        
        source_rows_mor := Source( rows_morphism );
        target_rows_mor := Target( rows_morphism );
        
        index := pair[2];
        
        if not IsZeroForObjects( Rows, source_rows_mor )  then
            
            source_rows_pair :=
                Filtered( ListOfPairsOfObjectAndIndex( S ), pair ->
                    pair[2] = index and
                    IsEqualForObjects( Rows, pair[1], source_rows_mor ) );
            
            if IsEmpty( source_rows_pair ) then
                
                # COVERAGE_IGNORE_NEXT_LINE
                Error( Concatenation( "no source object found for the morphism pair ", String( index ), "\n" ) );
                
            fi;
            
        fi;
        
        if not IsZeroForObjects( Rows, target_rows_mor )  then
            
            target_rows_pair :=
                Filtered( ListOfPairsOfObjectAndIndex( T ), pair ->
                    pair[2] = index and
                    IsEqualForObjects( Rows, pair[1], target_rows_mor ) );
            
            if IsEmpty( target_rows_pair ) then
                
                # COVERAGE_IGNORE_NEXT_LINE
                Error( Concatenation( "no target object found for the morphism pair ", String( index ), "\n" ) );
                
            fi;
            
        fi;
    od;
    
    # If there is a pair [ RowsObject_source, index ] in 'S' and
    # a pair [ RowsObject_target, index ] in 'T' with the same index,
    # such that RowsObject_source =/= 0 =/= RowsObject_target,
    # then there must be a pair [ RowsMorphism, index ] with
    # RowsMorphism: RowsObject_source -> RowsObject_target.
    for source_rows_pair in ListOfPairsOfObjectAndIndex( S ) do
        
        if not IsZeroForObjects( source_rows_pair[1] ) then
            
            # Check if there is also a pair [ obj, index ] in the pairs list of 'T'
            # with the same 'index' as 'source_rows_pair' and with 'obj' not zero.
            target_rows_pair :=
                Filtered( ListOfPairsOfObjectAndIndex( T ), target_rows_pair ->
                    target_rows_pair[2] = source_rows_pair[2] and
                    not IsZeroForObjects( Rows, target_rows_pair[1] ) );
            
            if not IsEmpty( target_rows_pair ) then
                
                target_rows_pair := target_rows_pair[1];
                
                # We have a rows object in 'S' and a rows object in 'T'
                # at the same index which are both not zero.
                # Hence there must be a non-zero morphism.
                morphism_pair :=
                    Filtered( list_of_pairs_of_morphism_and_index, morphism_pair ->
                        source_rows_pair[2] = morphism_pair[2] and
                        IsEqualForObjects( Rows, source_rows_pair[1], Source( morphism_pair[1] ) ) and
                        IsEqualForObjects( Rows, target_rows_pair[1], Target( morphism_pair[1] ) ) );
                
                if IsEmpty( morphism_pair ) then
                    
                    Error( Concatenation( "missing morphism at index ", String( source_rows_pair[2] ),
                                          " whose underlying matrix must be ",
                                          String( RankOfObject( source_rows_pair[1] ) ),
                                          "x",
                                          String( RankOfObject( target_rows_pair[1] ) ) ) );
                    
                fi;
                
            fi;
            
        fi;
        
    od;
    
end );

InstallGlobalFunction( CAP_INTERNAL_coproduct_sparse_object_list_to_dense_list,
  function( coproduct, list_of_pairs_of_object_and_index )
    local multiplicities, pair;
    
    # Turn a list of pairs into a dense list of integer multiplicities.
    # Example:
    #
    # [ [ RowsObject(1), 2], [ RowsObject(2), 5], [ RowsObject(3), 9] ]
    #
    #                                |
    #                                |
    #                                v
    #
    #                  [ 0, 1, 0, 0, 2, 0, 0, 0, 3 ]
    
    multiplicities := ListWithIdenticalEntries( NrOfSummandsOfCoproduct( coproduct ), 0 );
    
    for pair in list_of_pairs_of_object_and_index do
        
        multiplicities[ pair[2] ] :=  RankOfObject( pair[1] );
        
    od;
    
    return multiplicities;
    
end );

InstallGlobalFunction( CAP_INTERNAL_coproduct_dense_object_list_to_sparse_list,
  function( coproduct, multiplicities )
    local Rows, list_of_pairs, i;
    
    # Turn a dense list of integer multiplicities into a sparse list of pairs.
    # Example:
    #
    #                  [ 0, 1, 0, 0, 2, 0, 0, 0, 3 ]
    #
    #                                |
    #                                |
    #                                v
    #
    # [ [ RowsObject(1), 2], [ RowsObject(2), 5], [ RowsObject(3), 9] ]
    
    Rows := UnderlyingCategoryOfRows( coproduct );
    
    list_of_pairs := [ ];
    
    for i in [ 1 .. Length( multiplicities ) ] do
        
        if multiplicities[i] > 0 then
            
            Add( list_of_pairs, [ CategoryOfRowsObject( Rows, multiplicities[i] ), i ] );
            
        fi;
        
    od;
    
    return list_of_pairs;
    
end );

InstallGlobalFunction( CAP_INTERNAL_coproduct_sparse_matrices_list_to_dense_list,
  function( coproduct, list_of_pairs_of_matrices_and_index )
    local dense_list, pair;
    
    # Turn a list of pairs into a dense list of matrices as listlist's.
    # Example:
    #
    #  [ [ 1x1, 2 ], [ 2x2, 5 ], [ 3x3, 9 ] ]
    #
    #                     |
    #                     |
    #                     v
    #
    # [ [], 1x1, [], [], 2x2, [], [], [], 3x3 ]
    
    # Create a list of 0x0 matrices.
    dense_list := ListWithIdenticalEntries( NrOfSummandsOfCoproduct( coproduct ), [] );
    
    # Copy all matrices into 'dense_list' at their correct index.
    # These are non-empty matrices.
    for pair in list_of_pairs_of_matrices_and_index do
        
        dense_list[ pair[2] ] := pair[1];
        
    od;
    
    return dense_list;
    
end );

InstallGlobalFunction( CAP_INTERNAL_coproduct_dense_matrices_list_to_sparse_list,
  function( coproduct, matrices )
    local Rows, list_of_pairs, i, matrix;
    
    # Turn a dense list of matrices as listlist's into a sparse list of pairs.
    # Example:
    #
    # [ 0x0, 1x1, 0x0, 0x0, 2x2, 0x0, 0x0, 0x0, 3x3 ]
    #
    #                         |
    #                         |
    #                         v
    #
    #       [ [ 1x1, 2 ], [ 2x2, 5 ], [ 3x3, 9 ] ]
    
    Rows := UnderlyingCategoryOfRows( coproduct );
    
    list_of_pairs := [ ];
    
    for i in [ 1 .. Length( matrices ) ] do
        
        matrix := matrices[i];
        
        if not IsEmpty( matrix ) and not IsEmpty( matrix[1] ) then
            
            Add( list_of_pairs, [ matrix, i ] );
            
        fi;
        
    od;
    
    return list_of_pairs;
    
end );

####################################
##
## View & Display
##
####################################

InstallMethod( DisplayString,
               [ IsObjectInCoproductOfCategoryOfRowsWithSparseDatastructure ],
               
  object -> String( ListOfPairsOfObjectAndIndex( object ) )
  
);

InstallMethod( DisplayString,
               [ IsMorphismInCoproductOfCategoryOfRowsWithSparseDatastructure ],
               
  function( morphism )
    local string, pair, rows_morphism, target, nr_rows, nr_cols, j, k;
    
    string := "";
    
    for pair in ListOfPairsOfMorphismAndIndex( morphism ) do
        
        rows_morphism := pair[1];
        
        nr_rows := RankOfObject( Source( rows_morphism ) );
        
        # 0xn morphism in category of rows?
        if nr_rows = 0 then
            
            nr_cols := RankOfObject( Target( rows_morphism ) );
            
            string := Concatenation( string,
                                     "Index ", String( pair[2] ),
                                     ": a ", String( 0 ), " x ", String( nr_cols ),
                                     " morphism in ",
                                     Name( UnderlyingCategoryOfRows( CapCategory( morphism ) ) ), "\n\n" );
            
            continue;
            
        fi;
        
        nr_cols := RankOfObject( Target( rows_morphism ) );
        
        # nx0 morphism in category of rows?
        if nr_cols = 0 then
            
            string := Concatenation( string,
                                     "Index ", String( pair[2] ),
                                     ": a ", String( nr_rows ), " x ", String( 0 ),
                                     " morphism in ",
                                     Name( UnderlyingCategoryOfRows( CapCategory( morphism ) ) ), "\n\n" );
            
            continue;
            
        fi;
        
        string := Concatenation( string,
                                 "Index ", String( pair[2] ),
                                 ": a ", String( nr_rows ), " x ", String( nr_cols ),
                                 " morphism in ",
                                 Name( UnderlyingCategoryOfRows( CapCategory( morphism ) ) ), "\n" );
        
        # Not a zero morphism so we can display its values.
        for j in [ 1 .. nr_rows ] do
            
            for k in [ 1 .. nr_cols ] do
                
                string := Concatenation( string, Concatenation( "\n[", String(j), ",", String(k), "]: " ) );
                
                string := Concatenation( string, ViewString( UnderlyingMatrix( rows_morphism )[j,k] ) );
                
            od;
            
        od;
        
        string := Concatenation( string, "\n\n" );
        
    od;
    
    return string;
    
end );

