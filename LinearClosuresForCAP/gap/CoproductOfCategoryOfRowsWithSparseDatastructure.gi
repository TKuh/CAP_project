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
# InstallMethod( COPRODUCT_OF_CATEGORY_OF_ROWS_WITH_SPARSE_DATASTRUCTURE,
#                [ IsCategoryOfRows, IsBigInt ],
#                COPRODUCT_OF_CATEGORY_OF_ROWS_WITH_SPARSE_DATASTRUCTURE
# );

##
InstallMethod( CoproductOfCategoryOfRowsWithSparseDatastructure,
               [ IsCapCategory, IsBigInt ],
               
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
    
    ##
    object_datum_type :=
        CapJitDataTypeOfListOf(
            CapJitDataTypeOfNTupleOf( 2,
                CapJitDataTypeOfObjectOfCategory( Rows ),
                IsBigInt ) );
    
    ##
    object_datum := { Coproduct, obj } -> ListOfPairsOfObjectAndIndex( obj );
    
    ##
    object_constructor :=
      function( Coproduct, list_of_pairs_of_object_and_index )
        
        # For all pairs [ RowsMorphism, index ] the 'index' must be
        # between 1 and NrOfSummandsOfCoproduct( Coproduct ).
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( list_of_pairs_of_object_and_index, pair ->
            1 <= pair[2] and pair[2] <= NrOfSummandsOfCoproduct( Coproduct ) ) );
        
        # For all pairs [ RowsMorphism, index ] the 'index' must be strictly increasing.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( [ 1 .. Length( list_of_pairs_of_object_and_index ) - 1 ], i ->
            list_of_pairs_of_object_and_index[i][2] < list_of_pairs_of_object_and_index[i+1][2] ) );
        
        return CreateCapCategoryObjectWithAttributes( Coproduct,
                       ListOfPairsOfObjectAndIndex, list_of_pairs_of_object_and_index );
        
    end;
    
    ##
    morphism_datum_type :=
        CapJitDataTypeOfListOf(
            CapJitDataTypeOfNTupleOf( 2,
                CapJitDataTypeOfMorphismOfCategory( Rows ),
                IsBigInt ) );
    
    ##
    morphism_datum := { Coproduct, phi } -> ListOfPairsOfMorphismAndIndex( phi );
    
    ##
    morphism_constructor :=
      function( Coproduct, S, list_of_pairs_of_morphism_and_index, T )
        local Rows, pair, rows_morphism, source_rows_mor, target_rows_mor, index, source_rows_pair, target_rows_pair, morphism_pair, source_pair, source_object, source_index, target_pair, target_object, target_index;
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        # For all pairs [ RowsMorphism, index ] the 'index' must be
        # between 1 and NrOfSummandsOfCoproduct( Coproduct ).
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( list_of_pairs_of_morphism_and_index, pair ->
            1 <= pair[2] and pair[2] <= NrOfSummandsOfCoproduct( Coproduct ) ) );
        
        # For all pairs [ RowsMorphism, index ] the 'index' must be strictly increasing.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( [ 1 .. Length( list_of_pairs_of_morphism_and_index ) - 1 ], i ->
            list_of_pairs_of_morphism_and_index[i][2] < list_of_pairs_of_morphism_and_index[i+1][2] ) );
        
        # For all pairs [ RowsMorphism, index ], if RowsMorphism has a non-zero
        # source or target, there must exist a pair
        # [ SourceRows, index ] or [ TargetRows, index ] in 'S' or 'T'.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        for pair in list_of_pairs_of_morphism_and_index do
            
            rows_morphism := pair[1];
            
            source_rows_mor := Source( rows_morphism );
            target_rows_mor := Target( rows_morphism );
            
            index := pair[2];
            
            if not IsZeroForObjects( Rows, source_rows_mor ) then
                
                source_rows_pair :=
                    Filtered( ListOfPairsOfObjectAndIndex( S ), pair ->
                        pair[2] = index and
                        IsEqualForObjects( Rows, pair[1], source_rows_mor ) );
                
                Assert( 0, not IsEmpty( source_rows_pair ) );
                
            fi;
            
            if not IsZeroForObjects( Rows, target_rows_mor ) then
                
                target_rows_pair :=
                    Filtered( ListOfPairsOfObjectAndIndex( T ), pair ->
                        pair[2] = index and
                        IsEqualForObjects( Rows, pair[1], target_rows_mor ) );
                
                Assert( 0, not IsEmpty( target_rows_pair ) );
                
            fi;
            
        od;
        
        # For any pair in 'S' with [r,l] with r =/= 0, there must
        # explicitly be a morphism pair [m,l] with Source( m ) = r.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        for source_pair in ListOfPairsOfObjectAndIndex( S ) do
            
            source_object := source_pair[1];
            source_index := source_pair[2];
            
            if not IsZeroForObjects( Rows, source_object ) then
                
                # Find the matrix at index 'source_index'.
                morphism_pair :=
                    First( Filtered( list_of_pairs_of_morphism_and_index, m_pair -> m_pair[2] = source_index ) );
                
                # Did we find a source object =/= 0 but not a matrix for it?
                Assert( 0, fail <> morphism_pair );
                
                Assert( 0, source_object = Source( morphism_pair[1] ) );
                
            fi;
            
        od;
        
        # For any pair in 'T' with [r,l] with r =/= 0, there must
        # explicitly be a morphism pair [m,l] with Target( m ) = r.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        for target_pair in ListOfPairsOfObjectAndIndex( T ) do
            
            target_object := target_pair[1];
            target_index := target_pair[2];
            
            if not IsZeroForObjects( Rows, target_object ) then
                
                # Find the matrix at index 'target_index'.
                morphism_pair :=
                    First( Filtered( list_of_pairs_of_morphism_and_index, m_pair -> m_pair[2] = target_index ) );
                
                # Did we find a target object =/= 0 but not a matrix for it?
                Assert( 0, fail <> morphism_pair );
                
                Assert( 0, target_object = Target( morphism_pair[1] ) );
                
            fi;
            
        od;
        
        return CreateCapCategoryMorphismWithAttributes(
                    Coproduct,
                    S,
                    T,
                    ListOfPairsOfMorphismAndIndex, list_of_pairs_of_morphism_and_index );
        
    end;
    
    ####################################
    # Modeling tower
    ####################################
    
    D := FiniteSkeletalDiscreteCategory( nr_summands : FinalizeCategory := true );
    
    L := LinearClosure( homalg_ring, D : FinalizeCategory := true );
    
    AC_disc := AdditiveClosureOfObjectFiniteDisconnectedCategory( L : FinalizeCategory := true );
    
    ####################################
    # Reinterpretation
    ####################################
    
    ## From the raw object data to the object in the modeling category:
    modeling_tower_object_constructor :=
      function( Coproduct, list_of_pairs_of_object_and_index )
        local AC_disc, dense_list_of_multiplicities, multiplicities;
        
        AC_disc := ModelingCategory( Coproduct );
        
        dense_list_of_multiplicities :=
            ListWithIdenticalEntries( NrOfSummandsOfCoproduct( Coproduct ), 0 );
        
        multiplicities :=
            COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( Coproduct, list_of_pairs_of_object_and_index, dense_list_of_multiplicities );
        
        return ObjectConstructor( AC_disc, Pair( Sum( multiplicities ), multiplicities ) );
        
    end;
    
    ## From the object in the modeling category to the raw object data:
    modeling_tower_object_datum :=
      function( Coproduct, object )
        local multiplicities, list_of_pairs_of_object_and_index;
        
        multiplicities := Multiplicities( object );
        
        list_of_pairs_of_object_and_index :=
            COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseObjectListToSparseList( Coproduct, multiplicities );
        
        return list_of_pairs_of_object_and_index;
        
    end;
    
    ## From the raw morphism data to the morphism in the modeling category:
    modeling_tower_morphism_constructor :=
      function( Coproduct, S, list_of_pairs_of_morphism_and_index, T )
        local AC_disc, L, underlying_linear_objects, pairs_listlist_with_index, pair, row, nr_matrices, list_of_empty_lists, dense_list_of_matrices, dense_list_of_matrices_with_expanded_empty_lists;
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( list_of_pairs_of_morphism_and_index, pair ->
            RankOfObject( Source( pair[1] ) ) = Multiplicities( S )[ pair[2] ] ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( list_of_pairs_of_morphism_and_index, pair ->
            RankOfObject( Target( pair[1] ) ) = Multiplicities( T )[ pair[2] ] ) );
        
        AC_disc := ModelingCategory( Coproduct );
        
        L := UnderlyingCategory( AC_disc );
        
        underlying_linear_objects := SetOfObjectsOfCategory( L );
        
        # Turn all Homalg matrices into listlist's.
        pairs_listlist_with_index :=
            List( list_of_pairs_of_morphism_and_index, pair ->
                [ EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair[1] ) ), pair[2] ] );
        
        # For all matrices as listlist's turn the entries 'c' into coefficients: c·IdentityMorphism.
        pairs_listlist_with_index :=
            List( pairs_listlist_with_index, pair ->
                Pair( List( pair[1], row ->
                        List( row, c ->
                            MultiplyWithElementOfCommutativeRingForMorphisms(
                                L, c, IdentityMorphism( L, underlying_linear_objects[ pair[2] ] ) ) ) ),
                      pair[2] ) );
        
        list_of_empty_lists :=
            ListWithIdenticalEntries(
                NrOfSummandsOfCoproduct( Coproduct ),
                CapJitTypedExpression( [ ], cat ->
                    CapJitDataTypeOfListOf(
                        CapJitDataTypeOfMorphismOfCategory(
                            UnderlyingCategory( ModelingCategory( cat ) ) ) ) ) );
        
        dense_list_of_matrices :=
            COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList(
                    Coproduct,
                    pairs_listlist_with_index,
                    list_of_empty_lists );
        
        nr_matrices := NrOfSummandsOfCoproduct( Coproduct );
        
        # Replace the entries for empty matrices of the form nx0, with n > 0,
        # from [ ] to [ [], [], ..., [] ] in 'dense_list'.
        # This is required by the modeling additive closure
        # to represent nx0 matrices.
        dense_list_of_matrices_with_expanded_empty_lists :=
            List( [ 1 .. nr_matrices ],
                function( i )
                    local nr_rows, nr_cols;
                    
                    nr_rows := Multiplicities( S )[i];
                    nr_cols := Multiplicities( T )[i];
                    
                    # Check if we have an nx0 matrix.
                    if  nr_rows > 0 and nr_cols = 0 then
                        
                        # Return an nx0 matrix.
                        return
                            ListWithIdenticalEntries( nr_rows,
                                CapJitTypedExpression( [ ], cat ->
                                    CapJitDataTypeOfListOf(
                                        CapJitDataTypeOfMorphismOfCategory(
                                            UnderlyingCategory( ModelingCategory( cat ) ) ) ) ) );
                        
                    fi;
                    
                    # We do not need to care about 0xn matrices,
                    # since these have the form '[ ]',
                    # and this is already the case by construction of 'dense_list_of_matrices'.
                    
                    return dense_list_of_matrices[i];
                    
        end );
        
        # Check that all matrices as listlist's still have the correct dimensions.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0,
            ForAllWithKeys( dense_list_of_matrices_with_expanded_empty_lists, { i, matrix } ->
                Length( matrix ) = Multiplicities( S )[i] and
                ForAll( matrix, row -> Length( row ) = Multiplicities( T )[i] ) ) );
        
        return MorphismConstructor( AC_disc, S, dense_list_of_matrices_with_expanded_empty_lists, T );
        
    end;
    
    # From the morphism in the modeling category to the raw morphism data:
    modeling_tower_morphism_datum :=
      function ( Coproduct, morphism )
        local Rows, underlying_ring, source_multiplicities, target_multiplicities, sparse_list, list_of_pairs_of_morphism_and_index;
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        underlying_ring := UnderlyingRing( Coproduct );
        
        source_multiplicities := Multiplicities( Source( morphism ) );
        target_multiplicities := Multiplicities( Target( morphism ) );
        
        sparse_list :=
            COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList(
                    Coproduct,
                    source_multiplicities,
                    ListOfMatrices( morphism ),
                    target_multiplicities );
        
        # For each pair, convert the matrix into a morphism in the category of rows.
        list_of_pairs_of_morphism_and_index :=
            List( sparse_list,
                function( pair )
                    local matrix, nr_rows, nr_cols, homalg_matrix, morphism;
                    
                    matrix := pair[1];
                    
                    # All entries are of the form: c·IdentityMorphism, so we extract the coefficients 'c'.
                    matrix :=
                        List( matrix, row ->
                            List( row, entry -> Coefficient( entry ) ) );
                    
                    nr_rows := source_multiplicities[ pair[2] ];
                    nr_cols := target_multiplicities[ pair[2] ];
                    
                    homalg_matrix := HomalgMatrixListList( matrix,
                                                           nr_rows,
                                                           nr_cols,
                                                           underlying_ring );
                    
                    morphism := CategoryOfRowsMorphism( Rows,
                                                        CategoryOfRowsObject( Rows, nr_rows ),
                                                        homalg_matrix,
                                                        CategoryOfRowsObject( Rows, nr_cols ) );
                    
                    return Pair( morphism, pair[2] );
                    
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
        "ModelingCategory",
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
                    Pair( KernelObject( Rows, pair[1] ), pair[2] ) );
            
            # Remove zero objects.
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
                    Pair( KernelEmbeddingWithGivenKernelObject( Rows, pair[1], Component( kernel_object, pair[2] ) ),
                          pair[2] ) );
            
            # Remove morphisms with underlying 0x0 matrix.
            kernel_embeddings :=
                Filtered( kernel_embeddings, pair ->
                    not IsZeroForObjects( Rows, Source( pair[1] ) ) or
                    not IsZeroForObjects( Rows, Target( pair[1] ) ) );
            
            return MorphismConstructor( Coproduct, kernel_object, kernel_embeddings, Source( morphism ) );
            
        end );
        
        ##
        AddLift( Coproduct,
          function( Coproduct, alpha, beta )
            local Rows, source, target, support, morphism_list;
            
            Rows := UnderlyingCategoryOfRows( Coproduct );
            
            source := Source( alpha );
            target := Source( beta );
            
            support := Union2( Support( source ), Support( target ) );
            
            morphism_list :=
                List( support, index ->
                   Pair( Lift( Rows, Component( alpha, index ), Component( beta, index ) ), index ) );
            
            return MorphismConstructor( Coproduct, source, morphism_list, target );
            
        end );
        
        ##
        AddCokernelObject( Coproduct,
          function( Coproduct, morphism )
            local Rows, cokernel_objects;
            
            Rows := UnderlyingCategoryOfRows( Coproduct );
            
            # Take the cokernel object of all morphisms.
            cokernel_objects :=
                List( ListOfPairsOfMorphismAndIndex( morphism ), pair ->
                    Pair( CokernelObject( Rows, pair[1] ), pair[2] ) );
            
            # Remove zero objects.
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
                    Pair( CokernelProjectionWithGivenCokernelObject( Rows, pair[1], Component( cokernel_object, pair[2] ) ),
                          pair[2] ) );
            
            # Remove morphisms with underlying 0x0 matrix.
            cokernel_projections :=
                Filtered( cokernel_projections, pair ->
                    not IsZeroForObjects( Rows, Source( pair[1] ) ) or
                    not IsZeroForObjects( Rows, Target( pair[1] ) ) );
            
            return MorphismConstructor( Coproduct, Target( morphism ), cokernel_projections, cokernel_object );
            
        end );
        
        AddColift( Coproduct,
          function( Coproduct, alpha, beta )
            local Rows, source, target, support, morphism_list;
            
            Rows := UnderlyingCategoryOfRows( Coproduct );
            
            source := Target( alpha );
            target := Target( beta );
            
            support := Union2( Support( source ), Support( target ) );
            
            morphism_list :=
                List( support, index ->
                   Pair( Colift( Rows, Component( alpha, index ), Component( beta, index ) ), index ) );
            
            return MorphismConstructor( Coproduct, source, morphism_list, target );
            
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

InstallMethodForCompilerForCAP( Support,
                                [ IsObjectInCoproductOfCategoryOfRowsWithSparseDatastructure ],
                                
  function( object )
    
    return List( ListOfPairsOfObjectAndIndex( object ), elem -> elem[2] );
    
end );

InstallMethodForCompilerForCAP( Support,
                                [ IsMorphismInCoproductOfCategoryOfRowsWithSparseDatastructure ],
                                
  function( morphism )
    
    return List( ListOfPairsOfMorphismAndIndex( morphism ), mor -> mor[2] );
    
end );

####################################
##
## Operations
##
####################################

InstallMethodForCompilerForCAP( Component,
                                [ IsObjectInCoproductOfCategoryOfRowsWithSparseDatastructure, IsBigInt ],
                                
  function( object, i )
    local component, Rows;
    
    #% CAP_JIT_DROP_NEXT_STATEMENT
    Assert( 0, 1 <= i and i <= NrOfSummandsOfCoproduct( CapCategory( object ) ) );
    
    component := Filtered( ListOfPairsOfObjectAndIndex( object ), pair -> pair[2] = i );
    
    if Length( component ) = 0 then
        
        Rows := UnderlyingCategoryOfRows( CapCategory( object ) );
        
        return ZeroObject( Rows );
        
    else
    
        # Return the object of the pair.
        return component[1][1];
    
    fi;
    
end );

InstallMethodForCompilerForCAP( Component,
                                [ IsMorphismInCoproductOfCategoryOfRowsWithSparseDatastructure, IsBigInt ],
                                
  function( morphism, i )
    local component, Rows, source, target;
    
    #% CAP_JIT_DROP_NEXT_STATEMENT
    Assert( 0, 1 <= i and i <= NrOfSummandsOfCoproduct( CapCategory( morphism ) ) );
    
    component := Filtered( ListOfPairsOfMorphismAndIndex( morphism ), pair -> pair[2] = i );
    
    if Length( component ) = 0 then
        
        Rows := UnderlyingCategoryOfRows( CapCategory( morphism ) );
        
        source := Component( Source( morphism ), i );
        target := Component( Target( morphism ), i );
        
        return ZeroMorphism( Rows, source, target );
        
    else
        
        # Return the morphism of the pair.
        return component[1][1];
        
    fi;
    
end );

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
                  
  function( list, Coproduct )
    local Rows, list_of_pairs_of_object_and_index, source_list, target_list, list_of_pairs_of_morphism_and_index, source, target;
    
    Rows := UnderlyingCategoryOfRows( Coproduct );
    
    # List of integers?
    if ForAll( list, i -> IsBigInt( i ) ) and Length( list ) = NrOfSummandsOfCoproduct( Coproduct ) then
        
        list_of_pairs_of_object_and_index :=
            ListWithKeys( list, { index, element } -> [ CategoryOfRowsObject( Rows, element ), index ] );
        
        # Only keep the non-zero entries.
        list_of_pairs_of_object_and_index :=
            Filtered( list_of_pairs_of_object_and_index, pair -> RankOfObject( pair[1] ) > 0 );
        
        return ObjectConstructor( Coproduct, list_of_pairs_of_object_and_index );
        
    # List of matrices?
    elif ForAll( list, m -> IsHomalgMatrix( m ) ) and Length( list ) = NrOfSummandsOfCoproduct( Coproduct ) then
        
        list_of_pairs_of_morphism_and_index :=
            ListWithKeys( list, { index, matrix } -> [ AsCategoryOfRowsMorphism( Rows, matrix ), index ] );
        
        source_list := List( list_of_pairs_of_morphism_and_index, pair ->
            [ Source( pair[1] ), pair[2] ] );
        
        target_list := List( list_of_pairs_of_morphism_and_index, pair ->
            [ Target( pair[1] ), pair[2] ] );
        
        source := ObjectConstructor( Coproduct, source_list );
        target := ObjectConstructor( Coproduct, target_list );
        
        # Now only keep the morphisms whose underlying matrix is not a 0x0 matrix.
        # Needs to be done after constructing 'source' and 'range', otherwise we lose information.
        list_of_pairs_of_morphism_and_index :=
            Filtered( list_of_pairs_of_morphism_and_index, pair ->
                IsZeroForObjects( Rows, Source( pair[1] ) ) = false or
                IsZeroForObjects( Rows, Target( pair[1] ) ) = false );
        
        return MorphismConstructor( Coproduct, source, list_of_pairs_of_morphism_and_index, target );
        
    # List of pairs of integers?
    elif ForAll( list, pair -> IsBigInt( pair[1] ) and IsBigInt( pair[2] ) ) then
        
        list_of_pairs_of_object_and_index := List( list, pair -> [ CategoryOfRowsObject( Rows, pair[1] ), pair[2] ] );
        
        return ObjectConstructor( Coproduct, list_of_pairs_of_object_and_index );
        
    # List of pairs of matrices?
    elif ForAll( list, pair -> IsHomalgMatrix( pair[1] ) and IsBigInt( pair[2] ) ) then
        
        source_list := List( list, pair -> [ CategoryOfRowsObject( Rows, NrRows( pair[1] ) ), pair[2] ] );
        target_list := List( list, pair -> [ CategoryOfRowsObject( Rows, NrCols( pair[1] ) ), pair[2] ] );
        
        source := ObjectConstructor( Coproduct, source_list );
        target := ObjectConstructor( Coproduct, target_list );
        
        list_of_pairs_of_morphism_and_index := List( list, pair -> [ AsCategoryOfRowsMorphism( Rows, pair[1] ), pair[2] ] );
        
        return MorphismConstructor( Coproduct, source, list_of_pairs_of_morphism_and_index, target );
        
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

InstallGlobalFunction( COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList,
  function( Coproduct, list_of_pairs_of_object_and_index, dense_list_of_multiplicities )
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
    
    multiplicities := dense_list_of_multiplicities;
    
    for pair in list_of_pairs_of_object_and_index do
        
        multiplicities[ pair[2] ] := RankOfObject( pair[1] );
        
    od;
    
    return multiplicities;
    
end );

InstallGlobalFunction( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseObjectListToSparseList,
  function( Coproduct, multiplicities )
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
    
    Rows := UnderlyingCategoryOfRows( Coproduct );
    
    list_of_pairs := [ ];
    
    for i in [ 1 .. Length( multiplicities ) ] do
        
        if multiplicities[i] > 0 then
            
            Add( list_of_pairs, [ CategoryOfRowsObject( Rows, multiplicities[i] ), i ] );
            
        fi;
        
    od;
    
    return list_of_pairs;
    
end );

InstallGlobalFunction( COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList,
  function( Coproduct, list_of_pairs_of_matrices_and_index, dense_list )
    local adjusted_dense_list, pair;
    
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
    adjusted_dense_list := dense_list;
    
    # Copy all matrices into 'dense_list' at their correct index.
    # These are non-empty matrices.
    for pair in list_of_pairs_of_matrices_and_index do
        
        adjusted_dense_list[ pair[2] ] := pair[1];
        
    od;
    
    return adjusted_dense_list;
    
end );

InstallGlobalFunction( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList,
  function( Coproduct, source_multiplicities, matrices, target_multiplicities )
    local Rows, list_of_pairs, i, matrix;
    
    # Turn a dense list of matrices as listlist's into a sparse list
    # of pairs of a matrix as a listlist and an integer index.
    #
    # Example:
    #
    #   source_multiplicities := [ 0, 1, 0, 0, 2, 0, 8, 0, 3 ]
    #   target_multiplicities := [ 0, 1, 0, 6, 2, 0, 0, 0, 3 ]
    #
    #        [ 0x0, 1x1, 0x0, 0x6, 2x2, 0x0, 8x0, 0x0, 3x3 ]
    #
    #                               |
    #                               |
    #                               v
    #
    # [ [ 1x1, 2 ], [ 0x6, 4 ], [ 2x2, 5 ], [ 8x0, 7 ], [ 3x3, 9 ] ]
    
    Rows := UnderlyingCategoryOfRows( Coproduct );
    
    list_of_pairs := [ ];
    
    for i in [ 1 .. Length( matrices ) ] do
        
        matrix := matrices[i];
        
        if source_multiplicities[ i ] <> 0 or target_multiplicities[ i ] <> 0 then
            
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

