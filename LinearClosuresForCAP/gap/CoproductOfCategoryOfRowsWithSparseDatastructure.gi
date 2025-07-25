# SPDX-License-Identifier: GPL-2.0-or-later
# AdditiveClosuresForCAP: Additive closures for pre-abelian categories
#
# Implementations
#

# Read precompiled categories
ReadPackage( "LinearClosuresForCAP", "gap/precompiled_categories/CoproductOfCategoryOfRowsWithSparseDatastructure_Field.gi" );

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
    local homalg_ring, object_datum_type, morphism_datum_type, name, Coproduct, compare_morphisms, object_datum, object_constructor, morphism_datum, morphism_constructor, SubscriptDigits, ToSubscript;
    
    Assert( 0, nr_summands > 0 );
    
    # Assert( 0, IsCategoryOfRows( Rows ) );
    
    if nr_summands = 1 then
        
        return Rows;
        
    fi;
    
    homalg_ring := UnderlyingRing( Rows );
    
    ##
    object_datum_type :=
        CapJitDataTypeOfListOf(
            CapJitDataTypeOfNTupleOf( 2,
                CapJitDataTypeOfObjectOfCategory( Rows ),
                IsBigInt ) );
    
    ##
    morphism_datum_type :=
        CapJitDataTypeOfListOf(
            CapJitDataTypeOfNTupleOf( 2,
                CapJitDataTypeOfMorphismOfCategory( Rows ),
                IsBigInt ) );
    
    name := Concatenation( "⊕ ( ", "CategoryOfRows( ", RingName( homalg_ring ), " ), ", String( nr_summands ), " )" );
    
    Coproduct :=
        CreateCapCategoryWithDataTypes( name,
                                        IsCoproductOfCategoryOfRowsWithSparseDatastructure,
                                        IsObjectInCoproductOfCategoryOfRowsWithSparseDatastructure,
                                        IsMorphismInCoproductOfCategoryOfRowsWithSparseDatastructure,
                                        IsCapCategoryTwoCell,
                                        object_datum_type,
                                        morphism_datum_type,
                                        fail );
    
    SetIsLinearCategoryOverCommutativeRing( Coproduct, true );
    
    if IsAbelianCategory( Rows ) then
        
        SetIsAbelianCategory( Coproduct, true );
        
    fi;
    
    SetIsSkeletalCategory( Coproduct, true );
    
    SetUnderlyingRing( Coproduct, homalg_ring );
    
    SetCommutativeRingOfLinearCategory( Coproduct, homalg_ring );
    
    SetUnderlyingCategoryOfRows( Coproduct, Rows );
    
    SetNrOfSummandsOfCoproduct( Coproduct, nr_summands );
    
    Coproduct!.compiler_hints :=
        rec( category_attribute_names :=
            [ "UnderlyingRing",
              "CommutativeRingOfLinearCategory",
              "NrOfSummandsOfCoproduct",
              "UnderlyingCategoryOfRows", ] );
    
    # Coproduct!.compiler_hints.source_and_range_attributes_from_morphism_attribute := rec(
    #     object_attribute_name := "SumOfRanksAndRanks",
    #     morphism_attribute_name := "ListOfMatrices",
    # );
    
    INSTALL_FUNCTIONS_FOR_COPRODUCT_OF_CATEGORY_OF_ROWS( Coproduct );
    
    if ValueOption( "no_precompiled_code" ) <> true then
        
        if HasIsFieldForHomalg( homalg_ring ) and IsFieldForHomalg( homalg_ring ) then
            
            ADD_FUNCTIONS_FOR_CoproductOfCategoryOfRowsWithSparseDatastructure_Field( Coproduct );
            
        fi;
        
    fi;
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        
        Finalize( Coproduct );
        
    fi;
    
    return Coproduct;
    
end ) );

####################################
##
## Basic operations
##
####################################

InstallGlobalFunction( INSTALL_FUNCTIONS_FOR_COPRODUCT_OF_CATEGORY_OF_ROWS,
  
  function( Coproduct )
    local compare_morphisms, Rows;
    
    ##
    AddObjectDatum( Coproduct,
      function( Coproduct, object )
        
        return ListOfPairsOfObjectAndIndex( object );
        
    end );
    
    ##
    AddObjectConstructor( Coproduct,
      function( Coproduct, pairs )
        
        # For all pairs [ RowsObject, index ] the 'index' must be
        # between 1 and NrOfSummandsOfCoproduct( Coproduct ).
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( pairs, pair ->
            1 <= pair[2] and pair[2] <= NrOfSummandsOfCoproduct( Coproduct ) ) );
        
        # For all pairs [ RowsObject, index ] the 'index' must be strictly increasing.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( [ 1 .. Length( pairs ) - 1 ], i ->
            pairs[i][2] < pairs[i+1][2] ) );
        
        return CreateCapCategoryObjectWithAttributes( Coproduct,
                       ListOfPairsOfObjectAndIndex, pairs );
        
    end );
    
    ##
    AddMorphismDatum( Coproduct,
      function( Coproduct, phi )
        
        return ListOfPairsOfMorphismAndIndex( phi );
        
    end );
    
    ##
    AddMorphismConstructor( Coproduct,
      function( Coproduct, S, pairs, T )
        local Rows, pair, rows_morphism, source_rows_mor, target_rows_mor, index, source_rows_pair, target_rows_pair, morphism_pair, source_pair, source_object, source_index, target_pair, target_object, target_index;
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        # For all pairs [ RowsMorphism, index ] the 'index' must be
        # between 1 and NrOfSummandsOfCoproduct( Coproduct ).
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( pairs, pair ->
            1 <= pair[2] and pair[2] <= NrOfSummandsOfCoproduct( Coproduct ) ) );
        
        # For all pairs [ RowsMorphism, index ] the 'index' must be strictly increasing.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( [ 1 .. Length( pairs ) - 1 ], i ->
            pairs[i][2] < pairs[i+1][2] ) );
        
        # For all pairs [ RowsMorphism, index ], if RowsMorphism has a non-zero
        # source or target, there must exist a pair
        # [ SourceRows, index ] or [ TargetRows, index ] in 'S' or 'T'.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        for pair in pairs do
            
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
                    First( Filtered( pairs, m_pair -> m_pair[2] = source_index ) );
                
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
                    First( Filtered( pairs, m_pair -> m_pair[2] = target_index ) );
                
                # Did we find a target object =/= 0 but not a matrix for it?
                Assert( 0, fail <> morphism_pair );
                
                Assert( 0, target_object = Target( morphism_pair[1] ) );
                
            fi;
            
        od;
        
        return CreateCapCategoryMorphismWithAttributes(
                    Coproduct,
                    S,
                    T,
                    ListOfPairsOfMorphismAndIndex, pairs );
        
    end );
    
    AddIsWellDefinedForObjects( Coproduct,
      function( Coproduct, object )
        local Rows, pairs;
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        pairs := ListOfPairsOfObjectAndIndex( object );
        
        # For all pairs [ RowsObject, index ] the 'index' must be
        # between 1 and NrOfSummandsOfCoproduct( Coproduct ).
        if not ForAll( pairs, pair ->
            1 <= pair[2] and pair[2] <= NrOfSummandsOfCoproduct( Coproduct ) ) then
            
            return false;
            
        # For all pairs [ RowsObject, index ] the 'index'
        # must be strictly increasing.
        elif not ForAll( [ 1 .. Length( pairs ) - 1 ], i ->
            pairs[i][2] < pairs[i+1][2] ) then
            
            return false;
            
        elif not ForAll( [ 1 .. Length( pairs ) - 1 ], i ->
            IsWellDefinedForObjects( Rows, pairs[i][1] ) ) then
            
            return false;
            
        else
            
            return true;
            
        fi;
        
    end );
    
    AddIsWellDefinedForMorphisms( Coproduct,
      function( Coproduct, morphism )
        local Rows, pairs;
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        pairs := ListOfPairsOfMorphismAndIndex( morphism );
        
        # For all pairs [ RowsMorphism, index ] the 'index' must be
        # between 1 and NrOfSummandsOfCoproduct( Coproduct ).
        if not ForAll( pairs, pair ->
            1 <= pair[2] and pair[2] <= NrOfSummandsOfCoproduct( Coproduct ) ) then
            
            return false;
            
        # For all pairs [ RowsMorphism, index ] the 'index'
        # must be strictly increasing.
        elif not ForAll( [ 1 .. Length( pairs ) - 1 ], i ->
            pairs[i][2] < pairs[i+1][2] ) then
            
            return false;
            
        elif not ForAll( [ 1 .. Length( pairs ) - 1 ], i ->
            IsWellDefinedForMorphisms( Rows, pairs[i][1] ) ) then
            
            return false;
            
        # We do not check the remaining requirements for the sparse datastructure.
        # See MorphismConstructor on how to do this.
        else
            
            return true;
            
        fi;
        
    end );
    
    ##
    AddIsEqualForObjects( Coproduct,
      function( Coproduct, object_1, object_2 )
        local Rows, pairs_1, pairs_2;
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        pairs_1 := ListOfPairsOfObjectAndIndex( object_1 );
        pairs_2 := ListOfPairsOfObjectAndIndex( object_2 );
        
        return Length( pairs_1 ) = Length( pairs_2 ) and
            # pairs_1 and pairs_2 have the same length.
            ForAll( [ 1 .. Length( pairs_1 ) ], i ->
                pairs_1[i][2] = pairs_2[i][2] and
                IsEqualForObjects( Rows, pairs_1[i][1], pairs_2[i][1] ) );
            
    end );
    
    compare_morphisms :=
      function( Coproduct, morphism_1, morphism_2, comparison_function )
        local Rows, pairs_1, pairs_2;
        #% CAP_JIT_RESOLVE_FUNCTION
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        pairs_1 := ListOfPairsOfMorphismAndIndex( morphism_1 );
        pairs_2 := ListOfPairsOfMorphismAndIndex( morphism_2 );
        
        if Length( pairs_1 ) <> Length( pairs_2 ) then
            
            return false;
            
        else
            
            return ForAll( [ 1 .. Length( pairs_1 ) ], i ->
                        pairs_1[i][2] = pairs_2[i][2] and
                        comparison_function( Rows, pairs_1[i][1], pairs_2[i][1] ) );
            
        fi;
        
    end;
    
    ##
    AddIsEqualForMorphisms( Coproduct,
      function( Coproduct, morphism_1, morphism_2 )
        
        return compare_morphisms( Coproduct, morphism_1, morphism_2, IsEqualForMorphisms );
        
    end );
    
    ##
    AddIsCongruentForMorphisms( Coproduct,
      function( Coproduct, morphism_1, morphism_2 )
        
        return compare_morphisms( Coproduct, morphism_1, morphism_2, IsCongruentForMorphisms );
        
    end );
    
    ##
    AddIdentityMorphism( Coproduct,
      function( Coproduct, object )
        local Rows, pairs, list_of_pairs;
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        pairs := ListOfPairsOfObjectAndIndex( object );
        
        list_of_pairs :=
            List( [ 1 .. Length( pairs ) ], n ->
               Pair( IdentityMorphism( Rows, pairs[n][1] ), pairs[n][2] ) );
        
        return MorphismConstructor( Coproduct, object, list_of_pairs, object );
        
    end );
    
    ##
    AddPreCompose( Coproduct,
      function( Coproduct, morphism_1, morphism_2 )
        local Rows, pairs_1, pairs_2, zero_object, zero_morphism, merged_pairs, list_of_precomposed_pairs;
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        pairs_1 := ListOfPairsOfMorphismAndIndex( morphism_1 );
        pairs_2 := ListOfPairsOfMorphismAndIndex( morphism_2 );
        
        zero_object := ZeroObject( Rows );
        zero_morphism := ZeroMorphism( Rows, zero_object, zero_object );
        
        merged_pairs :=
            COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZeroMorphism( Rows, pairs_1, pairs_2, zero_morphism );
        
        list_of_precomposed_pairs :=
            List( merged_pairs, pair ->
                Pair( PreCompose( Rows, pair[1], pair[2] ), pair[3] ) );
        
        return MorphismConstructor( Coproduct, Source( morphism_1 ), list_of_precomposed_pairs, Target( morphism_2 ) );
        
    end );
    
    ##
    AddZeroObject( Coproduct,
      function( Coproduct )
        
        return ObjectConstructor( Coproduct, CapJitTypedExpression( [ ], cat ->
                    CapJitDataTypeOfListOf(
                        CapJitDataTypeOfNTupleOf( 2,
                            CapJitDataTypeOfObjectOfCategory( UnderlyingCategoryOfRows( cat ) ),
                            IsBigInt ) ) ) );
        
    end );
    
    ##
    AddZeroMorphism( Coproduct,
      function( Coproduct, source, target )
        local Rows, pairs_1, pairs_2, merged_pairs, list_of_zero_morphism_pairs;
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        pairs_1 := ListOfPairsOfObjectAndIndex( source );
        pairs_2 := ListOfPairsOfObjectAndIndex( target );
        
        # Merge the source and target pairs.
        merged_pairs :=
            COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZeroObject( Rows, pairs_1, pairs_2, ZeroObject( Rows ) );
        
        list_of_zero_morphism_pairs :=
            List( merged_pairs, pair ->
                Pair( ZeroMorphism( Rows, pair[1], pair[2] ), pair[3] ) );
        
        return MorphismConstructor( Coproduct, source, list_of_zero_morphism_pairs, target );
        
    end );
    
    AddIsZeroForMorphisms( Coproduct,
      function( Coproduct, morphism )
        local Rows, pairs;
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        pairs := ListOfPairsOfMorphismAndIndex( morphism );
        
        return ForAll( pairs, pair -> IsZeroForMorphisms( Rows, pair[1] ) );
        
    end );
    
    AddAdditionForMorphisms( Coproduct,
      function( Coproduct, morphism_1, morphism_2 )
        local Rows, pairs_1, pairs_2, list_of_added_pairs;
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        pairs_1 := ListOfPairsOfMorphismAndIndex( morphism_1 );
        pairs_2 := ListOfPairsOfMorphismAndIndex( morphism_2 );
        
        list_of_added_pairs :=
            List( [ 1 .. Length( pairs_1 ) ], n ->
                Pair( AdditionForMorphisms( Rows, pairs_1[n][1], pairs_2[n][1] ),
                      pairs_1[n][2] ) );
        
        return MorphismConstructor( Coproduct, Source( morphism_1 ), list_of_added_pairs, Target( morphism_1 ) );
        
    end );
    
    ##
    AddSumOfMorphisms( Coproduct,
      function( Coproduct, source, morphisms, target )
        local Rows, matrix_of_pairs, sources, targets, zero, merged_pairs, list_of_summed_pairs;
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        matrix_of_pairs := List( morphisms, morphism -> ListOfPairsOfMorphismAndIndex( morphism ) );
        
        # matrix_of_pairs takes the following form:
        #
        # [ [ ... [m1,i], [m2,j], [m3,k], ... ]
        #   [ ... [m4,i], [m5,j], [m6,k], ... ]
        #   [ ... [m7,i], [m8,j], [m9,k], ... ] ]
        #
        # We sum over its columns.
        #
        # But note, that not all rows must have the same indices
        # i, j, k, etc. due to the sparse datastructure!
        # This is only for illustration.
        
        sources := ListOfPairsOfObjectAndIndex( source );
        targets := ListOfPairsOfObjectAndIndex( target );
        
        zero := ZeroObject( Rows );
        
        merged_pairs :=
            COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZeroObject( Rows, sources, targets, zero );
        
        # For each pair in merged_pairs:
        #   pair[1][1] gives the source for the morphisms in the same colum.
        #   pair[1][2] gives the target for the morphisms in the same colum.
        #   pair[2] gives the index.
        #
        # The variable 'n' below corresponds to the column indices in the above matrix.
        
        list_of_summed_pairs :=
            List( [ 1 .. Length( merged_pairs ) ], n ->
                Pair( SumOfMorphisms( Rows,
                                      merged_pairs[n][1],
                                      List( matrix_of_pairs, row -> row[n][1] ),
                                      merged_pairs[n][2] ),
                      merged_pairs[n][3] ) );
                
        return MorphismConstructor( Coproduct, source, list_of_summed_pairs, target );
        
    end );
    
    ##
    AddAdditiveInverseForMorphisms( Coproduct,
      function( Coproduct, morphism )
        local Rows, list_of_pairs;
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        list_of_pairs :=
            List( ListOfPairsOfMorphismAndIndex( morphism ), pair ->
                Pair( AdditiveInverseForMorphisms( Rows, pair[1] ),
                      pair[2] ) );
        
        return MorphismConstructor( Coproduct, Source( morphism ), list_of_pairs, Target( morphism ) );
        
    end );
    
    ##
    AddDirectSum( Coproduct,
      function( Coproduct, diagram )
        local Rows, merged_pairs, matrix_of_pairs, pairs_of_sums;
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        matrix_of_pairs := List( diagram, obj -> ListOfPairsOfObjectAndIndex( obj ) );
        
        merged_pairs :=
             COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfObjectAndIndex( Rows, matrix_of_pairs );
        
        pairs_of_sums := List( merged_pairs, pair -> Pair( DirectSum( Rows, pair[1] ), pair[2] ) );
        
        return ObjectConstructor( Coproduct, pairs_of_sums );
        
    end );
    
    ##
    AddDirectSumFunctorialWithGivenDirectSums( Coproduct,
      function( cat, direct_sum_source, source_diagram, morphism_diagram, target_diagram, direct_sum_target )
        local Rows, merged_pairs, source_pairs, target_pairs, matrix_of_pairs, pairs_of_sums;
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        matrix_of_pairs := List( morphism_diagram, obj -> ListOfPairsOfMorphismAndIndex( obj ) );
        
        merged_pairs :=
             COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfMorphismAndIndex( Rows, matrix_of_pairs );
        
        # We can not reuse 'source_diagram' and 'target_diagram'.
        # Due to the sparse datastructure they miss zero objects,
        # and we can not pass the list of sources/targets obtained
        # from them to DirectSumFunctorialWithGivenDirectSums( Rows, ... ).
        # 
        # So instead we get the complete list of sources/targets from
        # the morphisms in the category of rows.
        
        source_pairs := List( merged_pairs, pair -> List( pair[1], Source ) );
        
        target_pairs := List( merged_pairs, pair -> List( pair[1], Target ) );
        
        pairs_of_sums :=
            List( [ 1 .. Length( merged_pairs ) ], i ->
                Pair( DirectSumFunctorialWithGivenDirectSums( Rows,
                            Component( direct_sum_source, merged_pairs[i][2] ),
                            source_pairs[i],
                            merged_pairs[i][1],
                            target_pairs[i],
                            Component( direct_sum_target, merged_pairs[i][2] ) ),
                      merged_pairs[i][2] ) );
        
        return MorphismConstructor( Coproduct, direct_sum_source, pairs_of_sums, direct_sum_target );
        
    end );
    
    ##
    AddUniversalMorphismIntoDirectSumWithGivenDirectSum( Coproduct,
      function( Coproduct, diagram, test_object, morphisms, direct_sum )
        local Rows, zero, matrix_of_morphism_pairs, merged_morphism_pairs, test_pairs, matrix_of_diagram_pairs, merged_diagram_pairs, merged_test_and_diagram_pairs, list_of_universal_mors;
        
        # We give an example of the algorithm.
        # 
        # Let o1 := [ [s1,1], [s1,4] ] ∈ Coproduct
        #     o2 := [ [s2,3], [s2,4] ] ∈ Coproduct
        #     o3 := [ [s3,1], [s3,3] ] ∈ Coproduct
        # 
        # be the objects for 'diagram',
        # 
        # direct_sum := o1⊕ o2⊕ o3 = [ [ [ s1, s3 ], 1 ],
        #                              [ [ s2, s3 ], 3 ],
        #                              [ [ s1, s2 ], 4 ] ]
        # 
        # test_object := [ [ t2, 2 ], [ t3, 3 ] ] ∈ Coproduct,
        # 
        # and let the morphisms be given by the following lists of pairs of morphisms
        # in the category of rows (i.e. matrices) and the index of
        # the category of rows as a summand in the coproduct:
        # 
        # m1 : test_object -> o1,         m2 : test_object -> 02        m3 : test_object -> o3
        # 
        #      [ [ m11: 0xs1, 1 ],             [ [ m22: t2x0, 2 ],           [ [ m31: 0xs3, 1 ],
        #        [ m12: t2x0, 2 ],               [ m23: t3xs2, 3 ],            [ m32: t2x0, 2 ],
        #        [ m13: t3x0, 3 ],               [ m24: 0xs2, 4 ] ],           [ m33: t3xs3, 3 ] ],
        #        [ m14: 0xs1, 4 ] ],
        # 
        # We want to delegate the computations to the copies of the category of rows.
        # So we merge all the morphism pairs according to which summand of 'Coproduct' they belong,
        # i.e., by their indices:
        # 
        # [ [ [ m11, m31      ], 1 ],  # Morphisms in the first summand of Coproduct
        #   [ [ m12, m22, m32 ], 2 ],  # Morphisms in the second summand of Coproduct
        #   [ [ m13, m23, m33 ], 3 ],  # Morphisms in the third summand of Coproduct
        #   [ [ m14, m24      ], 4 ] ] # Morphisms in the fourth summand of Coproduct
        # 
        # Now we can call UniversalMorphismIntoDirectSumWithGivenDirectSum in the category of rows.
        # 
        # It remains to figure out the 'diagram', 'test_object' and 'direct_sum'
        # for these calls to UniversalMorphismIntoDirectSumWithGivenDirectSum
        # in the category of rows. For this reason we also merge the lists
        # of 'test_object' and o1, o2, o3.
        # 
        # [
        #   [ [ 0  ], [ s1, s3 ], 1 ],
        #   [ [ t2 ], [ 0      ], 2 ],
        #   [ [ t3 ], [ s2, s3 ], 3 ],
        #   [ [ 0  ], [ s1, s2 ], 4 ],
        # ]
        # 
        # We see, that
        #   - the number of rows is equal to the number of rows of the merged morphism pairs
        #   - in each row, the first list gives the source for the morphisms, i.e., the 'test_object'
        #   - in each row, the second list gives the targets for the morphisms, i.e., the 'diagram'
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        zero := ZeroObject( Rows );
        
        matrix_of_morphism_pairs :=
            List( morphisms, morphism -> ListOfPairsOfMorphismAndIndex( morphism ) );
        
        merged_morphism_pairs :=
             COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfMorphismAndIndex( Rows, matrix_of_morphism_pairs );
        
        # Wrap the objects in 'test_pairs' inside a list
        # so that the merge with 'merged_diagram_pairs' below
        # produces an output of the form
        # 
        # [
        #   [ list, list, index ],
        #            .
        #            .
        #            .
        #   [ list, list, index ]
        # ]
        # 
        test_pairs := ListOfPairsOfObjectAndIndex( test_object );
        test_pairs := List( test_pairs, pair -> Pair( [ pair[1] ], pair[2] ) );
        
        matrix_of_diagram_pairs := List( diagram, obj -> ListOfPairsOfObjectAndIndex( obj ) );
        
        merged_diagram_pairs :=
            COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfObjectAndIndex( Rows, matrix_of_diagram_pairs );
        
        merged_test_and_diagram_pairs :=
            COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZeroObjectInList( Rows, test_pairs, merged_diagram_pairs, [ zero ] );
        
        # Length( merged_sources_targets ) = Length( merged_morphism_pairs ).
        list_of_universal_mors :=
            List( [ 1 .. Length( merged_test_and_diagram_pairs ) ], n ->
                Pair( UniversalMorphismIntoDirectSumWithGivenDirectSum( Rows,
                            merged_test_and_diagram_pairs[n][2], # The second index has the list of merged_diagram_pairs or the list [ zero ].
                            merged_test_and_diagram_pairs[n][1][1], # The first index has the list of test_pairs or the list [ zero ]. Both are guaranted to be one-element lists, hence the '[1][1]'.
                            merged_morphism_pairs[n][1],
                            Component( direct_sum, merged_test_and_diagram_pairs[n][3] ) ), # The third entry is the number of the current summand in the coproduct of categories of rows.
                      merged_test_and_diagram_pairs[n][3] ) );
        
        return MorphismConstructor( Coproduct, test_object, list_of_universal_mors, direct_sum );
        
    end );
    
    ##
    AddUniversalMorphismFromDirectSumWithGivenDirectSum( Coproduct,
      function( Coproduct, diagram, test_object, morphisms, direct_sum )
        local Rows, zero, matrix_of_morphism_pairs, merged_morphism_pairs, test_pairs, matrix_of_diagram_pairs, merged_diagram_pairs, merged_diagram_and_test_pairs, list_of_universal_mors;
        
        # We give an example of the algorithm.
        # 
        # Let o1 := [ [s1,1], [s1,4] ] ∈ Coproduct
        #     o2 := [ [s2,3], [s2,4] ] ∈ Coproduct
        #     o3 := [ [s3,1], [s3,3] ] ∈ Coproduct
        # 
        # be the objects for 'diagram',
        # 
        # direct_sum := o1⊕ o2⊕ o3 = [ [ [ s1, s3 ], 1 ],
        #                              [ [ s2, s3 ], 3 ],
        #                              [ [ s1, s2 ], 4 ] ]
        # 
        # test_object := [ [ t2, 2 ], [ t3, 3 ] ] ∈ Coproduct,
        # 
        # and let the morphisms be given by the following lists of pairs of morphisms
        # in the category of rows (i.e. matrices) and the index of
        # the category of rows as a summand in the coproduct:
        # 
        # m1 : o1 -> test_object,        m2 : o2 -> test_object        m3 : o3 -> test_object
        # 
        #      [ [ m11: s1x0, 1 ],            [                             [ [ m31: s3x0,  1 ],
        #        [ m12: 0xt2, 2 ],              [ m22: 0xt2,  2 ],            [ m32: 0xt2,  2 ],
        #        [ m13: 0xt3, 3 ],              [ m23: s2xt3, 3 ],            [ m33: s3xt3, 3 ]
        #        [ m14: s1x0, 4 ] ],            [ m24: s2x0,  4 ] ],                            ]
        # 
        # We want to delegate the computations to the copies of the category of rows.
        # So we merge all the morphism pairs according to which summand of 'Coproduct' they belong,
        # i.e., by their indices:
        # 
        # [ [ [ m11, m31      ], 1 ],  # Morphisms in the first summand of Coproduct
        #   [ [ m12, m22, m32 ], 2 ],  # Morphisms in the second summand of Coproduct
        #   [ [ m13, m23, m33 ], 3 ],  # Morphisms in the third summand of Coproduct
        #   [ [ m14, m24      ], 4 ] ] # Morphisms in the fourth summand of Coproduct
        # 
        # Now we can call UniversalMorphismIntoDirectSumWithGivenDirectSum in the category of rows.
        # 
        # It remains to figure out the 'diagram', 'test_object' and 'direct_sum'
        # for these calls to UniversalMorphismIntoDirectSumWithGivenDirectSum
        # in the category of rows. For this reason we also merge the lists
        # of o1, o2, o3 and 'test_object'.
        # 
        # [
        #   [ [ s1, s3 ], [ 0  ], 1 ],
        #   [ [ 0      ], [ t2 ], 2 ],
        #   [ [ s2, s3 ], [ t3 ], 3 ],
        #   [ [ s1, s2 ], [ 0  ], 4 ],
        # ]
        # 
        # We see, that
        #   - the number of rows is equal to the number of rows of the merged morphism pairs
        #   - in each row, the first list gives the targets for the morphisms, i.e., the 'diagram'
        #   - in each row, the second list gives the source for the morphisms, i.e., the 'test_object'
        
        Rows := UnderlyingCategoryOfRows( Coproduct );
        
        zero := ZeroObject( Rows );
        
        matrix_of_morphism_pairs :=
            List( morphisms, morphism -> ListOfPairsOfMorphismAndIndex( morphism ) );
        
        merged_morphism_pairs :=
             COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfMorphismAndIndex( Rows, matrix_of_morphism_pairs );
        
        matrix_of_diagram_pairs := List( diagram, obj -> ListOfPairsOfObjectAndIndex( obj ) );
        
        merged_diagram_pairs :=
            COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfObjectAndIndex( Rows, matrix_of_diagram_pairs );
        
        # Wrap the objects in 'test_pairs' inside a list
        # so that the merge with 'merged_diagram_pairs' below
        # produces an output of the type
        # 
        # [
        #   [ list, list, index ],
        #            .
        #            .
        #            .
        #   [ list, list, index ]
        # ]
        # 
        test_pairs := ListOfPairsOfObjectAndIndex( test_object );
        test_pairs := List( test_pairs, pair -> Pair( [ pair[1] ], pair[2] ) );
        
        merged_diagram_and_test_pairs :=
            COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZeroObjectInList( Rows, merged_diagram_pairs, test_pairs, [ zero ] );
        
        # Length( merged_sources_targets ) = Length( merged_morphism_pairs ).
        list_of_universal_mors :=
            List( [ 1 .. Length( merged_diagram_and_test_pairs ) ], n ->
                Pair( UniversalMorphismFromDirectSumWithGivenDirectSum( Rows,
                            merged_diagram_and_test_pairs[n][1], # The first index has the list of merged_diagram_pairs or the list [ zero ].
                            merged_diagram_and_test_pairs[n][2][1], # The second index has the list of test_pairs or the list [ zero ]. Both are guaranted to be one-element lists, hence the '[1][1]'.
                            merged_morphism_pairs[n][1],
                            Component( direct_sum, merged_diagram_and_test_pairs[n][3] ) ), # The third entry is the index of the current summand in the coproduct of categories of rows.
                      merged_diagram_and_test_pairs[n][3] ) );
        
        return MorphismConstructor( Coproduct, direct_sum, list_of_universal_mors, test_object );
        
    end );
    
    # AddComponentOfMorphismIntoDirectSum( Coproduct,
    #   function( Coproduct, morphism, summands, nr )
    #     local Rows, target_summand, pairs_of_target_summand, pairs_of_target_summand_with_marked_row_objects, support_of_target_summand, matrix_of_pairs_of_all_summands, merged_summands, flattened_merged_summands, numbers, morphism_pairs, list_of_component_morphisms;
    #
    #     Rows := UnderlyingCategoryOfRows( Coproduct );
    #
    #     target_summand := summands[ nr ];
    #
    #     support_of_target_summand := Support( target_summand );
    #
    #     pairs_of_target_summand := ListOfPairsOfObjectAndIndex( target_summand );
    #
    #     # Wrap the row objects of our target summand in lists.
    #     pairs_of_target_summand_with_marked_row_objects :=
    #         List( pairs_of_target_summand, pair -> [ [ pair[1] ], pair[2] ] );
    #
    #     matrix_of_pairs_of_all_summands :=
    #         Concatenation(
    #             List( summands{[ 1 .. nr - 1 ]}, summand -> ListOfPairsOfObjectAndIndex( summand ) ),
    #             [ pairs_of_target_summand_with_marked_row_objects ],
    #             List( summands{[ nr + 1 .. Length( summands ) ]}, summand ->
    #                 ListOfPairsOfObjectAndIndex( summand ) ) );
    #
    #     merged_summands :=
    #         COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairs( Rows, matrix_of_pairs_of_all_summands );
    #
    #     # Only keep the merged summands neccessary for the wanted summand.
    #     # This could also be done before merging (but would increase the complexity).
    #     merged_summands := Filtered( merged_summands, pair -> pair[2] in support_of_target_summand );
    #
    #     # Find the positions of the target summands in the merged lists
    #     # They were previously wrapped inside lists.
    #     numbers := List( merged_summands, row_objects -> PositionProperty( row_objects, IsList ) );
    #
    #     # Remove the wrapping via lists of the row objects of 'target_summand'.
    #     flattened_merged_summands := List( merged_summands, pair -> [ Flat( pair[1] ), pair[2] ] );
    #
    #     morphism_pairs :=
    #         Filtered( ListOfPairsOfMorphismAndIndex( morphism ), mor ->
    #             mor[2] in support_of_target_summand );
    #
    #     list_of_component_morphisms :=
    #         List( [ 1 .. Length( support_of_target_summand ) ], n ->
    #             Pair( ComponentOfMorphismIntoDirectSum( Rows,
    #                         morphism_pairs[n][1],
    #                         flattened_merged_summands[n][1],
    #                         numbers[n] ),
    #                   support_of_target_summand[n] ) );
    #
    #     return MorphismConstructor( Coproduct,
    #                                 Source( morphism ),
    #                                 list_of_component_morphisms,
    #                                 target_summand );
    #
    # end );
    
    Rows := UnderlyingCategoryOfRows( Coproduct );
    
    if CanCompute( Rows, "MultiplyWithElementOfCommutativeRingForMorphisms" ) then
      
      AddMultiplyWithElementOfCommutativeRingForMorphisms( Coproduct,
        function( Coproduct, r, alpha )
          local Rows, multiplied_morphisms;
          
          Rows := UnderlyingCategoryOfRows( Coproduct );
          
          multiplied_morphisms :=
              List( ListOfPairsOfMorphismAndIndex( alpha ), pair ->
                      Pair( MultiplyWithElementOfCommutativeRingForMorphisms( Rows, r, pair[1] ),
                            pair[2] ) );
          
          return MorphismConstructor( Coproduct, Source( alpha ), multiplied_morphisms, Target( alpha ) );
          
      end );
      
    fi;
    
    ####################################
    ## Abelian structure
    ####################################
    
    if IsAbelianCategory( Rows ) then
        
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
    
end );

####################################
##
## Attributes
##
####################################

InstallMethodForCompilerForCAP( Components,
                                [ IsObjectInCoproductOfCategoryOfRowsWithSparseDatastructure ],
                                
  function( object )
    
    return List( ListOfPairsOfObjectAndIndex( object ), pair -> pair[1] );
    
end );

InstallMethodForCompilerForCAP( Components,
                                [ IsMorphismInCoproductOfCategoryOfRowsWithSparseDatastructure ],
                                
  function( morphism )
    
    return List( ListOfPairsOfMorphismAndIndex( morphism ), pair -> pair[1] );
    
end );

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
    local Rows, pairs, source_list, target_list, source, target;
    
    Rows := UnderlyingCategoryOfRows( Coproduct );
    
    # List of integers?
    if ForAll( list, i -> IsBigInt( i ) ) and Length( list ) = NrOfSummandsOfCoproduct( Coproduct ) then
        
        pairs :=
            ListWithKeys( list, { index, element } -> [ CategoryOfRowsObject( Rows, element ), index ] );
        
        # Only keep the non-zero entries.
        pairs :=
            Filtered( pairs, pair -> RankOfObject( pair[1] ) > 0 );
        
        return ObjectConstructor( Coproduct, pairs );
        
    # List of matrices?
    elif ForAll( list, m -> IsHomalgMatrix( m ) ) and Length( list ) = NrOfSummandsOfCoproduct( Coproduct ) then
        
        pairs :=
            ListWithKeys( list, { index, matrix } -> [ AsCategoryOfRowsMorphism( Rows, matrix ), index ] );
        
        source_list := List( pairs, pair ->
            [ Source( pair[1] ), pair[2] ] );
        
        target_list := List( pairs, pair ->
            [ Target( pair[1] ), pair[2] ] );
        
        source := ObjectConstructor( Coproduct, source_list );
        target := ObjectConstructor( Coproduct, target_list );
        
        # Now only keep the morphisms whose underlying matrix is not a 0x0 matrix.
        # Needs to be done after constructing 'source' and 'range', otherwise we lose information.
        pairs :=
            Filtered( pairs, pair ->
                IsZeroForObjects( Rows, Source( pair[1] ) ) = false or
                IsZeroForObjects( Rows, Target( pair[1] ) ) = false );
        
        return MorphismConstructor( Coproduct, source, pairs, target );
        
    # List of pairs of integers?
    elif ForAll( list, pair -> IsBigInt( pair[1] ) and IsBigInt( pair[2] ) ) then
        
        pairs := List( list, pair -> [ CategoryOfRowsObject( Rows, pair[1] ), pair[2] ] );
        
        return ObjectConstructor( Coproduct, pairs );
        
    # List of pairs of matrices?
    elif ForAll( list, pair -> IsHomalgMatrix( pair[1] ) and IsBigInt( pair[2] ) ) then
        
        source_list := List( list, pair -> [ CategoryOfRowsObject( Rows, NrRows( pair[1] ) ), pair[2] ] );
        target_list := List( list, pair -> [ CategoryOfRowsObject( Rows, NrCols( pair[1] ) ), pair[2] ] );
        
        source := ObjectConstructor( Coproduct, source_list );
        target := ObjectConstructor( Coproduct, target_list );
        
        pairs := List( list, pair -> [ AsCategoryOfRowsMorphism( Rows, pair[1] ), pair[2] ] );
        
        return MorphismConstructor( Coproduct, source, pairs, target );
        
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

# Merge sort strategy.
COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZero :=
  function( Rows, list1, list2, zero )
    local merged_list, i, j, len1, len2, current_key, val;
    
    merged_list := [];
    
    i := 1; # Pointer for list1
    j := 1; # Pointer for list2
    
    len1 := Length( list1 );
    len2 := Length( list2 );
    
    while i <= len1 or j <= len2 do
        
        val := [];
        
        # Case 1: key from list1 is smaller OR list2 is exhausted.
        if i <= len1 and (j > len2 or list1[i][2] < list2[j][2]) then
            
            current_key := list1[i][2];
            
            Add( val, list1[i][1] );
            Add( val, zero );
            
            i := i + 1;
            
        # Case 2: key from list2 is strictly smaller OR list1 is exhausted.
        elif j <= len2 and (i > len1 or list2[j][2] < list1[i][2]) then
            
            current_key := list2[j][2];
            
            Add( val, zero );
            Add( val, list2[j][1] );
            
            j := j + 1;
            
        # Case 3: keys are equal.
        else
            
            current_key := list1[i][2];
            
            Add( val, list1[i][1] );
            Add( val, list2[j][1] );
            
            i := i + 1;
            j := j + 1;
            
        fi;
        
        Add( merged_list, [ val[1], val[2], current_key ] );
        
    od;
    
    return merged_list;
    
end;

InstallGlobalFunction( "COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZeroObject", COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZero );

InstallGlobalFunction( "COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZeroMorphism", COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZero );

InstallGlobalFunction( "COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZeroObjectInList", COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZero );

# Uses a k-way merge.
COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairs :=
  function( Rows, matrix_of_pairs )
    local num_lists, merged_map, indices, active_pairs, minKey, pair, colliding_pairs, combined_val;
    
    num_lists := Length( matrix_of_pairs );
    
    if num_lists = 0 then return []; fi;
    
    merged_map := [];
    
    # Tracks the current index for each list
    indices := List( [ 1 .. num_lists ], k -> 1 );
    
    while true do
        
        # 1. Identify all currently "active" pairs (the heads of the lists)
        # Format: [ [value, key], listIndex ]
        active_pairs := List( [ 1 .. num_lists ], function( k )
            if indices[k] <= Length(matrix_of_pairs[k]) then
                return [ matrix_of_pairs[k][indices[k]], k ];
            else
                # Mark an exhausted list.
                return fail;
            fi;
        end );
        
        active_pairs := Filtered( active_pairs, p -> p <> fail );
        
        if IsEmpty(active_pairs) then break; fi;
        
        # 2. Find the minimum key across all active lists
        minKey := Minimum( List( active_pairs, p -> p[1][2] ) );
        
        # 3. Find all pairs matching the minimum key and collect their values
        # Colliding pairs are filtered from active_pairs
        colliding_pairs := Filtered( active_pairs, p -> p[1][2] = minKey );
        
        # Combine all first elements (values) into a single list
        combined_val := Concatenation( List( colliding_pairs, p -> [ p[1][1] ] ) );
        
        # 4. Add the combined result
        Add( merged_map, [ combined_val, minKey ] );
        
        # 5. Advance the index pointer for every list that contributed
        for pair in colliding_pairs do
            indices[pair[2]] := indices[pair[2]] + 1;
        od;
    od;
    
    return merged_map;
    
end;

InstallGlobalFunction( "COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfObjectAndIndex",
    COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairs );

InstallGlobalFunction( "COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfMorphismAndIndex",
    COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairs );

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
                                     "Component ", String( pair[2] ),
                                     ": a ", String( 0 ), " x ", String( nr_cols ),
                                     " morphism in ",
                                     Name( UnderlyingCategoryOfRows( CapCategory( morphism ) ) ), "\n\n" );
            
            continue;
            
        fi;
        
        nr_cols := RankOfObject( Target( rows_morphism ) );
        
        # nx0 morphism in category of rows?
        if nr_cols = 0 then
            
            string := Concatenation( string,
                                     "Component ", String( pair[2] ),
                                     ": a ", String( nr_rows ), " x ", String( 0 ),
                                     " morphism in ",
                                     Name( UnderlyingCategoryOfRows( CapCategory( morphism ) ) ), "\n\n" );
            
            continue;
            
        fi;
        
        string := Concatenation( string,
                                 "Component ", String( pair[2] ),
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

