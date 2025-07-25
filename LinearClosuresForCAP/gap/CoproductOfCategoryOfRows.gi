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
InstallMethod( CoproductOfCategoryOfRows,
               [ IsHomalgRing, IsInt ],
               
  FunctionWithNamedArguments(
  [
    [ "FinalizeCategory", true ],
  ],
  function( CAP_NAMED_ARGUMENTS, homalg_ring, nr_summands )
    local D, L, AC_disc, object_datum_type, object_datum, object_constructor, morphism_datum, morphism_datum_type, morphism_constructor, modeling_tower_object_constructor, modeling_tower_object_datum, modeling_tower_morphism_constructor, modeling_tower_morphism_datum, SubscriptDigits, ToSubscript, name, CoproductOfCatOfRows;
    
    if nr_summands <= 0 then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "the number of summands of the coproduct category must be at least 1\n" );
        
    fi;
    
    D := FiniteSkeletalDiscreteCategory( [ 1 .. nr_summands ] : FinalizeCategory := true );
    
    L := LinearClosure( homalg_ring, D : FinalizeCategory := true );
    
    AC_disc := AdditiveClosureOfObjectFiniteDisconnectedCategory( L : FinalizeCategory := false );
    
    Finalize( AC_disc );
    
    ####################################
    # Reinterpretation
    ####################################
    
    ##
    object_datum_type := CapJitDataTypeOfNTupleOf( 2, IsBigInt, CapJitDataTypeOfListOf( IsBigInt ) );
    
    ##
    object_datum := { coproduct_rows, obj } -> SumOfRanksAndRanks( obj );
    
    ##
    object_constructor :=
      function( coproduct_rows, sum_of_ranks_and_ranks )
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0,
                IsList( sum_of_ranks_and_ranks ) and
                Length( sum_of_ranks_and_ranks ) = 2 and
                IsList( sum_of_ranks_and_ranks[2] ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        if sum_of_ranks_and_ranks[1] <> Sum( sum_of_ranks_and_ranks[2] ) then
            
            # COVERAGE_IGNORE_NEXT_LINE
            Error( "the first entry has to be the sum of all multiplicities\n" );
            
        fi;
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        if Length( sum_of_ranks_and_ranks[2] ) <> nr_summands then
            
            # COVERAGE_IGNORE_NEXT_LINE
            Error( "the length of the multiplicities list has to be equal to the number of objects in the underlying category\n" );
            
        fi;
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        if ForAny( sum_of_ranks_and_ranks[2], rank -> not IsInt( rank ) or rank < 0 ) then
            
            # COVERAGE_IGNORE_NEXT_LINE
            Error( "the entries of the multiplicity list must be non-negative integers\n" );
            
        fi;
        
        return CreateCapCategoryObjectWithAttributes( coproduct_rows,
                       SumOfRanksAndRanks, sum_of_ranks_and_ranks );
        
    end;
    
    ##
    morphism_datum_type := CapJitDataTypeOfListOf( IsHomalgMatrix );
    
    ##
    morphism_datum := { coproduct_rows, phi } -> ListOfMatrices( phi );
    
    morphism_constructor :=
      function( coproduct_rows, S, list_of_matrices, T )
        local nr_summands, matrix, i;
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, IsList( list_of_matrices ) );
        
        nr_summands := NrOfSummandsOfCoproduct( coproduct_rows );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        if nr_summands <> Length( list_of_matrices ) then
            
            # COVERAGE_IGNORE_NEXT_LINE
            Error( Concatenation( "the number of matrices must be equal to ",
                                  "the number of copies of the category of rows\n" ) );
            
        fi;
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        for i in [ 1 .. nr_summands ] do
            
            matrix := list_of_matrices[i];
            
            if not IsHomalgMatrix( matrix ) then
                
                # COVERAGE_IGNORE_NEXT_LINE
                Error( "all matrices must be Homalg matrices\n" );
                
            fi;
            
            if HomalgRing( matrix ) <> UnderlyingRing( coproduct_rows ) then
                
                # COVERAGE_IGNORE_NEXT_LINE
                Error( "all matrices must be defined over the same ring as the category\n" );
                
            fi;
            
            if NrRows( matrix ) <> Ranks( S )[i] then
                
                # COVERAGE_IGNORE_NEXT_LINE
                Error( Concatenation( "<matrix> must have ",
                                      String( Ranks( S )[i] ),
                                      " rows\n" ) );
                
            fi;
            
            if NrColumns( matrix ) <> Ranks( T )[i] then
                
                # COVERAGE_IGNORE_NEXT_LINE
                Error( Concatenation( "<matrix> must have ",
                                      String( Ranks( T )[i] ),
                                      " columns\n" ) );
                
            fi;
            
        od;
        
        return CreateCapCategoryMorphismWithAttributes( coproduct_rows,
                                                        S,
                                                        T,
                                                        ListOfMatrices, list_of_matrices );
        
    end;
    
    ####################################
    # Modeling
    ####################################
    
    ## From the raw object data to the object in the modeling category.
    modeling_tower_object_constructor :=
      function( coproduct_rows, sum_of_ranks_and_ranks )
        local AC_disc;
        
        # Checks are done in the modeling category.
        AC_disc := ModelingCategory( coproduct_rows );
        
        return ObjectConstructor( AC_disc, sum_of_ranks_and_ranks );
        
    end;
    
    ## From the object in the modeling category to the raw object data.
    modeling_tower_object_datum := { coproduct_rows, object } -> NrSummandsAndMultiplicities( object );
    
    ## From the raw morphism data to the morphism in the modeling category.
    modeling_tower_morphism_constructor :=
      function( coproduct_rows, S, list_of_homalg_matrices, T )
        local AC_disc, L, D, underlying_disconnected_objects, list_of_matrices, i, matrix, nr_rows, nr_cols, source, range, matrix_entries, listlist, obj_D, obj_L, id_obj_D;
        
        Assert( 0, Length( list_of_homalg_matrices ) = NrOfSummandsOfCoproduct( coproduct_rows ) );
        
        AC_disc := ModelingCategory( coproduct_rows );
        
        L := UnderlyingCategory( AC_disc );
        
        D := UnderlyingCategory( L );
        
        underlying_disconnected_objects := SetOfObjectsOfCategory( D );
        
        list_of_matrices := [];
        
        for i in [ 1 .. Length( list_of_homalg_matrices ) ] do
            
            matrix := list_of_homalg_matrices[i];
            
            if not IsHomalgMatrix( matrix ) then
                
                # COVERAGE_IGNORE_NEXT_LINE
                Error( "all matrices must be homalg matrices\n" );
                
            fi;
            
            if not IsIdenticalObj( HomalgRing( matrix ), UnderlyingRing( coproduct_rows ) ) then
                
                # COVERAGE_IGNORE_NEXT_LINE
                Error( "the matrix is defined over a different ring than the category" );
                
            fi;
            
            if NrRows( matrix ) <> Multiplicities( S )[i] then
                
                # COVERAGE_IGNORE_NEXT_LINE
                Error( Concatenation( "the number of rows of the matrix at index ",
                                      String( i ),
                                      " has to be equal to the multiplicity at the same index ",
                                      "of the source\n" ) );
                
            fi;
            
            if NrColumns( matrix ) <> Multiplicities( T )[i] then
                
                # COVERAGE_IGNORE_NEXT_LINE
                Error( Concatenation( "the number of rows of the matrix at index ",
                                      String( i ),
                                      " has to be equal to the multiplicity at the same index ",
                                      "of the target\n" ) );
                
            fi;
            
            nr_rows := NrRows( matrix );
            nr_cols := NrCols( matrix );
            
            matrix_entries := EntriesOfHomalgMatrixAsListList( matrix );
            
            obj_D := underlying_disconnected_objects[i];
            
            id_obj_D := IdentityMorphism( D, obj_D );
            
            obj_L := LinearClosureObject( L, obj_D );
            
            # Turn the matrix entries 'c' into coefficients: c*IdentityMorphism.
            listlist :=
                List( matrix_entries,
                    row -> List( row,
                        c -> LinearClosureMorphismNC( L, obj_L, [ c ], [ id_obj_D ], obj_L ) ) );
            
            #% CAP_JIT_DROP_NEXT_STATEMENT
            Assert( 0, Length( listlist ) = Multiplicities( S )[i] );
            
            #% CAP_JIT_DROP_NEXT_STATEMENT
            Assert( 0, ForAll( listlist, row -> Length( row ) = Multiplicities( T )[i] ) );
            
            Append( list_of_matrices, [ listlist ] );
            
        od;
        
        return MorphismConstructor( AC_disc, S, list_of_matrices, T );
        
    end;
    
    # From the morphism in the modeling category to the raw morphism data.
    modeling_tower_morphism_datum :=
      function ( coproduct_rows, morphism )
        local list_of_matrices, list_of_homalg_matrices, source_multiplicities, target_multiplicities, i, matrix, matrix_to_list, nr_rows, nr_cols, homalg_matrix;
        
        list_of_matrices := ListOfMatrices( morphism );
        
        list_of_homalg_matrices := [];
        
        source_multiplicities := Multiplicities( Source( morphism ) );
        
        target_multiplicities := Multiplicities( Target( morphism ) );
        
        for i in [ 1 .. Length( list_of_matrices ) ] do
            
            matrix := list_of_matrices[i];
            
            # All entries are of the form: c_1*IdentityMorphism( L, i ) + ... + c_n*IdentityMorphism( L, i )
            # over the same identity morphism.
            # Because LinearClosure has a lazy datastructure, we need to sum over all the coefficients c_i ourself.
            matrix_to_list :=
                List( matrix,
                    row -> List( row, mor -> Sum( CoefficientsList( mor ) ) ) );
            
            nr_rows := source_multiplicities[i];
            
            nr_cols := target_multiplicities[i];
            
            homalg_matrix := HomalgMatrixListList( matrix_to_list,
                                                   nr_rows,
                                                   nr_cols,
                                                   UnderlyingRing( coproduct_rows ) );
            
            Append( list_of_homalg_matrices, [ homalg_matrix ] );
            
        od;
        
        return list_of_homalg_matrices;
        
    end;
    
    name := Concatenation( "⊕ ( ", "CategoryOfRows( ", RingName( homalg_ring ), " ), ", String( nr_summands ), " )" );
    
    CoproductOfCatOfRows :=
        ReinterpretationOfCategory( AC_disc,
            rec( name := name,
                 category_filter := IsCoproductOfCategoryOfRows,
                 category_object_filter := IsObjectInCoproductOfCategoryOfRows,
                 category_morphism_filter := IsMorphismInCoproductOfCategoryOfRows,
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
        
        SetIsAbelianCategory( CoproductOfCatOfRows, true );
        
    fi;
    
    SetNrOfSummandsOfCoproduct( CoproductOfCatOfRows, nr_summands );
    
    SetUnderlyingRing( CoproductOfCatOfRows, homalg_ring );
    
    CoproductOfCatOfRows!.compiler_hints.category_attribute_names := [
        "NrOfSummandsOfCoproduct",
        "UnderlyingRing",
    ];
    
    # CoproductOfCatOfRows!.compiler_hints.source_and_range_attributes_from_morphism_attribute := rec(
    #     object_attribute_name := "SumOfRanksAndRanks",
    #     morphism_attribute_name := "ListOfMatrices",
    # );
    
    ####################################
    ## Abelian structure
    ####################################
    
    if IsFieldForHomalg( homalg_ring ) then
        
        AddKernelObject( CoproductOfCatOfRows,
          function( CoproductOfCatOfRows, morphism )
            local row_ranks_of_matrices, kernel_dimensions;
            
            row_ranks_of_matrices := List( ListOfMatrices( morphism ), matrix -> RowRankOfMatrix( matrix ) );
            
            kernel_dimensions := Ranks( Source( morphism ) ) - row_ranks_of_matrices;
            
            return ObjectConstructor( CoproductOfCatOfRows, [ Sum( kernel_dimensions ), kernel_dimensions ] );
            
        end );
        
        ##
        AddKernelEmbedding( CoproductOfCatOfRows,
          function( CoproductOfCatOfRows, morphism )
            local row_syzygies_of_matrices, nr_rows_of_matrices, kernel_object;
            
            row_syzygies_of_matrices := List( ListOfMatrices( morphism ), matrix -> SyzygiesOfRows( matrix ) );
            
            nr_rows_of_matrices := List( row_syzygies_of_matrices, matrix -> NrRows( matrix ) );
            
            kernel_object := ObjectConstructor( CoproductOfCatOfRows, [ Sum( nr_rows_of_matrices ), nr_rows_of_matrices ] );
            
            return MorphismConstructor( CoproductOfCatOfRows, kernel_object, row_syzygies_of_matrices, Source( morphism ) );
            
        end );
        
        ##
        AddKernelEmbeddingWithGivenKernelObject( CoproductOfCatOfRows,
          function( CoproductOfCatOfRows, morphism, kernel_object )
            local row_syzygies_of_matrices;
            
            row_syzygies_of_matrices := List( ListOfMatrices( morphism ), matrix -> SyzygiesOfRows( matrix ) );
            
            return MorphismConstructor( CoproductOfCatOfRows, kernel_object, row_syzygies_of_matrices, Source( morphism ) );
            
        end );
        
        ##
        AddLift( CoproductOfCatOfRows,
          function( CoproductOfCatOfRows, alpha, beta )
            local list_of_matrices_alpha, list_of_matrices_beta, lifts;
            
            list_of_matrices_alpha := ListOfMatrices( alpha );
            
            list_of_matrices_beta := ListOfMatrices( beta );
            
            lifts :=
                List( [ 1 .. NrOfSummandsOfCoproduct( CoproductOfCatOfRows ) ], i ->
                    SafeRightDivide( list_of_matrices_alpha[i], list_of_matrices_beta[i] ) );
            
            return MorphismConstructor( CoproductOfCatOfRows, Source( alpha ), lifts, Source( beta ) );
            
        end );
        
        ##
        AddCokernelObject( CoproductOfCatOfRows,
          function( CoproductOfCatOfRows, morphism )
            local row_ranks_of_matrices, cokernel_dimensions;
            
            row_ranks_of_matrices := List( ListOfMatrices( morphism ), matrix -> RowRankOfMatrix( matrix ) );
            
            cokernel_dimensions := Ranks( Target( morphism ) ) - row_ranks_of_matrices;
            
            return ObjectConstructor( CoproductOfCatOfRows, [ Sum( cokernel_dimensions ), cokernel_dimensions ] );
            
        end );
        
        ##
        AddCokernelProjection( CoproductOfCatOfRows,
          function( CoproductOfCatOfRows, morphism )
            local col_syzygies_of_matrices, nr_cols_of_matrices, cokernel_object;
            
            col_syzygies_of_matrices := List( ListOfMatrices( morphism ), matrix -> SyzygiesOfColumns( matrix ) );
            
            nr_cols_of_matrices := List( col_syzygies_of_matrices, matrix -> NrColumns( matrix ) );
            
            cokernel_object := ObjectConstructor( CoproductOfCatOfRows, [ Sum( nr_cols_of_matrices ), nr_cols_of_matrices ] );
            
            return MorphismConstructor( CoproductOfCatOfRows, Target( morphism ), col_syzygies_of_matrices, cokernel_object );
            
        end );

        ##
        AddCokernelProjectionWithGivenCokernelObject( CoproductOfCatOfRows,
          function( CoproductOfCatOfRows, morphism, cokernel_object )
            local col_syzygies_of_matrices;
            
            col_syzygies_of_matrices := List( ListOfMatrices( morphism ), matrix -> SyzygiesOfColumns( matrix ) );
            
            return MorphismConstructor( CoproductOfCatOfRows, Target( morphism ), col_syzygies_of_matrices, cokernel_object );
            
        end );

        ##
        AddColift( CoproductOfCatOfRows,
          function( CoproductOfCatOfRows, alpha, beta )
            local list_of_matrices_alpha, list_of_matrices_beta, colifts;
            
            list_of_matrices_alpha := ListOfMatrices( alpha );
            
            list_of_matrices_beta := ListOfMatrices( beta );
            
            colifts :=
                List( [ 1 .. NrOfSummandsOfCoproduct( CoproductOfCatOfRows ) ], i ->
                    SafeLeftDivide( list_of_matrices_alpha[i], list_of_matrices_beta[i] ) );
            
            return MorphismConstructor( CoproductOfCatOfRows, Target( alpha ), colifts, Target( beta ) );
            
        end );
    
    fi;
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        
        Finalize( CoproductOfCatOfRows );
        
    fi;
    
    return CoproductOfCatOfRows;
    
end ) );

####################################
##
## Operations
##
####################################

InstallMethodForCompilerForCAP( SumOfRanks,
                                [ IsObjectInCoproductOfCategoryOfRows ],
                                
  function( object )

    return SumOfRanksAndRanks( object )[1];

end );

InstallMethodForCompilerForCAP( Ranks,
                                [ IsObjectInCoproductOfCategoryOfRows ],
                                
  function( object )
    
    return SumOfRanksAndRanks( object )[2];
    
end );

##
InstallMethodForCompilerForCAP( \[\],
                                [ IsObjectInCoproductOfCategoryOfRows, IsInt ],
                                
  function( object, i )
    
    if i < 1 or i > NrOfSummandsOfCoproduct( CapCategory( object ) ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "out of bounds\n" );
        
    fi;
    
    return Ranks( object )[i];
    
end );

##
InstallMethodForCompilerForCAP( \[\],
                                [ IsMorphismInCoproductOfCategoryOfRows, IsInt ],
                                
  function( morphism, i )
    
    if i < 1 or i > NrOfSummandsOfCoproduct( CapCategory( morphism ) ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "out of bounds\n" );
        
    fi;
    
    return ListOfMatrices( morphism )[i];
    
end );

####################################
##
## View & Display
##
####################################

