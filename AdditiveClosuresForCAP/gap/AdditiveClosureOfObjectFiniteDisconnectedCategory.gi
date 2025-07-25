# SPDX-License-Identifier: GPL-2.0-or-later
# FiniteCocompletions: Finite (co)product/(co)limit (co)completions
#
# Implementations
#

####################################
##
## Constructors
##
####################################

##
InstallMethod( AdditiveClosureOfObjectFiniteDisconnectedCategory,
               [ IsCapCategory ],
               ADDITIVE_CLOSURE_OF_OBJECT_FINITE_DISCONNECTED_CATEGORY
);

##
InstallMethod( ADDITIVE_CLOSURE_OF_OBJECT_FINITE_DISCONNECTED_CATEGORY,
               [ IsCapCategory ],
               
  FunctionWithNamedArguments(
  [
    [ "FinalizeCategory", true ],
  ],
  function( CAP_NAMED_ARGUMENTS, underlying_category )
    local object_datum_type, morphism_datum_type, DAC, name, object_constructor, object_datum, morphism_constructor, morphism_datum, compare_morphisms;
    
    Assert( 0, HasIsAbCategory( underlying_category ) and
               IsAbCategory( underlying_category ) );
    
    Assert( 0, HasIsObjectFiniteCategory( underlying_category ) and
               IsObjectFiniteCategory( underlying_category ) );
    
    ##
    object_datum_type :=
        CapJitDataTypeOfNTupleOf( 2,
            IsBigInt,
            CapJitDataTypeOfListOf( IsBigInt ) );
    
    ##
    morphism_datum_type :=
        CapJitDataTypeOfListOf(
            CapJitDataTypeOfListOf(
                CapJitDataTypeOfListOf(
                    CapJitDataTypeOfMorphismOfCategory( underlying_category ) ) ) );
   
    name := Concatenation( "AdditiveClosureOfObjectFiniteDisconnectedCategory( ", Name( underlying_category )," )" );
    
    DAC := CreateCapCategoryWithDataTypes( name,
                                           IsAdditiveClosureOfObjectFiniteDisconnectedCategory,
                                           IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory,
                                           IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategory,
                                           IsCapCategoryTwoCell,
                                           object_datum_type,
                                           morphism_datum_type,
                                           fail );
    
    DAC!.supports_empty_limits := true;
    
    DAC!.compiler_hints :=
      rec( category_attribute_names :=
          [ "UnderlyingCategory",
            "ListOfObjectsOfUnderlyingCategory",
            "NumberOfObjectsOfUnderlyingCategory",] );
    
    
    if HasIsSkeletalCategory( underlying_category ) and IsSkeletalCategory( underlying_category ) then
        
        SetIsSkeletalCategory( DAC, true );
        
    fi;
    
    SetUnderlyingCategory( DAC, underlying_category );
    
    SetListOfObjectsOfUnderlyingCategory( DAC, SetOfObjectsOfCategory( underlying_category ) );
    
    SetNumberOfObjectsOfUnderlyingCategory( DAC, Length( SetOfObjectsOfCategory( underlying_category ) ) );
    
    ##
    AddObjectDatum( DAC,
      function( DAC, object )
        
        return NrSummandsAndMultiplicities( object );
        
    end );
    
    ##
    AddObjectConstructor( DAC,
      function( DAC, nr_summands_and_multiplicities )
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0,
            nr_summands_and_multiplicities[1] = Sum( nr_summands_and_multiplicities[2] ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0,
            Length( nr_summands_and_multiplicities[2] ) =
            Length( SetOfObjectsOfCategory( underlying_category ) ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAll( nr_summands_and_multiplicities[2], rank -> rank >= 0 ) );
        
        return CreateCapCategoryObjectWithAttributes( DAC,
                       NrSummandsAndMultiplicities, nr_summands_and_multiplicities );
        
    end );
    
    ##
    AddMorphismDatum( DAC,
      function( DAC, morphism )
        
        return ListOfMatrices( morphism );
        
    end );
    
    ##
    AddMorphismConstructor( DAC,
      function( DAC, S, list_of_matrices, T )
        local i, matrix, row;
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( list_of_matrices ) = NumberOfObjectsOfUnderlyingCategory( DAC ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        for i in [ 1 .. Length( list_of_matrices ) ] do
            
            matrix := list_of_matrices[i];
            
            Assert( 0, Length( matrix ) = Multiplicities( S )[i] );
            
            Assert( 0, ForAll( matrix, row -> Length( row ) = Multiplicities( T )[i] ) );
            
        od;
        
        return CreateCapCategoryMorphismWithAttributes( DAC,
                                                        S,
                                                        T,
                                                        ListOfMatrices, list_of_matrices );
        
    end );
    
    AddIsEqualForObjects( DAC,
      function( DAC, object_1, object_2 )
        
        return NrSummandsAndMultiplicities( object_1 ) = NrSummandsAndMultiplicities( object_2 );
        
    end );
    
    compare_morphisms :=
      function( cat, morphism_1, morphism_2, comparison_function )
        local nr_matrices, nr_rows_1, nr_rows_2, nr_cols_1, nr_cols_2;
        #% CAP_JIT_RESOLVE_FUNCTION
        
        underlying_category := UnderlyingCategory( cat );
        nr_matrices := NumberOfObjectsOfUnderlyingCategory( cat );
        
        nr_rows_1 := Multiplicities( Source( morphism_1 ) );
        nr_rows_2 := Multiplicities( Source( morphism_2 ) );
        
        nr_cols_1 := Multiplicities( Target( morphism_1 ) );
        nr_cols_2 := Multiplicities( Target( morphism_2 ) );
        
        if nr_rows_1 <> nr_rows_2 then
            
            return false;
            
        elif nr_cols_1 <> nr_cols_2 then
            
            return false;
            
        else
            
            return ForAll( [ 1 .. nr_matrices ], n ->
                        ForAll( nr_rows_1, i ->
                            ForAll( nr_cols_1, j ->
                                comparison_function( underlying_category, ListOfMatrices( morphism_1 )[n][i][j], ListOfMatrices( morphism_2 )[n][i][j] ) ) ) );
            
        fi;
        
    end;
    
    #
    AddIsEqualForMorphisms( DAC,
      function( DAC, morphism_1, morphism_2 )
        
        return compare_morphisms( DAC, morphism_1, morphism_2, IsEqualForMorphisms );
        
    end );
    
    #
    AddIsCongruentForMorphisms( DAC,
      function( DAC, morphism_1, morphism_2 )
        
        return compare_morphisms( DAC, morphism_1, morphism_2, IsCongruentForMorphisms );
        
    end );
    
    ##
    AddIdentityMorphism( DAC,
      function( DAC, object )
        local nr_matrices, underlying_objects, multiplicities, list_of_matrices;
        
        nr_matrices := NumberOfObjectsOfUnderlyingCategory( DAC );
        
        underlying_objects := ListOfObjectsOfUnderlyingCategory( DAC );
        
        multiplicities := Multiplicities( object );
        
        list_of_matrices :=
            List( [ 1 .. nr_matrices ], n ->
                List( [ 1 .. multiplicities[n] ], i ->
                    List( [ 1 .. multiplicities[n] ], function( j )
                       if i = j then
                           return IdentityMorphism( UnderlyingCategory( DAC ), underlying_objects[i] );
                       else
                           return ZeroMorphism( UnderlyingCategory( DAC ), underlying_objects[i], underlying_objects[j] );
                        fi;
                    end ) ) );
        
        return MorphismConstructor( DAC, object, list_of_matrices, object );
        
    end );
    
    ##
    AddPreCompose( DAC,
      function( DAC, morphism_1, morphism_2 )
        local nr_matrices, underlying_objects, list_of_matrices1, list_of_matrices2, nr_rows_of_source_matrices, nr_cols_of_source_matrices, nr_cols_of_target_matrices, list_of_matrices_source, list_of_matrices_target, list_of_matrices;
        
        nr_matrices := NumberOfObjectsOfUnderlyingCategory( DAC );
        
        underlying_objects := ListOfObjectsOfUnderlyingCategory( DAC );
        
        list_of_matrices1 := ListOfMatrices( morphism_1 );
        list_of_matrices2 := ListOfMatrices( morphism_2 );
        
        nr_rows_of_source_matrices := Multiplicities( Source( morphism_1 ) );
        nr_cols_of_source_matrices := Multiplicities( Target( morphism_1 ) );
        nr_cols_of_target_matrices := Multiplicities( Target( morphism_2 ) );
        
        list_of_matrices :=
            List( [ 1 .. nr_matrices ], n ->
                List( [ 1 .. nr_rows_of_source_matrices[n] ], i ->
                    List( [ 1 .. nr_cols_of_target_matrices[n] ], j ->
                        SumOfMorphisms( UnderlyingCategory( DAC ),
                                        underlying_objects[i],
                                        List( [ 1 .. nr_cols_of_source_matrices[n] ], k ->
                                            PreCompose( UnderlyingCategory( DAC ), list_of_matrices1[n][i][k], list_of_matrices2[n][k][j] ) ),
                                        underlying_objects[j] ) ) ) );
        
        return MorphismConstructor( DAC, Source( morphism_1 ), list_of_matrices, Target( morphism_2 ) );
        
    end );
    
    AddZeroMorphism( DAC,
      function( DAC, source, target )
        local nr_matrices, underlying_objects, nr_rows_source, nr_cols_target, morphism_matrix;
        
        nr_matrices := NumberOfObjectsOfUnderlyingCategory( DAC );
        
        underlying_objects := ListOfObjectsOfUnderlyingCategory( DAC );
        
        nr_rows_source := Multiplicities( source );
        nr_cols_target := Multiplicities( target );
        
        morphism_matrix :=
            List( [ 1 .. nr_matrices ], n ->
                List( [ 1 .. nr_rows_source[n] ], i ->
                    List( [ 1 .. nr_cols_target[n] ], j ->
                        ZeroMorphism( UnderlyingCategory( DAC ), underlying_objects[i], underlying_objects[j] ) ) ) );
        
        return MorphismConstructor( DAC, source, morphism_matrix, target );
        
    end );
    
    ##
    AddIsZeroForMorphisms( DAC,
      function( DAC, morphism )
        local nr_matrices, nr_rows_source, nr_cols_target;
        
        nr_matrices := NumberOfObjectsOfUnderlyingCategory( DAC );
        
        nr_rows_source := Multiplicities( Source( morphism ) );
        nr_cols_target := Multiplicities( Target( morphism ) );
        
        return ForAll( [ 1 .. nr_matrices ], n ->
                   ForAll( [ 1 .. nr_rows_source[n] ], i ->
                       ForAll( [ 1 .. nr_cols_target[n] ], j ->
                           IsZeroForMorphisms( UnderlyingCategory( DAC ), ListOfMatrices( morphism )[n][i][j] ) ) ) );
        
    end );
    
    ##
    AddAdditionForMorphisms( DAC,
      function( DAC, morphism_1, morphism_2 )
        local nr_matrices, nr_rows_source, nr_cols_target, list_of_matrices;
        
        nr_matrices := NumberOfObjectsOfUnderlyingCategory( DAC );
        
        nr_rows_source := Multiplicities( Source( morphism_1 ) );
        nr_cols_target := Multiplicities( Target( morphism_1 ) );
        
        list_of_matrices :=
            List( [ 1 .. nr_matrices ], n ->
                List( [ 1 .. nr_rows_source[n] ], i ->
                    List( [ 1 .. nr_cols_target[n] ], j ->
                        AdditionForMorphisms( UnderlyingCategory( DAC ),
                            ListOfMatrices( morphism_1 )[n][i][j],
                            ListOfMatrices( morphism_2 )[n][i][j] ) ) ) );
        
        return MorphismConstructor( DAC, Source( morphism_1 ), list_of_matrices, Target( morphism_1 ) );
        
    end );
    
    # ##
    # AddSumOfMorphisms( AC_objfin,
    #   function( AC_objfin, source, morphisms, target )
    #     local length_source_list, length_target_list, source_object_list, target_object_list, morphism_matrix;
    #
    #     length_source_list := NrOfSummands( source );
    #     length_target_list := NrOfSummands( target );
    #
    #     source_object_list := UnderlyingObjectList( AC_objfin, source );
    #     target_object_list := UnderlyingObjectList( AC_objfin, target );
    #
    #     morphism_matrix :=
    #         List( [ 1 .. length_source_list ], i ->
    #             List( [ 1 .. length_target_list ], j ->
    #                 SumOfMorphisms( underlying_category,
    #                                 source_object_list[i],
    #                                 List( morphisms, m -> m[i, j] ),
    #                                 target_object_list[j] ) ) );
    #
    #     return AdditiveClosureMorphism( AC_objfin,
    #                                     source,
    #                                     morphism_matrix,
    #                                     target );
    #
    # end );
    #
    # AddAdditiveInverseForMorphisms( AC_objfin,
    #   function( AC_objfin, morphism )
    #     local morphism_matrix;
    #
    #     morphism_matrix :=
    #         List( [ 1 .. NumberRows( morphism ) ], i ->
    #             List( [ 1 .. NumberColumns( morphism ) ], j ->
    #                 AdditiveInverseForMorphisms( UnderlyingCategory( AC_objfin ), morphism[i, j] ) ) );
    #
    #     return AdditiveClosureMorphism( AC_objfin, Source( morphism ), morphism_matrix, Target( morphism ) );
    #
    # end );
    #
    # AddZeroObject( AC_objfin,
    #   function( AC_objfin )
    #     local zero_list;
    #
    #     zero_list := ListWithIdenticalEntries( NumberOfObjectsOfUnderlyingCategory( AC_objfin ), 0 );
    #
    #     return AdditiveClosureObject( AC_objfin, Pair( 0, zero_list ) );
    #
    # end );
    #
    # ##
    # AddDirectSum( AC_objfin,
    #   function( AC_objfin, diagram )
    #     local sum;
    #
    #     sum := Sum( List( diagram, obj -> NrSummandsAndMultiplicities( obj ) ) );
    #
    #     return AdditiveClosureObject( AC_objfin, sum );
    #
    # end );
    #
    # ##
    # AddUniversalMorphismIntoDirectSumWithGivenDirectSum( AC_objfin,
    #   function( AC_objfin, diagram, test_object, morphisms, direct_sum )
    #     local morphism_matrix;
    #
    #     morphism_matrix := UnionOfColumnsListList( NrOfSummands( test_object ),
    #                                                List( morphisms, tau -> MorphismMatrix( tau ) ) );
    #
    #     return AdditiveClosureMorphism( AC_objfin, test_object, morphism_matrix, direct_sum );
    #
    # end );
    #
    # ##
    # AddUniversalMorphismFromDirectSumWithGivenDirectSum( AC_objfin,
    #   function( AC_objfin, diagram, test_object, morphisms, direct_sum )
    #     local morphism_matrix;
    #
    #     morphism_matrix := UnionOfRowsListList( NrOfSummands( test_object ),
    #                                             List( morphisms, tau -> MorphismMatrix( tau ) ) );
    #
    #     return AdditiveClosureMorphism( AC_objfin, direct_sum, morphism_matrix, test_object );
    #
    # end );
    #
    # ##
    # AddComponentOfMorphismIntoDirectSum( AC_objfin,
    #   function( AC_objfin, morphism, summands, nr )
    #     local lengths, offset, start, stop;
    #
    #     lengths := List( summands, s -> NrOfSummands( s ) );
    #
    #     offset := Sum( lengths{[ 1 .. nr-1 ]} );
    #
    #     start := offset + 1;
    #     stop := offset + lengths[nr];
    #
    #     return AdditiveClosureMorphism( AC_objfin,
    #                                     Source( morphism ),
    #                                     List( MorphismMatrix( morphism ), row -> row{[ start .. stop ]} ), # CertainColumns
    #                                     summands[nr] );
    #
    # end );
    #
    # ##
    # AddComponentOfMorphismFromDirectSum( AC_objfin,
    #   function( AC_objfin, morphism, summands, nr )
    #     local lengths, offset, start, stop;
    #
    #     lengths := List( summands, s -> NrOfSummands( s ) );
    #
    #     offset := Sum( lengths{[ 1 .. nr-1 ]} );
    #
    #     start := offset + 1;
    #     stop := offset + lengths[nr];
    #
    #     return AdditiveClosureMorphism( AC_objfin, summands[nr],
    #                                     MorphismMatrix( morphism ){[ start .. stop ]}, # CertainRows
    #                                     Target( morphism ) );
    #
    # end );
    #
    # if CanCompute( underlying_category, "MultiplyWithElementOfCommutativeRingForMorphisms" ) then
    #
    #   AddMultiplyWithElementOfCommutativeRingForMorphisms( AC_objfin,
    #     function( AC_objfin, r, alpha )
    #       local morphism_matrix;
    #
    #       morphism_matrix :=
    #           List( [ 1 .. NumberRows( alpha ) ], i ->
    #               List( [ 1 .. NumberColumns( alpha ) ], j ->
    #                   MultiplyWithElementOfCommutativeRingForMorphisms( underlying_category, r, alpha[i, j] ) ) );
    #
    #       return AdditiveClosureMorphism( AC_objfin, Source( alpha ), morphism_matrix, Target( alpha ) );
    #
    #   end );
    #
    # fi;
    
    # HandlePrecompiledTowers( DAC, underlying_category, "LinearClosure" );
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        
        Finalize( DAC );
        
    fi;
    
    return DAC;
    
end ) );

####################################
##
## Attributes
##
####################################

InstallMethodForCompilerForCAP( UnderlyingObjectList,
                                [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory ],
                                
  function( obj )
    local underlying_objects, l, multiplicities;
    
    underlying_objects := SetOfObjectsOfCategory( UnderlyingCategory( CapCategory( obj )  ) );
    
    l := NumberOfObjectsOfUnderlyingCategory( CapCategory( obj ) );
    
    multiplicities := Multiplicities( obj );
    
    return Concatenation( List( [ 1 .. l ], i -> ListWithIdenticalEntries( multiplicities[i], underlying_objects[i] ) ) );
    
end );

####################################
##
## Operations
##
####################################

InstallMethodForCompilerForCAP( NrOfSummands,
                                [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory ],
                                
  function( obj )

    return NrSummandsAndMultiplicities( obj )[1];

end );

InstallMethodForCompilerForCAP( Multiplicities,
                                [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory ],
                                
  function( obj )
    
    return NrSummandsAndMultiplicities( obj )[2];
    
end );

####################################
##
## Operators
##
####################################

##
InstallMethodForCompilerForCAP( \[\],
                                [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory, IsInt ],
                                
  function( object, i )
    local obj_list;
    
    obj_list := UnderlyingObjectList( object );
    
    Assert( 0, 1 <= i and i <= Length( obj_list ) );
    
    return obj_list[ i ];
    
end );

##
InstallMethodForCompilerForCAP( \[\],
                                [ IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategory, IsInt ],
                                
  function( morphism, i )
    
    Assert( 0, 1 <= i and i <= NumberOfObjectsOfUnderlyingCategory( CapCategory( morphism ) ) );
    
    return ListOfMatrices( morphism )[i];
    
end );

##
InstallOtherMethod( \/,
                   [ IsList, IsAdditiveClosureOfObjectFiniteDisconnectedCategory ],
                  
  function( list, DAC )
    local underlying_category, multiplicities, nr_summands_and_multiplicities,
          sources_multiplicities, nr_rows, targets_multiplicities, source, target, mor;
    
    underlying_category := UnderlyingCategory( DAC );
    
    if ForAll( list, obj -> IsCapCategoryObject( obj ) and
                            IsIdenticalObj( CapCategory( obj ), underlying_category ) )
    then
        
        # It's a list of objets in the underlying category.
        
        multiplicities := ObjectsToMultiplicityList( underlying_category, list );
        
        nr_summands_and_multiplicities := [ Length( list ), multiplicities ];
        
        return ObjectConstructor( DAC, nr_summands_and_multiplicities );
        
    else
        
        # Assume it's a list of matrices of morphisms in the underlying category.
        # 
        # WARNING: We can only detect 0xn matrices as 0x0 matrices, as they correspond to empty lists '[]'.
        #          For 0xn matrices explicitly use MorphismConstructor.
        
        sources_multiplicities := List( list, matrix -> Length( matrix ) );
        
        nr_rows :=
          function( matrix )
            if IsEmpty( matrix ) then
                return 0;
            fi;
            return Length( matrix[1] );
        end;
        
        targets_multiplicities := List( list, matrix -> nr_rows( matrix ) );
        
        source := ObjectConstructor( DAC, [ Sum( sources_multiplicities ), sources_multiplicities ] );
        
        target := ObjectConstructor( DAC, [ Sum( targets_multiplicities ), targets_multiplicities ] );
        
        return MorphismConstructor( DAC, source, list, target );
        
    fi;
    
end );

##
InstallOtherMethod( \/,
               [ IsCapCategoryObject, IsAdditiveClosureOfObjectFiniteDisconnectedCategory ],
               
  function( obj, DAC )
    local underlying_category, pos, multiplicity_list;
    
    underlying_category := UnderlyingCategory( DAC );
    
    Assert( 0, IsIdenticalObj( underlying_category, CapCategory( obj ) ) );
    
    multiplicity_list := ObjectToMultiplicityList( underlying_category, obj );
    
    return ObjectConstructor( DAC, [ 1, multiplicity_list ] );
    
end );

##
InstallOtherMethod( \/,
               [ IsCapCategoryMorphism, IsAdditiveClosureOfObjectFiniteDisconnectedCategory ],
               
  function( alpha, DAC )
    local underlying_category, source, object, list_of_matrices;
    
    underlying_category := UnderlyingCategory( DAC );
    
    Assert( 0, IsIdenticalObj( underlying_category, CapCategory( alpha ) ) );
    
    source := Source( alpha );
    
    if not IsIdenticalObj( source, Target( alpha ) ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "the source and target of <alpha> have to be equal\n" );
        
    fi;
    
    object := ObjectConstructor( DAC, [ 1, ObjectToMultiplicityList( underlying_category, source ) ] );
    
    # All matrices are empty except for the one corresponding to <alpha>.
    list_of_matrices := ListWithIdenticalEntries( NumberOfObjectsOfUnderlyingCategory( DAC ), [ ] );
    
    list_of_matrices[ Position( SetOfObjectsOfCategory( underlying_category ), source ) ] := [ [ alpha ] ];
    
    return MorphismConstructor( DAC, object, list_of_matrices, object );
    
end );

####################################
##
## Global functions
##
####################################

InstallGlobalFunction( COMPILATION_HELPER_AdditiveClosureOfObjectFiniteDisconnectedCategory_BlockDiagonalMatrix,
  function( DAC, nr_objects, source_mults, target_mults, list_of_matrices )
    local underlying_category, objects, list_of_extended_matrices, morphism_matrix;
    
    underlying_category := UnderlyingCategory( DAC );
    
    objects := SetOfObjectsOfCategory( underlying_category );
    
    # Extend the rows of the matrices with zero morphisms.
    # Note: number of matrices = number of objects,
    #       source_mults = number of rows for each matrix,
    #       target_mults = number of columns for each matrix.
    list_of_extended_matrices :=
        List( [ 1 .. nr_objects ], m_i ->
            List( list_of_matrices[ m_i ], row ->
                Concatenation(
                    Concatenation( List( [ 1 .. m_i-1 ], i ->
                        ListWithIdenticalEntries( target_mults[i],
                                                  ZeroMorphism( underlying_category, objects[m_i], objects[i] ) ) ) ),
                    row,
                    Concatenation( List( [ m_i+1 .. nr_objects ], i ->
                        ListWithIdenticalEntries( target_mults[i],
                                                  ZeroMorphism( underlying_category, objects[m_i], objects[i] ) ) ) ) ) ) );
    
    # All rows of all matrices now have the same number of colums
    # so we can stack all matrices to get our final matrix.
    morphism_matrix := Concatenation( list_of_extended_matrices );
    
    return morphism_matrix;
    
end );

InstallGlobalFunction( COMPILATION_HELPER_AdditiveClosureOfObjectFiniteDisconnectedCategory_ExtractBlocksOfBlockDiagonalMatrix,
  function( DAC, phi )
    local AC_objfin, underlying_category, nr_objects, morphism_matrix, source, target, source_mults, target_mults, row_indices, col_indices, list_of_matrices;
    
    AC_objfin := ModelingCategory( DAC );
    
    underlying_category := UnderlyingCategory( DAC );
    
    nr_objects := NumberOfObjectsOfUnderlyingCategory( DAC );
    
    morphism_matrix := MorphismMatrix( phi );
    
    source := Source( phi );
    target := Target( phi );
    
    source_mults := Multiplicities( source );
    target_mults := Multiplicities( target );
    
    row_indices := List( [ 0 .. Length( source_mults ) ], i -> Sum( source_mults{ [ 1 .. i ] } ) );
    col_indices := List( [ 0 .. Length( target_mults ) ], i -> Sum( target_mults{ [ 1 .. i ] } ) );
    
    # Extract the block matrices on the diagonal.
    list_of_matrices :=
        List( [ 1 .. nr_objects ], obj_idx ->
            List( [ row_indices[obj_idx] + 1 .. row_indices[obj_idx + 1] ], nr_rows ->
                morphism_matrix[nr_rows]{ [ col_indices[obj_idx] + 1 .. col_indices[obj_idx + 1] ] } ) );
    
    return list_of_matrices;
    
end );

####################################
##
## View & Display
##
####################################

##
InstallMethod( ViewString,
               [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory ],
               
  function( object )
    local nr;
    
    nr := NrOfSummands( object );
    
    if nr = 1 then
        
        return Concatenation(
                    "<An object in ", Name( CapCategory( object ) ),
                    " defined by ", String( nr ), " underlying object>" );
        
    else
        
        return Concatenation(
                    "<An object in ", Name( CapCategory( object ) ),
                    " defined by ", String( nr ), " underlying objects>" );
        
    fi;
    
end );

##
InstallMethod( ViewString,
               [ IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategory ],
               
  function( morphism )
    local string, number_matrices;
    
    number_matrices := Length( ListOfMatrices( morphism ) );
    string := Concatenation( "<A morphism in ", Name( CapCategory( morphism ) ),
                             " defined by a list of ",
                             String( number_matrices ) );
    
    if number_matrices = 1 then
        
        string := Concatenation( string, " matrix of underlying morphisms>" );
        
    else
        
        string := Concatenation( string, " matrices of underlying morphisms>" );
        
    fi;
    
    return string;
end );

##
InstallMethod( DisplayString,
               [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory ],
               
  function( object )
    local DAC, A, objects_of_underlying_category, nr_objects_of_underlying_category,
          nr_objects, multiplicities, string, obj;
    
    DAC := CapCategory( object );
    A := UnderlyingCategory( DAC );
    
    objects_of_underlying_category := SetOfObjectsOfCategory( A );
    nr_objects_of_underlying_category := NumberOfObjectsOfUnderlyingCategory( DAC );
    nr_objects := NrOfSummands( object );
    multiplicities := Multiplicities( object );
    
    if nr_objects = 1 then
      
      string := Concatenation( "A formal direct sum consisting of ", String( nr_objects ), " object:\n\n" );
      
    else
      
      string := Concatenation( "A formal direct sum consisting of ", String( nr_objects ), " objects:\n\n" );
      
    fi;
    
    for obj in [ 1 .. nr_objects_of_underlying_category  ] do
        
        string := Concatenation( string, String( multiplicities[ obj ] ), " times: " );
        
        string := Concatenation( string, ViewString( objects_of_underlying_category[ obj ] ), "\n" );
        
    od;
    
    return string;
    
end );

##
InstallMethod( DisplayString,
               [ IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategory ],
               
  function( morphism )
    local i, matrix, target, nr_rows, nr_cols, string, j, k;
    
    string := "";
    
    for i in [ 1 .. Length( ListOfMatrices( morphism ) ) ] do
        
        matrix := morphism[i];
        
        # 0xn matrix?
        if Length( matrix ) = 0 then
            
            target := Target( morphism );
            
            nr_cols := Multiplicities( ModelingObject( CapCategory( target ), target ) )[i];
            
            string := Concatenation( string,
                                     "A ", String( 0 ), " x ", String( nr_cols ),
                                     " matrix with entries in ",
                                     Name( UnderlyingCategory( CapCategory( morphism ) ) ), "\n\n" );
            
            continue;
            
        fi;
        
        nr_rows := Length( matrix );

        # nx0 matrix?
        if Length( matrix[1] ) = 0 then
            
            string := Concatenation( string,
                                     "A ", String( nr_rows ), " x ", String( 0 ),
                                     " matrix with entries in ",
                                     Name( UnderlyingCategory( CapCategory( morphism ) ) ), "\n\n" );
            
            continue;
            
        fi;
        
        nr_cols := Length( matrix[1] );
        
        string := Concatenation( string,
                                 "A ", String( nr_rows ), " x ", String( nr_cols ),
                                 " matrix with entries in ",
                                 Name( UnderlyingCategory( CapCategory( morphism ) ) ), "\n" );
        
        # Not a zero matrix so we can display its values.
        for j in [ 1 .. nr_rows ] do
            
            for k in [ 1 .. nr_cols ] do
                
                string := Concatenation( string, Concatenation( "\n[", String(j), ",", String(k), "]: " ) );
                
                string := Concatenation( string, ViewString( matrix[j,k] ) );
                
            od;
            
        od;
        
        string := Concatenation( string, "\n\n" );
        
    od;
    
    return string;
    
end );

