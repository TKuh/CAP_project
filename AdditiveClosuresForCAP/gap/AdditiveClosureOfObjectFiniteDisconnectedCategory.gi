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
    [ "UsePrecompiledUnderlyingAdditiveClosure", false ],
    [ "PrecompiledUnderlyingAdditiveClosure", fail ],
  ],
  function( CAP_NAMED_ARGUMENTS, underlying_category )
    local object_datum_type, object_constructor, object_datum, morphism_datum_type, morphism_constructor, morphism_datum, AC_objfin, modeling_tower_object_constructor, modeling_tower_object_datum, modeling_tower_morphism_constructor, modeling_tower_morphism_datum, DAC;
    
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
    object_datum := { DAC, obj } -> NrSummandsAndMultiplicities( obj );
    
    ##
    object_constructor :=
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
        
    end;
    
    ##
    morphism_datum_type :=
        CapJitDataTypeOfListOf(
            CapJitDataTypeOfListOf(
                CapJitDataTypeOfListOf(
                    CapJitDataTypeOfMorphismOfCategory( underlying_category ) ) ) );
   
    ##
    morphism_datum := { DAC, phi } -> ListOfMatrices( phi );
    
    ##
    morphism_constructor :=
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
        
    end;
    
    ####################################
    # Reinterpretation
    ####################################
    
    if CAP_NAMED_ARGUMENTS.UsePrecompiledUnderlyingAdditiveClosure then
        
        AC_objfin := CAP_NAMED_ARGUMENTS.PrecompiledUnderlyingAdditiveClosure;
        
        # AC_objfin := ADDITIVE_CLOSURE_OF_LINEAR_CLOSURE_OF_FINITE_SKELETAL_DISCRETE_CATEGORY( underlying_category : FinalizeCategory := true );
        
    else
        
        AC_objfin := AdditiveClosureOfObjectFiniteCategory( underlying_category : FinalizeCategory := true );
        
    fi;
    
    ## From the raw object data to the object in the modeling category.
    modeling_tower_object_constructor :=
      function( DAC, nr_summands_and_multiplicities )
        
        return ObjectConstructor( ModelingCategory( DAC ), nr_summands_and_multiplicities );
        
    end;
    
    ## From the object in the modeling category to the raw object data.
    modeling_tower_object_datum :=
      function( DAC, objAC )
        
        return NrSummandsAndMultiplicities( objAC );
        
    end;
    
    ## From the raw morphism data to the morphism in the modeling category.
    modeling_tower_morphism_constructor :=
      function( DAC, source, list_of_matrices, target )
        local AC_objfin, underlying_category, objects, nr_objects, source_mults, target_mults, list_of_extended_matrices, morphism_matrix;
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( list_of_matrices ) = NumberOfObjectsOfUnderlyingCategory( DAC ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, ForAllWithKeys( list_of_matrices, { key, matrix } ->
            Length( matrix ) = Multiplicities( source )[key] and
            ForAll( matrix, row -> Length( row ) = Multiplicities( target )[key] ) ) );
        
        AC_objfin := ModelingCategory( DAC );
        
        nr_objects := NumberOfObjectsOfUnderlyingCategory( DAC );
        
        source_mults := Multiplicities( source );
        target_mults := Multiplicities( target );
        
        morphism_matrix :=
            COMPILATION_HELPER_AdditiveClosureOfObjectFiniteDisconnectedCategory_BlockDiagonalMatrix(
                DAC,
                nr_objects,
                source_mults,
                target_mults,
                list_of_matrices );
        
        return MorphismConstructor( AC_objfin, source, morphism_matrix, target );
        
    end;
    
    ## From the morphism in the modeling category to the raw morphism data.
    modeling_tower_morphism_datum :=
      function( DAC, phi )
        local list_of_matrices;
        
        list_of_matrices := COMPILATION_HELPER_AdditiveClosureOfObjectFiniteDisconnectedCategory_ExtractBlocksOfBlockDiagonalMatrix( DAC, phi );
        
        return list_of_matrices;
        
    end;
    
    ##
    DAC :=
        ReinterpretationOfCategory( AC_objfin,
            rec( name := Concatenation( "AdditiveClosureOfObjectFiniteDisconnectedCategory( ", Name( underlying_category ), " )" ),
                 category_filter := IsAdditiveClosureOfObjectFiniteDisconnectedCategory,
                 category_object_filter := IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory,
                 category_morphism_filter := IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategory,
                 object_datum_type := object_datum_type,
                 morphism_datum_type := morphism_datum_type,
                 object_constructor := object_constructor,
                 object_datum := object_datum,
                 morphism_constructor := morphism_constructor,
                 morphism_datum := morphism_datum,
                 modeling_tower_object_constructor := modeling_tower_object_constructor,
                 modeling_tower_object_datum := modeling_tower_object_datum,
                 modeling_tower_morphism_constructor := modeling_tower_morphism_constructor,
                 modeling_tower_morphism_datum := modeling_tower_morphism_datum,
                 only_primitive_operations := true )
            : FinalizeCategory := false );
    
    if HasIsSkeletalCategory( underlying_category ) and IsSkeletalCategory( underlying_category ) then
        
        SetIsSkeletalCategory( DAC, true );
        
    fi;
    
    Append( DAC!.compiler_hints.category_attribute_names,
            [ "UnderlyingCategory",
              "NumberOfObjectsOfUnderlyingCategory" ] );
    
    SetUnderlyingCategory( DAC, underlying_category );
    
    SetNumberOfObjectsOfUnderlyingCategory( DAC, Length( SetOfObjectsOfCategory( underlying_category ) ) );
    
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

