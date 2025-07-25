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
               [ IsCategoryOfRows, IsInt ],
               
  FunctionWithNamedArguments(
  [
    [ "FinalizeCategory", true ],
  ],
  function( CAP_NAMED_ARGUMENTS, Rows, nr_summands )
    local homalg_ring, D, L, AC_disc, object_datum_type, object_datum, object_constructor, morphism_datum, morphism_datum_type, morphism_constructor, modeling_tower_object_constructor, modeling_tower_object_datum, modeling_tower_morphism_constructor, modeling_tower_morphism_datum, SubscriptDigits, ToSubscript, name, Coproduct;
    
    Assert( 0, nr_summands > 0 );
    
    if nr_summands = 1 then
        
        return Rows;
        
    fi;
    
    homalg_ring := UnderlyingRing( Rows );
    
    D := FiniteSkeletalDiscreteCategory( nr_summands : FinalizeCategory := true );
    
    L := LinearClosure( homalg_ring, D : FinalizeCategory := true );
    
    AC_disc := AdditiveClosureOfObjectFiniteDisconnectedCategory( L : FinalizeCategory := false );
    
    Finalize( AC_disc );
    
    ####################################
    # Reinterpretation
    ####################################
    
    ##
    object_datum_type :=
        CapJitDataTypeOfListOf(
            CapJitDataTypeOfObjectOfCategory( Rows ) );
    
    ##
    object_datum := { coproduct, obj } -> ListOfObjects( obj );
    
    ##
    object_constructor :=
      function( coproduct, list_of_row_objects )
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( list_of_row_objects ) = NrOfSummandsOfCoproduct( coproduct ) );
        
        return CreateCapCategoryObjectWithAttributes( coproduct,
                       ListOfObjects, list_of_row_objects );
        
    end;
    
    ##
    morphism_datum_type := CapJitDataTypeOfListOf( CapJitDataTypeOfMorphismOfCategory( Rows ) );
    
    ##
    morphism_datum := { coproduct, phi } -> ListOfMorphisms( phi );
    
    ##
    morphism_constructor :=
      function( coproduct, S, list_of_row_morphisms, T )
        local nr_summands, morphism, i;
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        for i in [ 1 .. NrOfSummandsOfCoproduct( coproduct ) ] do
            
            morphism := list_of_row_morphisms[i];
            
            Assert( 0, RankOfObject( Source( morphism ) ) = RankOfObject( ListOfObjects( S )[i] ) );
            Assert( 0, RankOfObject( Target( morphism ) ) = RankOfObject( ListOfObjects( T )[i] ) );
            
        od;
        
        return CreateCapCategoryMorphismWithAttributes( coproduct,
                                                        S,
                                                        T,
                                                        ListOfMorphisms, list_of_row_morphisms );
        
    end;
    
    ####################################
    # Modeling
    ####################################
    
    ## From the raw object data to the object in the modeling category.
    modeling_tower_object_constructor :=
      function( coproduct, list_of_row_objects )
        local AC_disc, list_of_ranks;
        
        # Checks are done in the modeling category.
        AC_disc := ModelingCategory( coproduct );
        
        list_of_ranks := List( list_of_row_objects, obj -> RankOfObject( obj ) );
        
        return ObjectConstructor( AC_disc, [ Sum( list_of_ranks ), list_of_ranks ] );
        
    end;
    
    ## From the object in the modeling category to the raw object data.
    modeling_tower_object_datum :=
      function( coproduct, object )
        local Rows, multiplicities, list_of_row_objects;
        
        Rows := UnderlyingCategoryOfRows( coproduct );
        
        multiplicities := Multiplicities( object );
        
        list_of_row_objects := List( multiplicities, mult -> ObjectConstructor( Rows, mult ) );
        
        return list_of_row_objects;
        
    end;
    
    ## From the raw morphism data to the morphism in the modeling category.
    modeling_tower_morphism_constructor :=
      function( coproduct, S, list_of_row_morphisms, T )
        local nr_summands, morphism, AC_disc, L, D, underlying_disconnected_objects, list_of_matrices, list_of_matrices_linear_closure, i, matrix, row, obj_D, obj_L, id_obj_D;
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        Assert( 0, Length( list_of_row_morphisms ) = NrOfSummandsOfCoproduct( coproduct ) );
        
        #% CAP_JIT_DROP_NEXT_STATEMENT
        for i in [ 1 .. NrOfSummandsOfCoproduct( coproduct ) ] do
            
            morphism := list_of_row_morphisms[i];
            
            Assert( 0, RankOfObject( Source( morphism ) ) = Multiplicities( S )[i] );
            Assert( 0, RankOfObject( Target( morphism ) ) = Multiplicities( T )[i] );
            
        od;
        
        AC_disc := ModelingCategory( coproduct );
        
        L := UnderlyingCategory( AC_disc );
        
        D := UnderlyingCategory( L );
        
        underlying_disconnected_objects := SetOfObjectsOfCategory( D );
        
        list_of_matrices :=
            List( list_of_row_morphisms, morphism ->
                EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( morphism ) ) );
        
        # For all matrices turn the matrix entries 'c' into coefficients: c·IdentityMorphism.
        list_of_matrices_linear_closure :=
            List( [ 1 .. NrOfSummandsOfCoproduct( coproduct ) ], i ->
                List( list_of_matrices[i], row ->
                    List( row,
                        function( c )
                            obj_D := underlying_disconnected_objects[i];
                            
                            id_obj_D := IdentityMorphism( D, obj_D );
                            
                            obj_L := LinearClosureObject( L, obj_D );
                            
                            return MorphismConstructor( L, obj_L, c, obj_L );
                            
        end ) ) );
        
        # Check that all matrices have the correct dimensions.
        #% CAP_JIT_DROP_NEXT_STATEMENT
        for i in [ 1 .. NrOfSummandsOfCoproduct( coproduct ) ] do
            
            matrix :=  list_of_matrices_linear_closure[i];
            
            Assert( 0, Length( matrix ) = Multiplicities( S )[i] );
            
            for row in matrix do
                
                Assert( 0, Length( row ) = Multiplicities( T )[i] );
                
            od;
            
        od;
        
        return MorphismConstructor( AC_disc, S, list_of_matrices_linear_closure, T );
        
    end;
    
    # From the morphism in the modeling category to the raw morphism data.
    modeling_tower_morphism_datum :=
      function ( coproduct, morphism )
        local list_of_matrices, source_multiplicities, target_multiplicities, Rows, underlying_ring, list_of_row_morphisms;
        
        list_of_matrices := ListOfMatrices( morphism );
        
        source_multiplicities := Multiplicities( Source( morphism ) );
        target_multiplicities := Multiplicities( Target( morphism ) );
        
        Rows := UnderlyingCategoryOfRows( coproduct );
        
        underlying_ring := UnderlyingRing( coproduct );
        
        list_of_row_morphisms :=
            List( [ 1 .. Length( list_of_matrices ) ],
                function( i )
                    local matrix, nr_rows, nr_cols, homalg_matrix;
                    
                    matrix := list_of_matrices[i];
                    
                    # All entries are of the form: c·IdentityMorphism, so we extract the coefficients 'c'.
                    matrix :=
                        List( matrix,
                            row -> List( row, entry -> Coefficient( entry ) ) );
                    
                    nr_rows := source_multiplicities[i];
                    nr_cols := target_multiplicities[i];
                    
                    homalg_matrix := HomalgMatrixListList( matrix,
                                                           nr_rows,
                                                           nr_cols,
                                                           underlying_ring );
                    
                    return CategoryOfRowsMorphism( CategoryOfRowsObject( Rows, nr_rows ),
                                                   homalg_matrix,
                                                   CategoryOfRowsObject( Rows, nr_cols ) );
                    
                end );
                
        return list_of_row_morphisms;
        
    end;
    
    name := Concatenation( "⊕ ( ", "CategoryOfRows( ", RingName( homalg_ring ), " ), ", String( nr_summands ), " )" );
    
    Coproduct :=
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
            local Rows, kernels;
            
            Rows := UnderlyingCategoryOfRows( Coproduct );
            
            kernels := List( ListOfMorphisms( morphism ), morphism -> KernelObject( Rows, morphism ) );
            
            return ObjectConstructor( Coproduct, kernels );
            
        end );
        
        ##
        AddKernelEmbedding( Coproduct,
          function( Coproduct, morphism )
            local Rows, kernel_embeddings, kernels, kernel_object;
            
            Rows := UnderlyingCategoryOfRows( Coproduct );
            
            kernel_embeddings := List( ListOfMorphisms( morphism ), morphism -> KernelEmbedding( Rows, morphism ) );
            
            kernels := List( kernel_embeddings, embedding -> Source( embedding ) );
            
            kernel_object := ObjectConstructor( Coproduct, kernels );
            
            return MorphismConstructor( Coproduct, kernel_object, kernel_embeddings, Source( morphism ) );
            
        end );
        
        ##
        AddKernelEmbeddingWithGivenKernelObject( Coproduct,
          function( Coproduct, morphism, kernel_object )
            local Rows, kernel_embeddings;
            
            Rows := UnderlyingCategoryOfRows( Coproduct );
            
            kernel_embeddings := List( ListOfMorphisms( morphism ), morphism -> KernelEmbedding( Rows, morphism ) );
            
            return MorphismConstructor( Coproduct, kernel_object, kernel_embeddings, Source( morphism ) );
            
        end );
        
        ##
        AddLift( Coproduct,
          function( Coproduct, alpha, beta )
            local morphisms_alpha, morphisms_beta, lifts;
            
            morphisms_alpha := ListOfMorphisms( alpha );
            
            morphisms_beta := ListOfMorphisms( beta );
            
            lifts := List( [ 1 .. Length( morphisms_alpha ) ], i -> Lift( morphisms_alpha[i], morphisms_beta[i] ) );
            
            return MorphismConstructor( Coproduct, Source( alpha ), lifts, Source( beta ) );
            
        end );
        
        ##
        AddCokernelObject( Coproduct,
          function( Coproduct, morphism )
            local Rows, cokernels;
            
            Rows := UnderlyingCategoryOfRows( Coproduct );
            
            cokernels := List( ListOfMorphisms( morphism ), morphism -> CokernelObject( Rows, morphism ) );
            
            return ObjectConstructor( Coproduct, cokernels );
            
        end );
        
        ##
        AddCokernelProjection( Coproduct,
          function( Coproduct, morphism )
            local Rows, cokernel_projections, cokernels, cokernel_object;
            
            Rows := UnderlyingCategoryOfRows( Coproduct );
            
            cokernel_projections := List( ListOfMorphisms( morphism ), morphism -> CokernelProjection( Rows, morphism ) );
            
            cokernels := List( cokernel_projections, projection -> Target( projection ) );
            
            cokernel_object := ObjectConstructor( Coproduct, cokernels );
            
            return MorphismConstructor( Coproduct, Target( morphism ), cokernel_projections, cokernel_object );
            
        end );

        ##
        AddCokernelProjectionWithGivenCokernelObject( Coproduct,
          function( Coproduct, morphism, cokernel_object )
            local Rows, cokernel_projections;
            
            Rows := UnderlyingCategoryOfRows( Coproduct );
            
            cokernel_projections := List( ListOfMorphisms( morphism ), morphism -> CokernelProjection( Rows, morphism ) );
            
            return MorphismConstructor( Coproduct, Target( morphism ), cokernel_projections, cokernel_object );
            
        end );

        ##
        AddColift( Coproduct,
          function( Coproduct, alpha, beta )
            local morphisms_alpha, morphisms_beta, colifts;
            
            morphisms_alpha := ListOfMorphisms( alpha );
            
            morphisms_beta := ListOfMorphisms( beta );
            
            colifts := List( [ 1 .. Length( morphisms_alpha ) ], i -> Colift( morphisms_alpha[i], morphisms_beta[i] ) );
            
            return MorphismConstructor( Coproduct, Target( alpha ), colifts, Target( beta ) );
            
        end );
    
    fi;
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        
        Finalize( Coproduct );
        
    fi;
    
    return Coproduct;
    
end ) );

####################################
##
## Operations
##
####################################

##
InstallMethodForCompilerForCAP( \[\],
                                [ IsObjectInCoproductOfCategoryOfRows, IsInt ],
                                
  function( object, i )
    
    if i < 1 or i > NrOfSummandsOfCoproduct( CapCategory( object ) ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "out of bounds\n" );
        
    fi;
    
    return ListOfObjects( object )[i];
    
end );

##
InstallMethodForCompilerForCAP( \[\],
                                [ IsMorphismInCoproductOfCategoryOfRows, IsInt ],
                                
  function( morphism, i )
    
    if i < 1 or i > NrOfSummandsOfCoproduct( CapCategory( morphism ) ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "out of bounds\n" );
        
    fi;
    
    return ListOfMorphisms( morphism )[i];
    
end );

InstallOtherMethod( \/,
                   [ IsList, IsCoproductOfCategoryOfRows ],
                  
  function( list, coproduct )
    local Rows, list_of_row_objects, source_list, target_list, list_of_row_morphisms, source, target;
    
    Rows := UnderlyingCategoryOfRows( coproduct );
    
    if ForAll( list, obj -> IsInt( obj ) ) then
        
        list_of_row_objects := List( list, rank -> CategoryOfRowsObject( Rows, rank ) );
        
        return ObjectConstructor( coproduct, list_of_row_objects );
        
    elif ForAll( list, obj -> IsHomalgMatrix( obj ) ) then
        
        source_list := List( list, matrix -> CategoryOfRowsObject( Rows, NrRows( matrix ) ) );
        target_list := List( list, matrix -> CategoryOfRowsObject( Rows, NrCols( matrix ) ) );
        
        list_of_row_morphisms := List( list, matrix -> AsCategoryOfRowsMorphism( Rows, matrix ) );
        
        source := ObjectConstructor( coproduct, source_list );
        target := ObjectConstructor( coproduct, target_list );
        
        return MorphismConstructor( coproduct, source, list_of_row_morphisms, target );
        
    else
        
        Error( "<list> has to be a list of integers or a list of Homalg matrices\n" );
        
    fi;
    
end );

InstallMethodForCompilerForCAP( Ranks,
                                [ IsObjectInCoproductOfCategoryOfRows ],
                                
  function( object )
    
    return List( ListOfObjects( object ), row_obj -> RankOfObject( row_obj ) );
    
end );

####################################
##
## View & Display
##
####################################

InstallMethod( DisplayString,
               [ IsObjectInCoproductOfCategoryOfRows ],
               
  object -> String( Ranks( object ) )
  
);

