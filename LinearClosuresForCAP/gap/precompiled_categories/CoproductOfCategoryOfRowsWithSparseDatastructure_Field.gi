# SPDX-License-Identifier: GPL-2.0-or-later
# LinearClosuresForCAP: Linear closures
#
# Implementations
#
BindGlobal( "ADD_FUNCTIONS_FOR_CoproductOfCategoryOfRowsWithSparseDatastructure_Field", function ( cat )
    
    ##
    AddIsEqualForObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_5_1, deduped_6_1, deduped_7_1;
    deduped_7_1 := ListOfPairsOfObjectAndIndex( arg3_1 );
    deduped_6_1 := ListOfPairsOfObjectAndIndex( arg2_1 );
    deduped_5_1 := Length( deduped_6_1 );
    return deduped_5_1 = Length( deduped_7_1 ) and ForAll( [ 1 .. deduped_5_1 ], function ( i_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := deduped_7_1[i_2];
              deduped_1_2 := deduped_6_1[i_2];
              return (deduped_1_2[2] = deduped_2_2[2] and RankOfObject( deduped_1_2[1] ) = RankOfObject( deduped_2_2[1] ));
          end );
end
########
        
    , 100 );
    
    ##
    AddIsEqualForMorphisms( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_5_1, deduped_6_1, deduped_7_1;
    deduped_7_1 := ListOfPairsOfMorphismAndIndex( arg3_1 );
    deduped_6_1 := ListOfPairsOfMorphismAndIndex( arg2_1 );
    deduped_5_1 := Length( deduped_6_1 );
    if deduped_5_1 <> Length( deduped_7_1 ) then
        return false;
    else
        return ForAll( [ 1 .. deduped_5_1 ], function ( i_2 )
                local deduped_1_2, deduped_2_2;
                deduped_2_2 := deduped_7_1[i_2];
                deduped_1_2 := deduped_6_1[i_2];
                return deduped_1_2[2] = deduped_2_2[2] and UnderlyingMatrix( deduped_1_2[1] ) = UnderlyingMatrix( deduped_2_2[1] );
            end );
    fi;
    return;
end
########
        
    , 100 );
    
    ##
    AddIsCongruentForMorphisms( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_5_1, deduped_6_1, deduped_7_1;
    deduped_7_1 := ListOfPairsOfMorphismAndIndex( arg3_1 );
    deduped_6_1 := ListOfPairsOfMorphismAndIndex( arg2_1 );
    deduped_5_1 := Length( deduped_6_1 );
    if deduped_5_1 <> Length( deduped_7_1 ) then
        return false;
    else
        return ForAll( [ 1 .. deduped_5_1 ], function ( i_2 )
                local deduped_1_2, deduped_2_2;
                deduped_2_2 := deduped_7_1[i_2];
                deduped_1_2 := deduped_6_1[i_2];
                return deduped_1_2[2] = deduped_2_2[2] and UnderlyingMatrix( deduped_1_2[1] ) = UnderlyingMatrix( deduped_2_2[1] );
            end );
    fi;
    return;
end
########
        
    , 100 );
    
    ##
    AddObjectConstructor( cat,
        
########
function ( cat_1, arg2_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, ListOfPairsOfObjectAndIndex, arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddMorphismConstructor( cat,
        
########
function ( cat_1, arg2_1, arg3_1, arg4_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, arg2_1, arg4_1, ListOfPairsOfMorphismAndIndex, arg3_1 );
end
########
        
    , 100 );
    
    ##
    AddObjectDatum( cat,
        
########
function ( cat_1, arg2_1 )
    return ListOfPairsOfObjectAndIndex( arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddMorphismDatum( cat,
        
########
function ( cat_1, arg2_1 )
    return ListOfPairsOfMorphismAndIndex( arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddIdentityMorphism( cat,
        
########
function ( cat_1, a_1 )
    local hoisted_2_1, hoisted_3_1, deduped_4_1;
    deduped_4_1 := ListOfPairsOfObjectAndIndex( a_1 );
    hoisted_3_1 := UnderlyingCategoryOfRows( cat_1 );
    hoisted_2_1 := UnderlyingRing( cat_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, a_1, a_1, ListOfPairsOfMorphismAndIndex, List( [ 1 .. Length( deduped_4_1 ) ], function ( n_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := deduped_4_1[n_2];
              deduped_1_2 := deduped_2_2[1];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( hoisted_3_1, deduped_1_2, deduped_1_2, UnderlyingMatrix, HomalgIdentityMatrix( RankOfObject( deduped_1_2 ), hoisted_2_1 ) ), deduped_2_2[2] );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddPreCompose( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    local deduped_4_1, deduped_5_1;
    deduped_5_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_4_1 := CreateCapCategoryObjectWithAttributes( deduped_5_1, RankOfObject, 0 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, Source( alpha_1 ), Target( beta_1 ), ListOfPairsOfMorphismAndIndex, List( COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZeroMorphism( deduped_5_1, ListOfPairsOfMorphismAndIndex( alpha_1 ), ListOfPairsOfMorphismAndIndex( beta_1 ), CreateCapCategoryMorphismWithAttributes( deduped_5_1, deduped_4_1, deduped_4_1, UnderlyingMatrix, HomalgZeroMatrix( 0, 0, UnderlyingRing( cat_1 ) ) ) ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := pair_2[1];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_5_1, Source( deduped_1_2 ), Range( deduped_2_2 ), UnderlyingMatrix, UnderlyingMatrix( deduped_1_2 ) * UnderlyingMatrix( deduped_2_2 ) ), pair_2[3] );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddZeroMorphism( cat,
        
########
function ( cat_1, a_1, b_1 )
    local hoisted_1_1, deduped_3_1;
    deduped_3_1 := UnderlyingCategoryOfRows( cat_1 );
    hoisted_1_1 := UnderlyingRing( cat_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, a_1, b_1, ListOfPairsOfMorphismAndIndex, List( COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZeroObject( deduped_3_1, ListOfPairsOfObjectAndIndex( a_1 ), ListOfPairsOfObjectAndIndex( b_1 ), CreateCapCategoryObjectWithAttributes( deduped_3_1, RankOfObject, 0 ) ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := pair_2[1];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_3_1, deduped_1_2, deduped_2_2, UnderlyingMatrix, HomalgZeroMatrix( RankOfObject( deduped_1_2 ), RankOfObject( deduped_2_2 ), hoisted_1_1 ) ), pair_2[3] );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddIsZeroForMorphisms( cat,
        
########
function ( cat_1, arg2_1 )
    return ForAll( ListOfPairsOfMorphismAndIndex( arg2_1 ), function ( pair_2 )
            return IsZero( UnderlyingMatrix( pair_2[1] ) );
        end );
end
########
        
    , 100 );
    
    ##
    AddAdditionForMorphisms( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    local hoisted_4_1, hoisted_5_1, deduped_6_1;
    deduped_6_1 := ListOfPairsOfMorphismAndIndex( alpha_1 );
    hoisted_5_1 := UnderlyingCategoryOfRows( cat_1 );
    hoisted_4_1 := ListOfPairsOfMorphismAndIndex( beta_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, Source( alpha_1 ), Target( alpha_1 ), ListOfPairsOfMorphismAndIndex, List( [ 1 .. Length( deduped_6_1 ) ], function ( n_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := deduped_6_1[n_2];
              deduped_1_2 := deduped_2_2[1];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( hoisted_5_1, Source( deduped_1_2 ), Range( deduped_1_2 ), UnderlyingMatrix, UnderlyingMatrix( deduped_1_2 ) + UnderlyingMatrix( hoisted_4_1[n_2][1] ) ), deduped_2_2[2] );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddSumOfMorphisms( cat,
        
########
function ( cat_1, source_1, list_of_morphisms_1, range_1 )
    local hoisted_2_1, deduped_4_1, deduped_5_1;
    deduped_5_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_4_1 := COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZeroObject( deduped_5_1, ListOfPairsOfObjectAndIndex( source_1 ), ListOfPairsOfObjectAndIndex( range_1 ), CreateCapCategoryObjectWithAttributes( deduped_5_1, RankOfObject, 0 ) );
    hoisted_2_1 := UnderlyingRing( cat_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, source_1, range_1, ListOfPairsOfMorphismAndIndex, List( [ 1 .. Length( deduped_4_1 ) ], function ( n_2 )
              local deduped_1_2, deduped_2_2, deduped_3_2;
              deduped_3_2 := deduped_4_1[n_2];
              deduped_2_2 := deduped_3_2[2];
              deduped_1_2 := deduped_3_2[1];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_5_1, deduped_1_2, deduped_2_2, UnderlyingMatrix, Sum( List( list_of_morphisms_1, function ( logic_new_func_x_3 )
                            return UnderlyingMatrix( ListOfPairsOfMorphismAndIndex( logic_new_func_x_3 )[n_2][1] );
                        end ), HomalgZeroMatrix( RankOfObject( deduped_1_2 ), RankOfObject( deduped_2_2 ), hoisted_2_1 ) ) ), deduped_3_2[3] );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddAdditiveInverseForMorphisms( cat,
        
########
function ( cat_1, alpha_1 )
    local hoisted_1_1;
    hoisted_1_1 := UnderlyingCategoryOfRows( cat_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, Source( alpha_1 ), Target( alpha_1 ), ListOfPairsOfMorphismAndIndex, List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
              local deduped_1_2;
              deduped_1_2 := pair_2[1];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( hoisted_1_1, Source( deduped_1_2 ), Range( deduped_1_2 ), UnderlyingMatrix, - UnderlyingMatrix( deduped_1_2 ) ), pair_2[2] );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddSubtractionForMorphisms( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    local deduped_2_1, hoisted_3_1, deduped_4_1;
    deduped_4_1 := ListOfPairsOfMorphismAndIndex( alpha_1 );
    deduped_2_1 := UnderlyingCategoryOfRows( cat_1 );
    hoisted_3_1 := List( ListOfPairsOfMorphismAndIndex( beta_1 ), function ( pair_2 )
            local deduped_1_2;
            deduped_1_2 := pair_2[1];
            return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_2_1, Source( deduped_1_2 ), Range( deduped_1_2 ), UnderlyingMatrix, - UnderlyingMatrix( deduped_1_2 ) ), pair_2[2] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, Source( alpha_1 ), Target( alpha_1 ), ListOfPairsOfMorphismAndIndex, List( [ 1 .. Length( deduped_4_1 ) ], function ( n_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := deduped_4_1[n_2];
              deduped_1_2 := deduped_2_2[1];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_2_1, Source( deduped_1_2 ), Range( deduped_1_2 ), UnderlyingMatrix, UnderlyingMatrix( deduped_1_2 ) + UnderlyingMatrix( hoisted_3_1[n_2][1] ) ), deduped_2_2[2] );
          end ) );
end
########
        
    , 201 : IsPrecompiledDerivation := true );
    
    ##
    AddZeroObject( cat,
        
########
function ( cat_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, ListOfPairsOfObjectAndIndex, [  ] );
end
########
        
    , 100 );
    
    ##
    AddDirectSum( cat,
        
########
function ( cat_1, objects_1 )
    local deduped_2_1;
    deduped_2_1 := UnderlyingCategoryOfRows( cat_1 );
    return CreateCapCategoryObjectWithAttributes( cat_1, ListOfPairsOfObjectAndIndex, List( COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfObjectAndIndex( deduped_2_1, List( objects_1, ListOfPairsOfObjectAndIndex ) ), function ( pair_2 )
              return NTuple( 2, CreateCapCategoryObjectWithAttributes( deduped_2_1, RankOfObject, Sum( List( pair_2[1], RankOfObject ) ) ), pair_2[2] );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddDirectSumFunctorialWithGivenDirectSums( cat,
        
########
function ( cat_1, P_1, objects_1, L_1, objectsp_1, Pp_1 )
    local hoisted_2_1, deduped_3_1, hoisted_4_1, hoisted_5_1, deduped_7_1, deduped_8_1;
    deduped_8_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_7_1 := COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfMorphismAndIndex( deduped_8_1, List( L_1, ListOfPairsOfMorphismAndIndex ) );
    hoisted_5_1 := UnderlyingRing( cat_1 );
    hoisted_4_1 := ListOfPairsOfObjectAndIndex( Pp_1 );
    deduped_3_1 := CreateCapCategoryObjectWithAttributes( deduped_8_1, RankOfObject, 0 );
    hoisted_2_1 := ListOfPairsOfObjectAndIndex( P_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, P_1, Pp_1, ListOfPairsOfMorphismAndIndex, List( [ 1 .. Length( deduped_7_1 ) ], function ( i_2 )
              local deduped_2_2, deduped_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := deduped_7_1[i_2];
              deduped_4_2 := deduped_5_2[2];
              deduped_3_2 := Filtered( hoisted_4_1, function ( pair_3 )
                      return pair_3[2] = deduped_4_2;
                  end );
              deduped_2_2 := Filtered( hoisted_2_1, function ( pair_3 )
                      return pair_3[2] = deduped_4_2;
                  end );
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_8_1, CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if Length( deduped_2_2 ) = 0 then
                                return deduped_3_1;
                            else
                                return deduped_2_2[1][1];
                            fi;
                            return;
                        end )(  ), CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if Length( deduped_3_2 ) = 0 then
                                return deduped_3_1;
                            else
                                return deduped_3_2[1][1];
                            fi;
                            return;
                        end )(  ), UnderlyingMatrix, DiagMat( hoisted_5_1, List( deduped_5_2[1], UnderlyingMatrix ) ) ), deduped_4_2 );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddUniversalMorphismIntoDirectSumWithGivenDirectSum( cat,
        
########
function ( cat_1, objects_1, T_1, tau_1, P_1 )
    local hoisted_2_1, hoisted_4_1, hoisted_5_1, deduped_7_1, deduped_8_1, deduped_9_1;
    deduped_9_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_8_1 := CreateCapCategoryObjectWithAttributes( deduped_9_1, RankOfObject, 0 );
    deduped_7_1 := COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZeroObjectInList( deduped_9_1, List( ListOfPairsOfObjectAndIndex( T_1 ), function ( pair_2 )
              return NTuple( 2, [ pair_2[1] ], pair_2[2] );
          end ), COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfObjectAndIndex( deduped_9_1, List( objects_1, ListOfPairsOfObjectAndIndex ) ), [ deduped_8_1 ] );
    hoisted_5_1 := UnderlyingRing( cat_1 );
    hoisted_4_1 := COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfMorphismAndIndex( deduped_9_1, List( tau_1, ListOfPairsOfMorphismAndIndex ) );
    hoisted_2_1 := ListOfPairsOfObjectAndIndex( P_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, T_1, P_1, ListOfPairsOfMorphismAndIndex, List( [ 1 .. Length( deduped_7_1 ) ], function ( n_2 )
              local deduped_2_2, deduped_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := deduped_7_1[n_2];
              deduped_4_2 := deduped_5_2[3];
              deduped_3_2 := deduped_5_2[1][1];
              deduped_2_2 := Filtered( hoisted_2_1, function ( pair_3 )
                      return pair_3[2] = deduped_4_2;
                  end );
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_9_1, deduped_3_2, CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if Length( deduped_2_2 ) = 0 then
                                return deduped_8_1;
                            else
                                return deduped_2_2[1][1];
                            fi;
                            return;
                        end )(  ), UnderlyingMatrix, UnionOfColumns( hoisted_5_1, CAP_JIT_INCOMPLETE_LOGIC( RankOfObject( CAP_JIT_INCOMPLETE_LOGIC( deduped_3_2 ) ) ), List( hoisted_4_1[n_2][1], UnderlyingMatrix ) ) ), deduped_4_2 );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.UniversalMorphismIntoDirectSumWithGivenDirectSum :=
        
########
function ( cat_1, objects_1, T_1, tau_1, P_1 )
    local hoisted_2_1, hoisted_4_1, hoisted_5_1, deduped_7_1, deduped_8_1, deduped_9_1;
    deduped_9_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_8_1 := CreateCapCategoryObjectWithAttributes( deduped_9_1, RankOfObject, 0 );
    deduped_7_1 := COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZeroObjectInList( deduped_9_1, List( ListOfPairsOfObjectAndIndex( T_1 ), function ( pair_2 )
              return NTuple( 2, [ pair_2[1] ], pair_2[2] );
          end ), COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfObjectAndIndex( deduped_9_1, List( objects_1, ListOfPairsOfObjectAndIndex ) ), [ deduped_8_1 ] );
    hoisted_5_1 := UnderlyingRing( cat_1 );
    hoisted_4_1 := COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfMorphismAndIndex( deduped_9_1, List( tau_1, ListOfPairsOfMorphismAndIndex ) );
    hoisted_2_1 := ListOfPairsOfObjectAndIndex( P_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, T_1, P_1, ListOfPairsOfMorphismAndIndex, List( [ 1 .. Length( deduped_7_1 ) ], function ( n_2 )
              local deduped_2_2, deduped_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := deduped_7_1[n_2];
              deduped_4_2 := deduped_5_2[3];
              deduped_3_2 := deduped_5_2[1];
              deduped_2_2 := Filtered( hoisted_2_1, function ( pair_3 )
                      return pair_3[2] = deduped_4_2;
                  end );
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_9_1, deduped_3_2[1], CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if Length( deduped_2_2 ) = 0 then
                                return deduped_8_1;
                            else
                                return deduped_2_2[1][1];
                            fi;
                            return;
                        end )(  ), UnderlyingMatrix, UnionOfColumns( hoisted_5_1, List( deduped_3_2, RankOfObject )[1], List( hoisted_4_1[n_2][1], UnderlyingMatrix ) ) ), deduped_4_2 );
          end ) );
end
########
        
    ;
    
    ##
    AddUniversalMorphismFromDirectSumWithGivenDirectSum( cat,
        
########
function ( cat_1, objects_1, T_1, tau_1, P_1 )
    local hoisted_2_1, hoisted_4_1, hoisted_5_1, deduped_7_1, deduped_8_1, deduped_9_1;
    deduped_9_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_8_1 := CreateCapCategoryObjectWithAttributes( deduped_9_1, RankOfObject, 0 );
    deduped_7_1 := COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZeroObjectInList( deduped_9_1, COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfObjectAndIndex( deduped_9_1, List( objects_1, ListOfPairsOfObjectAndIndex ) ), List( ListOfPairsOfObjectAndIndex( T_1 ), function ( pair_2 )
              return NTuple( 2, [ pair_2[1] ], pair_2[2] );
          end ), [ deduped_8_1 ] );
    hoisted_5_1 := UnderlyingRing( cat_1 );
    hoisted_4_1 := COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfMorphismAndIndex( deduped_9_1, List( tau_1, ListOfPairsOfMorphismAndIndex ) );
    hoisted_2_1 := ListOfPairsOfObjectAndIndex( P_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, P_1, T_1, ListOfPairsOfMorphismAndIndex, List( [ 1 .. Length( deduped_7_1 ) ], function ( n_2 )
              local deduped_2_2, deduped_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := deduped_7_1[n_2];
              deduped_4_2 := deduped_5_2[3];
              deduped_3_2 := deduped_5_2[2][1];
              deduped_2_2 := Filtered( hoisted_2_1, function ( pair_3 )
                      return pair_3[2] = deduped_4_2;
                  end );
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_9_1, CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if Length( deduped_2_2 ) = 0 then
                                return deduped_8_1;
                            else
                                return deduped_2_2[1][1];
                            fi;
                            return;
                        end )(  ), deduped_3_2, UnderlyingMatrix, UnionOfRows( hoisted_5_1, CAP_JIT_INCOMPLETE_LOGIC( RankOfObject( CAP_JIT_INCOMPLETE_LOGIC( deduped_3_2 ) ) ), List( hoisted_4_1[n_2][1], UnderlyingMatrix ) ) ), deduped_4_2 );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.UniversalMorphismFromDirectSumWithGivenDirectSum :=
        
########
function ( cat_1, objects_1, T_1, tau_1, P_1 )
    local hoisted_2_1, hoisted_4_1, hoisted_5_1, deduped_7_1, deduped_8_1, deduped_9_1;
    deduped_9_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_8_1 := CreateCapCategoryObjectWithAttributes( deduped_9_1, RankOfObject, 0 );
    deduped_7_1 := COPRODUCT_OF_CATEGORY_OF_ROWS_MergePairsWithZeroObjectInList( deduped_9_1, COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfObjectAndIndex( deduped_9_1, List( objects_1, ListOfPairsOfObjectAndIndex ) ), List( ListOfPairsOfObjectAndIndex( T_1 ), function ( pair_2 )
              return NTuple( 2, [ pair_2[1] ], pair_2[2] );
          end ), [ deduped_8_1 ] );
    hoisted_5_1 := UnderlyingRing( cat_1 );
    hoisted_4_1 := COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfMorphismAndIndex( deduped_9_1, List( tau_1, ListOfPairsOfMorphismAndIndex ) );
    hoisted_2_1 := ListOfPairsOfObjectAndIndex( P_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, P_1, T_1, ListOfPairsOfMorphismAndIndex, List( [ 1 .. Length( deduped_7_1 ) ], function ( n_2 )
              local deduped_2_2, deduped_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := deduped_7_1[n_2];
              deduped_4_2 := deduped_5_2[3];
              deduped_3_2 := deduped_5_2[2];
              deduped_2_2 := Filtered( hoisted_2_1, function ( pair_3 )
                      return pair_3[2] = deduped_4_2;
                  end );
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_9_1, CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if Length( deduped_2_2 ) = 0 then
                                return deduped_8_1;
                            else
                                return deduped_2_2[1][1];
                            fi;
                            return;
                        end )(  ), deduped_3_2[1], UnderlyingMatrix, UnionOfRows( hoisted_5_1, List( deduped_3_2, RankOfObject )[1], List( hoisted_4_1[n_2][1], UnderlyingMatrix ) ) ), deduped_4_2 );
          end ) );
end
########
        
    ;
    
    ##
    AddMultiplyWithElementOfCommutativeRingForMorphisms( cat,
        
########
function ( cat_1, r_1, alpha_1 )
    local hoisted_1_1;
    hoisted_1_1 := UnderlyingCategoryOfRows( cat_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, Source( alpha_1 ), Target( alpha_1 ), ListOfPairsOfMorphismAndIndex, List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
              local deduped_1_2;
              deduped_1_2 := pair_2[1];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( hoisted_1_1, Source( deduped_1_2 ), Range( deduped_1_2 ), UnderlyingMatrix, r_1 * UnderlyingMatrix( deduped_1_2 ) ), pair_2[2] );
          end ) );
end
########
        
    , 100 );
    
    if IsBound( cat!.precompiled_functions_added ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "precompiled functions have already been added before" );
        
    fi;
    
    cat!.precompiled_functions_added := true;
    
end );

BindGlobal( "CoproductOfCategoryOfRowsWithSparseDatastructure_Field", function ( homalg_ring )
  local category_constructor, cat;
    
    category_constructor :=
        
        
        function ( homalg_ring )
    return CoproductOfCategoryOfRowsWithSparseDatastructure( CategoryOfRows( homalg_ring : FinalizeCategory := true ), 5 );
end;
        
        
    
    cat := category_constructor( homalg_ring : FinalizeCategory := false, no_precompiled_code := true );
    
    ADD_FUNCTIONS_FOR_CoproductOfCategoryOfRowsWithSparseDatastructure_Field( cat );
    
    Finalize( cat );
    
    return cat;
    
end );
