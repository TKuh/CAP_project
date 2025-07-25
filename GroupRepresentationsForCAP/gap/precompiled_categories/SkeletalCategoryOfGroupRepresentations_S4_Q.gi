# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Implementations
#
BindGlobal( "ADD_FUNCTIONS_FOR_SkeletalCategoryOfGroupRepresentations_S4_Q", function ( cat )
    
    ##
    AddIsEqualForObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_3_1, hoisted_4_1, deduped_5_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1;
    deduped_9_1 := ListOfPairsOfRankAndIndex( arg3_1 );
    deduped_8_1 := ListOfPairsOfRankAndIndex( arg2_1 );
    deduped_7_1 := Length( deduped_9_1 );
    deduped_6_1 := Length( deduped_8_1 );
    deduped_5_1 := [ 1 .. deduped_7_1 ];
    hoisted_4_1 := List( deduped_5_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( CAP_JIT_INCOMPLETE_LOGIC( deduped_9_1[i_2] )[1] );
        end );
    hoisted_3_1 := List( deduped_5_1, function ( i_2 )
            return CAP_JIT_INCOMPLETE_LOGIC( CAP_JIT_INCOMPLETE_LOGIC( deduped_9_1[i_2] )[2] );
        end );
    return deduped_6_1 = deduped_7_1 and ForAll( [ 1 .. deduped_6_1 ], function ( i_2 )
              local deduped_1_2;
              deduped_1_2 := CAP_JIT_INCOMPLETE_LOGIC( deduped_8_1[CAP_JIT_INCOMPLETE_LOGIC( i_2 )] );
              return (CAP_JIT_INCOMPLETE_LOGIC( deduped_1_2[2] ) = hoisted_3_1[i_2] and CAP_JIT_INCOMPLETE_LOGIC( deduped_1_2[1] ) = hoisted_4_1[i_2]);
          end );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.IsEqualForObjects :=
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, deduped_9_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1;
    deduped_14_1 := ListOfPairsOfRankAndIndex( arg3_1 );
    deduped_13_1 := ListOfPairsOfRankAndIndex( arg2_1 );
    deduped_12_1 := Length( deduped_14_1 );
    deduped_11_1 := Length( deduped_13_1 );
    deduped_10_1 := [ 1 .. deduped_12_1 ];
    deduped_9_1 := [ 1 .. deduped_11_1 ];
    hoisted_7_1 := List( deduped_14_1, function ( logic_new_func_x_2 )
            return logic_new_func_x_2[1];
        end );
    hoisted_8_1 := List( deduped_10_1, function ( i_2 )
            return hoisted_7_1[i_2];
        end );
    hoisted_5_1 := List( deduped_13_1, function ( logic_new_func_x_2 )
            return logic_new_func_x_2[1];
        end );
    hoisted_6_1 := List( deduped_9_1, function ( i_2 )
            return hoisted_5_1[i_2];
        end );
    hoisted_3_1 := List( deduped_14_1, function ( logic_new_func_x_2 )
            return logic_new_func_x_2[2];
        end );
    hoisted_4_1 := List( deduped_10_1, function ( i_2 )
            return hoisted_3_1[i_2];
        end );
    hoisted_1_1 := List( deduped_13_1, function ( logic_new_func_x_2 )
            return logic_new_func_x_2[2];
        end );
    hoisted_2_1 := List( deduped_9_1, function ( i_2 )
            return hoisted_1_1[i_2];
        end );
    return deduped_11_1 = deduped_12_1 and ForAll( deduped_9_1, function ( i_2 )
              return (hoisted_2_1[i_2] = hoisted_4_1[i_2] and hoisted_6_1[i_2] = hoisted_8_1[i_2]);
          end );
end
########
        
    ;
    
    ##
    AddTensorProductOnObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_4_1, hoisted_5_1, hoisted_7_1, hoisted_8_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1;
    deduped_13_1 := ListOfPairsOfRankAndIndex( arg3_1 );
    deduped_12_1 := ListOfPairsOfRankAndIndex( arg2_1 );
    deduped_11_1 := UnderlyingCategoryOfRows( UnderlyingCoproductOfCategoryOfRows( cat_1 ) );
    hoisted_8_1 := [ 1 .. Length( deduped_13_1 ) ];
    hoisted_7_1 := List( deduped_13_1, function ( logic_new_func_x_2 )
            return logic_new_func_x_2[1];
        end );
    hoisted_5_1 := List( deduped_13_1, function ( logic_new_func_x_2 )
            return logic_new_func_x_2[2];
        end );
    deduped_4_1 := UnderlyingIrreducibleCharacters( cat_1 );
    deduped_10_1 := COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfObjectAndIndex( deduped_11_1, List( [ 1 .. Length( deduped_12_1 ) ], function ( i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := CAP_JIT_INCOMPLETE_LOGIC( deduped_12_1[i_2] );
              hoisted_2_2 := CAP_JIT_INCOMPLETE_LOGIC( deduped_5_2[1] );
              hoisted_1_2 := deduped_4_1[CAP_JIT_INCOMPLETE_LOGIC( deduped_5_2[2] )];
              deduped_4_2 := COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfObjectAndIndex( deduped_11_1, List( hoisted_8_1, function ( i_3 )
                        local hoisted_2_3, deduped_3_3;
                        deduped_3_3 := CATEGORY_OF_SKELETAL_GROUP_REPRESENTATIONS_DECOMPOSE_CHARACTER( deduped_11_1, deduped_4_1, hoisted_1_2 * deduped_4_1[hoisted_5_1[i_3]] );
                        hoisted_2_3 := hoisted_2_2 * hoisted_7_1[i_3];
                        return List( [ 1 .. Length( deduped_3_3 ) ], function ( i_4 )
                                local deduped_1_4;
                                deduped_1_4 := CAP_JIT_INCOMPLETE_LOGIC( deduped_3_3[CAP_JIT_INCOMPLETE_LOGIC( i_4 )] );
                                return NTuple( 2, CreateCapCategoryObjectWithAttributes( deduped_11_1, RankOfObject, CAP_JIT_INCOMPLETE_LOGIC( RankOfObject( deduped_1_4[1] ) * hoisted_2_3 ) ), CAP_JIT_INCOMPLETE_LOGIC( deduped_1_4[2] ) );
                            end );
                    end ) );
              return List( [ 1 .. Length( deduped_4_2 ) ], function ( i_3 )
                      local deduped_1_3;
                      deduped_1_3 := CAP_JIT_INCOMPLETE_LOGIC( deduped_4_2[CAP_JIT_INCOMPLETE_LOGIC( i_3 )] );
                      return NTuple( 2, CreateCapCategoryObjectWithAttributes( deduped_11_1, RankOfObject, CAP_JIT_INCOMPLETE_LOGIC( Sum( List( deduped_1_3[1], RankOfObject ) ) ) ), CAP_JIT_INCOMPLETE_LOGIC( deduped_1_3[2] ) );
                  end );
          end ) );
    return CreateCapCategoryObjectWithAttributes( cat_1, ListOfPairsOfRankAndIndex, List( [ 1 .. Length( deduped_10_1 ) ], function ( i_2 )
              local deduped_1_2;
              deduped_1_2 := CAP_JIT_INCOMPLETE_LOGIC( deduped_10_1[i_2] );
              return NTuple( 2, CAP_JIT_INCOMPLETE_LOGIC( Sum( List( deduped_1_2[1], RankOfObject ) ) ), CAP_JIT_INCOMPLETE_LOGIC( deduped_1_2[2] ) );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.TensorProductOnObjects :=
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_3_1, deduped_4_1, hoisted_5_1, hoisted_7_1, hoisted_8_1, hoisted_9_1, hoisted_10_1, hoisted_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1;
    deduped_15_1 := ListOfPairsOfRankAndIndex( arg3_1 );
    deduped_14_1 := ListOfPairsOfRankAndIndex( arg2_1 );
    deduped_13_1 := UnderlyingCategoryOfRows( UnderlyingCoproductOfCategoryOfRows( cat_1 ) );
    hoisted_9_1 := [ 1 .. Length( deduped_15_1 ) ];
    hoisted_8_1 := List( deduped_15_1, function ( logic_new_func_x_2 )
            return logic_new_func_x_2[1];
        end );
    hoisted_7_1 := List( deduped_14_1, function ( logic_new_func_x_2 )
            return logic_new_func_x_2[1];
        end );
    hoisted_5_1 := List( deduped_15_1, function ( logic_new_func_x_2 )
            return logic_new_func_x_2[2];
        end );
    deduped_4_1 := UnderlyingIrreducibleCharacters( cat_1 );
    hoisted_3_1 := List( deduped_14_1, function ( logic_new_func_x_2 )
            return logic_new_func_x_2[2];
        end );
    deduped_12_1 := COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfObjectAndIndex( deduped_13_1, List( [ 1 .. Length( deduped_14_1 ) ], function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, hoisted_4_2, hoisted_5_2, hoisted_6_2, deduped_7_2, deduped_8_2;
              hoisted_2_2 := hoisted_7_1[i_2];
              hoisted_1_2 := deduped_4_1[hoisted_3_1[i_2]];
              deduped_8_2 := COPRODUCT_OF_CATEGORY_OF_ROWS_MergeMatrixOfPairsOfObjectAndIndex( deduped_13_1, List( hoisted_9_1, function ( i_3 )
                        local hoisted_1_3, hoisted_2_3, hoisted_3_3, hoisted_4_3, hoisted_5_3, deduped_6_3, deduped_7_3;
                        deduped_7_3 := CATEGORY_OF_SKELETAL_GROUP_REPRESENTATIONS_DECOMPOSE_CHARACTER( deduped_13_1, deduped_4_1, hoisted_1_2 * deduped_4_1[hoisted_5_1[i_3]] );
                        deduped_6_3 := [ 1 .. Length( deduped_7_3 ) ];
                        hoisted_4_3 := List( deduped_7_3, function ( pair_4 )
                                return pair_4[2];
                            end );
                        hoisted_5_3 := List( deduped_6_3, function ( i_4 )
                                return hoisted_4_3[i_4];
                            end );
                        hoisted_1_3 := hoisted_2_2 * hoisted_8_1[i_3];
                        hoisted_2_3 := List( deduped_7_3, function ( pair_4 )
                                return RankOfObject( pair_4[1] ) * hoisted_1_3;
                            end );
                        hoisted_3_3 := List( deduped_6_3, function ( i_4 )
                                return hoisted_2_3[i_4];
                            end );
                        return List( deduped_6_3, function ( i_4 )
                                return NTuple( 2, CreateCapCategoryObjectWithAttributes( deduped_13_1, RankOfObject, hoisted_3_3[i_4] ), hoisted_5_3[i_4] );
                            end );
                    end ) );
              deduped_7_2 := [ 1 .. Length( deduped_8_2 ) ];
              hoisted_5_2 := List( deduped_8_2, function ( pair_3 )
                      return pair_3[2];
                  end );
              hoisted_6_2 := List( deduped_7_2, function ( i_3 )
                      return hoisted_5_2[i_3];
                  end );
              hoisted_3_2 := List( deduped_8_2, function ( pair_3 )
                      return Sum( List( pair_3[1], RankOfObject ) );
                  end );
              hoisted_4_2 := List( deduped_7_2, function ( i_3 )
                      return hoisted_3_2[i_3];
                  end );
              return List( deduped_7_2, function ( i_3 )
                      return NTuple( 2, CreateCapCategoryObjectWithAttributes( deduped_13_1, RankOfObject, hoisted_4_2[i_3] ), hoisted_6_2[i_3] );
                  end );
          end ) );
    hoisted_11_1 := List( deduped_12_1, function ( pair_2 )
            return pair_2[2];
        end );
    hoisted_10_1 := List( deduped_12_1, function ( pair_2 )
            return Sum( List( pair_2[1], RankOfObject ) );
        end );
    return CreateCapCategoryObjectWithAttributes( cat_1, ListOfPairsOfRankAndIndex, List( [ 1 .. Length( deduped_12_1 ) ], function ( i_2 )
              return NTuple( 2, hoisted_10_1[i_2], hoisted_11_1[i_2] );
          end ) );
end
########
        
    ;
    
    ##
    AddTensorProductOnMorphismsWithGivenTensorProducts( cat,
        
########
function ( cat_1, s_1, alpha_1, beta_1, r_1 )
    local deduped_1_1, deduped_2_1, hoisted_3_1, hoisted_5_1, deduped_6_1;
    deduped_6_1 := UnderlyingSplittingField( cat_1 );
    deduped_1_1 := UnderlyingCategoryOfRows( UnderlyingCoproductOfCategoryOfRows( cat_1 ) );
    hoisted_5_1 := Cartesian( [ List( ListOfPairsOfMatrixAndIndex( alpha_1 ), function ( pair_2 )
                  local deduped_1_2;
                  deduped_1_2 := pair_2[1];
                  return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_1_1, CreateCapCategoryObjectWithAttributes( deduped_1_1, RankOfObject, NumberRows( deduped_1_2 ) ), CreateCapCategoryObjectWithAttributes( deduped_1_1, RankOfObject, NumberColumns( deduped_1_2 ) ), UnderlyingMatrix, deduped_1_2 ), pair_2[2] );
              end ), List( ListOfPairsOfMatrixAndIndex( beta_1 ), function ( pair_2 )
                  local deduped_1_2;
                  deduped_1_2 := pair_2[1];
                  return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_1_1, CreateCapCategoryObjectWithAttributes( deduped_1_1, RankOfObject, NumberRows( deduped_1_2 ) ), CreateCapCategoryObjectWithAttributes( deduped_1_1, RankOfObject, NumberColumns( deduped_1_2 ) ), UnderlyingMatrix, deduped_1_2 ), pair_2[2] );
              end ) ] );
    hoisted_3_1 := HomalgZeroMatrix( 0, 0, deduped_6_1 );
    deduped_2_1 := UnderlyingIrreducibleCharacters( cat_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, s_1, r_1, ListOfPairsOfMatrixAndIndex, List( [ 1 .. NrIrreducibleCharacters( cat_1 ) ], function ( i_2 )
              local hoisted_1_2;
              hoisted_1_2 := deduped_2_1[CAP_JIT_INCOMPLETE_LOGIC( i_2 )];
              return NTuple( 2, CAP_JIT_INCOMPLETE_LOGIC( DiagMat( deduped_6_1, List( hoisted_5_1, function ( pair_3 )
                            local deduped_1_3, deduped_2_3, deduped_3_3, deduped_4_3, deduped_5_3;
                            deduped_5_3 := List( pair_3, function ( logic_new_func_x_4 )
                                    return logic_new_func_x_4[2];
                                end );
                            deduped_4_3 := List( pair_3, function ( logic_new_func_x_4 )
                                    return logic_new_func_x_4[1];
                                end );
                            deduped_3_3 := KroneckerMat( UnderlyingMatrix( deduped_4_3[1] ), UnderlyingMatrix( deduped_4_3[2] ) );
                            deduped_2_3 := CAP_JIT_INCOMPLETE_LOGIC( NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_1_1, CreateCapCategoryObjectWithAttributes( deduped_1_1, RankOfObject, NumberRows( deduped_3_3 ) ), CreateCapCategoryObjectWithAttributes( deduped_1_1, RankOfObject, NumberColumns( deduped_3_3 ) ), UnderlyingMatrix, deduped_3_3 ), NTuple( 2, deduped_5_3[1], deduped_5_3[2] ) )[2] );
                            deduped_1_3 := ScalarProduct( hoisted_1_2, deduped_2_1[CAP_JIT_INCOMPLETE_LOGIC( deduped_2_3[1] )] * deduped_2_1[CAP_JIT_INCOMPLETE_LOGIC( deduped_2_3[2] )] );
                            if deduped_1_3 = 0 then
                                return hoisted_3_1;
                            else
                                return KroneckerMat( deduped_3_3, HomalgIdentityMatrix( deduped_1_3, deduped_6_1 ) );
                            fi;
                            return;
                        end ) ) ), i_2 );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.TensorProductOnMorphismsWithGivenTensorProducts :=
        
########
function ( cat_1, s_1, alpha_1, beta_1, r_1 )
    local deduped_1_1, deduped_2_1, hoisted_3_1, hoisted_5_1, hoisted_6_1, deduped_7_1, deduped_8_1;
    deduped_8_1 := UnderlyingSplittingField( cat_1 );
    deduped_7_1 := [ 1 .. NrIrreducibleCharacters( cat_1 ) ];
    deduped_1_1 := UnderlyingCategoryOfRows( UnderlyingCoproductOfCategoryOfRows( cat_1 ) );
    hoisted_5_1 := Cartesian( [ List( ListOfPairsOfMatrixAndIndex( alpha_1 ), function ( pair_2 )
                  local deduped_1_2;
                  deduped_1_2 := pair_2[1];
                  return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_1_1, CreateCapCategoryObjectWithAttributes( deduped_1_1, RankOfObject, NumberRows( deduped_1_2 ) ), CreateCapCategoryObjectWithAttributes( deduped_1_1, RankOfObject, NumberColumns( deduped_1_2 ) ), UnderlyingMatrix, deduped_1_2 ), pair_2[2] );
              end ), List( ListOfPairsOfMatrixAndIndex( beta_1 ), function ( pair_2 )
                  local deduped_1_2;
                  deduped_1_2 := pair_2[1];
                  return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_1_1, CreateCapCategoryObjectWithAttributes( deduped_1_1, RankOfObject, NumberRows( deduped_1_2 ) ), CreateCapCategoryObjectWithAttributes( deduped_1_1, RankOfObject, NumberColumns( deduped_1_2 ) ), UnderlyingMatrix, deduped_1_2 ), pair_2[2] );
              end ) ] );
    hoisted_3_1 := HomalgZeroMatrix( 0, 0, deduped_8_1 );
    deduped_2_1 := UnderlyingIrreducibleCharacters( cat_1 );
    hoisted_6_1 := List( deduped_7_1, function ( l_2 )
            local hoisted_1_2;
            hoisted_1_2 := deduped_2_1[l_2];
            return DiagMat( deduped_8_1, List( hoisted_5_1, function ( pair_3 )
                      local deduped_1_3, deduped_2_3, deduped_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3;
                      deduped_7_3 := List( pair_3, function ( logic_new_func_x_4 )
                              return logic_new_func_x_4[2];
                          end );
                      deduped_6_3 := List( pair_3, function ( logic_new_func_x_4 )
                              return logic_new_func_x_4[1];
                          end );
                      deduped_5_3 := deduped_6_3[2];
                      deduped_4_3 := deduped_6_3[1];
                      deduped_3_3 := KroneckerMat( UnderlyingMatrix( deduped_4_3 ), UnderlyingMatrix( deduped_5_3 ) );
                      deduped_2_3 := NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_1_1, CreateCapCategoryObjectWithAttributes( deduped_1_1, RankOfObject, RankOfObject( Source( deduped_4_3 ) ) * RankOfObject( Source( deduped_5_3 ) ) ), CreateCapCategoryObjectWithAttributes( deduped_1_1, RankOfObject, RankOfObject( Range( deduped_4_3 ) ) * RankOfObject( Range( deduped_5_3 ) ) ), UnderlyingMatrix, deduped_3_3 ), NTuple( 2, deduped_7_3[1], deduped_7_3[2] ) );
                      deduped_1_3 := ScalarProduct( hoisted_1_2, deduped_2_1[List( deduped_2_3, function ( logic_new_func_x_4 )
                                     return logic_new_func_x_4[1];
                                 end )[2]] * deduped_2_1[List( deduped_2_3, function ( logic_new_func_x_4 )
                                     return logic_new_func_x_4[2];
                                 end )[2]] );
                      if deduped_1_3 = 0 then
                          return hoisted_3_1;
                      else
                          return KroneckerMat( deduped_3_3, HomalgIdentityMatrix( deduped_1_3, deduped_8_1 ) );
                      fi;
                      return;
                  end ) );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, s_1, r_1, ListOfPairsOfMatrixAndIndex, List( deduped_7_1, function ( i_2 )
              return NTuple( 2, hoisted_6_1[i_2], i_2 );
          end ) );
end
########
        
    ;
    
    if IsBound( cat!.precompiled_functions_added ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "precompiled functions have already been added before" );
        
    fi;
    
    cat!.precompiled_functions_added := true;
    
end );

BindGlobal( "SkeletalCategoryOfGroupRepresentations_S4_Q", function ( group, homalg_field )
  local category_constructor, cat;
    
    category_constructor :=
        
        
        function ( group, homalg_field )
    return SkeletalCategoryOfGroupRepresentations( group, homalg_field );
end;
        
        
    
    cat := category_constructor( group, homalg_field : FinalizeCategory := false, no_precompiled_code := true );
    
    ADD_FUNCTIONS_FOR_SkeletalCategoryOfGroupRepresentations_S4_Q( cat );
    
    Finalize( cat );
    
    return cat;
    
end );
