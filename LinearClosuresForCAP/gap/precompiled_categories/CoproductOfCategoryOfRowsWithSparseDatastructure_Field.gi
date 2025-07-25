# SPDX-License-Identifier: GPL-2.0-or-later
# LinearClosuresForCAP: Linear closures
#
# Implementations
#
BindGlobal( "ADD_FUNCTIONS_FOR_CoproductOfCategoryOfRowsWithSparseDatastructure_Field", function ( cat )
    
    ##
    AddAdditionForMorphisms( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    local deduped_2_1, hoisted_5_1, deduped_7_1, deduped_8_1, hoisted_10_1, hoisted_11_1, deduped_12_1, hoisted_13_1, hoisted_14_1, deduped_15_1, hoisted_16_1, hoisted_17_1, hoisted_18_1, hoisted_19_1, deduped_20_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1, deduped_30_1, deduped_31_1, deduped_32_1, deduped_33_1;
    deduped_33_1 := [  ];
    deduped_32_1 := UnderlyingRing( cat_1 );
    deduped_31_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_30_1 := Range( alpha_1 );
    deduped_29_1 := Source( alpha_1 );
    deduped_28_1 := [ 1 .. deduped_31_1 ];
    deduped_27_1 := ListWithIdenticalEntries( deduped_31_1, deduped_33_1 );
    deduped_26_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
    deduped_25_1 := ListWithIdenticalEntries( deduped_31_1, 0 );
    deduped_24_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_30_1 ), deduped_25_1 );
    deduped_23_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_29_1 ), deduped_25_1 );
    deduped_22_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_20_1 := List( [ 0 .. Length( deduped_24_1 ) ], function ( i_2 )
            return Sum( deduped_24_1{[ 1 .. i_2 ]} );
        end );
    hoisted_18_1 := [ 1 .. Sum( deduped_24_1 ) ];
    hoisted_5_1 := UnderlyingCategory( deduped_26_1 );
    deduped_7_1 := List( deduped_28_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_26_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_5_1, IndexOfObject, i_2 ) );
        end );
    hoisted_16_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( beta_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := deduped_7_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_26_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), deduped_27_1 );
    deduped_15_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( beta_1 ) ), deduped_25_1 );
    hoisted_14_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( beta_1 ) ), deduped_25_1 );
    deduped_12_1 := ZeroImmutable( deduped_32_1 );
    hoisted_17_1 := Concatenation( List( deduped_28_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
              deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
              deduped_3_2 := hoisted_14_1[deduped_4_2];
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_31_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_15_1[i_3], deduped_12_1 );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_15_1[i_3], deduped_12_1 );
                    end ) );
              return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_3_2 > 0 and deduped_15_1[deduped_4_2] = 0 then
                                return ListWithIdenticalEntries( deduped_3_2, deduped_33_1 );
                            else
                                return hoisted_16_1[deduped_4_2];
                            fi;
                            return;
                        end )(  ), function ( row_3 )
                        return Concatenation( hoisted_1_2, List( row_3, Coefficient ), hoisted_2_2 );
                    end ) );
          end ) );
    deduped_8_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := deduped_7_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_26_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), deduped_27_1 );
    hoisted_13_1 := Concatenation( List( deduped_28_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
              deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
              deduped_3_2 := deduped_23_1[deduped_4_2];
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_31_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_24_1[i_3], deduped_12_1 );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_24_1[i_3], deduped_12_1 );
                    end ) );
              return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_3_2 > 0 and deduped_24_1[deduped_4_2] = 0 then
                                return ListWithIdenticalEntries( deduped_3_2, deduped_33_1 );
                            else
                                return deduped_8_1[deduped_4_2];
                            fi;
                            return;
                        end )(  ), function ( row_3 )
                        return Concatenation( hoisted_1_2, List( row_3, Coefficient ), hoisted_2_2 );
                    end ) );
          end ) );
    hoisted_11_1 := Concatenation( List( deduped_28_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
              deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
              deduped_3_2 := deduped_23_1[deduped_4_2];
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_31_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_24_1[i_3], deduped_7_1[i_3] );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_24_1[i_3], deduped_7_1[i_3] );
                    end ) );
              return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_3_2 > 0 and deduped_24_1[deduped_4_2] = 0 then
                                return ListWithIdenticalEntries( deduped_3_2, deduped_33_1 );
                            else
                                return deduped_8_1[deduped_4_2];
                            fi;
                            return;
                        end )(  ), function ( row_3 )
                        return Concatenation( hoisted_1_2, List( row_3, Target ), hoisted_2_2 );
                    end ) );
          end ) );
    hoisted_10_1 := Concatenation( List( deduped_28_1, function ( m_i_2 )
              local deduped_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
              deduped_4_2 := deduped_23_1[deduped_5_2];
              deduped_1_2 := deduped_7_1[m_i_2];
              hoisted_3_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_31_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_24_1[i_3], deduped_1_2 );
                    end ) );
              hoisted_2_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_24_1[i_3], deduped_1_2 );
                    end ) );
              return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_4_2 > 0 and deduped_24_1[deduped_5_2] = 0 then
                                return ListWithIdenticalEntries( deduped_4_2, deduped_33_1 );
                            else
                                return deduped_8_1[deduped_5_2];
                            fi;
                            return;
                        end )(  ), function ( row_3 )
                        return Concatenation( hoisted_2_2, List( row_3, Source ), hoisted_3_2 );
                    end ) );
          end ) );
    hoisted_19_1 := List( [ 1 .. Sum( deduped_23_1 ) ], function ( i_2 )
            local hoisted_1_2, hoisted_2_2, hoisted_3_2, hoisted_4_2;
            hoisted_4_2 := hoisted_17_1[i_2];
            hoisted_3_2 := hoisted_13_1[i_2];
            hoisted_2_2 := hoisted_11_1[i_2];
            hoisted_1_2 := hoisted_10_1[i_2];
            return List( hoisted_18_1, function ( j_3 )
                    return CreateCapCategoryMorphismWithAttributes( deduped_26_1, hoisted_1_2[j_3], hoisted_2_2[j_3], Coefficient, hoisted_3_2[j_3] + hoisted_4_2[j_3] );
                end );
        end );
    deduped_2_1 := List( [ 0 .. Length( deduped_23_1 ) ], function ( i_2 )
            return Sum( deduped_23_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_29_1, deduped_30_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_23_1, List( deduped_28_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_20_1[obj_idx_2] + 1 .. deduped_20_1[deduped_2_2] ];
                  return List( [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_19_1[nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_24_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                        return List( row_3, Coefficient );
                    end ), deduped_23_1[deduped_2_2], deduped_24_1[deduped_2_2], deduped_32_1 );
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_22_1, CreateCapCategoryObjectWithAttributes( deduped_22_1, RankOfObject, NumberRows( deduped_1_2 ) ), CreateCapCategoryObjectWithAttributes( deduped_22_1, RankOfObject, NumberColumns( deduped_1_2 ) ), UnderlyingMatrix, deduped_1_2 ), deduped_2_2 );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.AdditionForMorphisms :=
        
########
function ( cat_1, alpha_1, beta_1 )
    local deduped_2_1, hoisted_5_1, deduped_7_1, deduped_8_1, hoisted_11_1, hoisted_12_1, deduped_13_1, hoisted_14_1, hoisted_15_1, deduped_16_1, hoisted_17_1, hoisted_18_1, hoisted_19_1, hoisted_20_1, deduped_21_1, deduped_22_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1, deduped_30_1, deduped_31_1, deduped_32_1, deduped_33_1, deduped_34_1;
    deduped_34_1 := [  ];
    deduped_33_1 := UnderlyingRing( cat_1 );
    deduped_32_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_31_1 := Range( alpha_1 );
    deduped_30_1 := Source( alpha_1 );
    deduped_29_1 := [ 1 .. deduped_32_1 ];
    deduped_28_1 := ListWithIdenticalEntries( deduped_32_1, deduped_34_1 );
    deduped_27_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
    deduped_26_1 := ListWithIdenticalEntries( deduped_32_1, 0 );
    deduped_25_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_31_1 ), deduped_26_1 );
    deduped_24_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_30_1 ), deduped_26_1 );
    deduped_22_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_21_1 := List( [ 0 .. Length( deduped_25_1 ) ], function ( i_2 )
            return Sum( deduped_25_1{[ 1 .. i_2 ]} );
        end );
    hoisted_19_1 := [ 1 .. Sum( deduped_25_1 ) ];
    hoisted_5_1 := UnderlyingCategory( deduped_27_1 );
    deduped_7_1 := List( deduped_29_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_27_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_5_1, IndexOfObject, i_2 ) );
        end );
    hoisted_17_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( beta_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := deduped_7_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_27_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), deduped_28_1 );
    deduped_16_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( beta_1 ) ), deduped_26_1 );
    hoisted_15_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( beta_1 ) ), deduped_26_1 );
    deduped_13_1 := ZeroImmutable( deduped_33_1 );
    hoisted_18_1 := Concatenation( List( deduped_29_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2;
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_32_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_16_1[i_3], deduped_13_1 );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_16_1[i_3], deduped_13_1 );
                    end ) );
              return List( deduped_29_1, function ( i_3 )
                        local deduped_1_3;
                        deduped_1_3 := hoisted_15_1[i_3];
                        return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                    if deduped_1_3 > 0 and deduped_16_1[i_3] = 0 then
                                        return ListWithIdenticalEntries( deduped_1_3, deduped_34_1 );
                                    else
                                        return hoisted_17_1[i_3];
                                    fi;
                                    return;
                                end )(  ), function ( row_4 )
                                return Concatenation( hoisted_1_2, List( row_4, Coefficient ), hoisted_2_2 );
                            end );
                    end )[m_i_2];
          end ) );
    deduped_8_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := deduped_7_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_27_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), deduped_28_1 );
    hoisted_14_1 := Concatenation( List( deduped_29_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2;
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_32_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_25_1[i_3], deduped_13_1 );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_25_1[i_3], deduped_13_1 );
                    end ) );
              return List( deduped_29_1, function ( i_3 )
                        local deduped_1_3;
                        deduped_1_3 := deduped_24_1[i_3];
                        return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                    if deduped_1_3 > 0 and deduped_25_1[i_3] = 0 then
                                        return ListWithIdenticalEntries( deduped_1_3, deduped_34_1 );
                                    else
                                        return deduped_8_1[i_3];
                                    fi;
                                    return;
                                end )(  ), function ( row_4 )
                                return Concatenation( hoisted_1_2, List( row_4, Coefficient ), hoisted_2_2 );
                            end );
                    end )[m_i_2];
          end ) );
    hoisted_12_1 := Concatenation( List( deduped_29_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2;
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_32_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_25_1[i_3], deduped_7_1[i_3] );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_25_1[i_3], deduped_7_1[i_3] );
                    end ) );
              return List( deduped_29_1, function ( i_3 )
                        local deduped_1_3;
                        deduped_1_3 := deduped_24_1[i_3];
                        return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                    if deduped_1_3 > 0 and deduped_25_1[i_3] = 0 then
                                        return ListWithIdenticalEntries( deduped_1_3, deduped_34_1 );
                                    else
                                        return deduped_8_1[i_3];
                                    fi;
                                    return;
                                end )(  ), function ( row_4 )
                                return Concatenation( hoisted_1_2, List( row_4, Target ), hoisted_2_2 );
                            end );
                    end )[m_i_2];
          end ) );
    hoisted_11_1 := Concatenation( List( deduped_29_1, function ( m_i_2 )
              local deduped_1_2, hoisted_2_2, hoisted_3_2;
              deduped_1_2 := deduped_7_1[m_i_2];
              hoisted_3_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_32_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_25_1[i_3], deduped_1_2 );
                    end ) );
              hoisted_2_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_25_1[i_3], deduped_1_2 );
                    end ) );
              return List( deduped_29_1, function ( i_3 )
                        local deduped_1_3;
                        deduped_1_3 := deduped_24_1[i_3];
                        return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                    if deduped_1_3 > 0 and deduped_25_1[i_3] = 0 then
                                        return ListWithIdenticalEntries( deduped_1_3, deduped_34_1 );
                                    else
                                        return deduped_8_1[i_3];
                                    fi;
                                    return;
                                end )(  ), function ( row_4 )
                                return Concatenation( hoisted_2_2, List( row_4, Source ), hoisted_3_2 );
                            end );
                    end )[m_i_2];
          end ) );
    hoisted_20_1 := List( [ 1 .. Sum( deduped_24_1 ) ], function ( i_2 )
            local hoisted_1_2, hoisted_2_2, hoisted_3_2, hoisted_4_2;
            hoisted_4_2 := hoisted_18_1[i_2];
            hoisted_3_2 := hoisted_14_1[i_2];
            hoisted_2_2 := hoisted_12_1[i_2];
            hoisted_1_2 := hoisted_11_1[i_2];
            return List( hoisted_19_1, function ( j_3 )
                    return CreateCapCategoryMorphismWithAttributes( deduped_27_1, hoisted_1_2[j_3], hoisted_2_2[j_3], Coefficient, hoisted_3_2[j_3] + hoisted_4_2[j_3] );
                end );
        end );
    deduped_2_1 := List( [ 0 .. Length( deduped_24_1 ) ], function ( i_2 )
            return Sum( deduped_24_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_30_1, deduped_31_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_24_1, List( deduped_29_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_21_1[obj_idx_2] + 1 .. deduped_21_1[deduped_2_2] ];
                  return List( [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_20_1[nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_25_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2, deduped_3_2;
              deduped_3_2 := pair_2[2];
              deduped_2_2 := deduped_25_1[deduped_3_2];
              deduped_1_2 := deduped_24_1[deduped_3_2];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_22_1, CreateCapCategoryObjectWithAttributes( deduped_22_1, RankOfObject, deduped_1_2 ), CreateCapCategoryObjectWithAttributes( deduped_22_1, RankOfObject, deduped_2_2 ), UnderlyingMatrix, HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                            return List( row_3, Coefficient );
                        end ), deduped_1_2, deduped_2_2, deduped_33_1 ) ), deduped_3_2 );
          end ) );
end
########
        
    ;
    
    ##
    AddAdditiveInverseForMorphisms( cat,
        
########
function ( cat_1, alpha_1 )
    local deduped_2_1, hoisted_5_1, deduped_7_1, deduped_8_1, hoisted_10_1, hoisted_11_1, deduped_12_1, hoisted_13_1, hoisted_14_1, hoisted_15_1, hoisted_16_1, deduped_17_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1;
    deduped_29_1 := [  ];
    deduped_28_1 := UnderlyingRing( cat_1 );
    deduped_27_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_26_1 := Range( alpha_1 );
    deduped_25_1 := Source( alpha_1 );
    deduped_24_1 := [ 1 .. deduped_27_1 ];
    deduped_23_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
    deduped_22_1 := ListWithIdenticalEntries( deduped_27_1, 0 );
    deduped_21_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_26_1 ), deduped_22_1 );
    deduped_20_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_25_1 ), deduped_22_1 );
    deduped_19_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_17_1 := List( [ 0 .. Length( deduped_21_1 ) ], function ( i_2 )
            return Sum( deduped_21_1{[ 1 .. i_2 ]} );
        end );
    hoisted_15_1 := [ 1 .. Sum( deduped_21_1 ) ];
    hoisted_14_1 := MinusOne( deduped_28_1 );
    deduped_12_1 := ZeroImmutable( deduped_28_1 );
    hoisted_5_1 := UnderlyingCategory( deduped_23_1 );
    deduped_7_1 := List( deduped_24_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_23_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_5_1, IndexOfObject, i_2 ) );
        end );
    deduped_8_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := deduped_7_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_23_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), ListWithIdenticalEntries( deduped_27_1, deduped_29_1 ) );
    hoisted_13_1 := Concatenation( List( deduped_24_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
              deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
              deduped_3_2 := deduped_20_1[deduped_4_2];
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_27_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_21_1[i_3], deduped_12_1 );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_21_1[i_3], deduped_12_1 );
                    end ) );
              return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_3_2 > 0 and deduped_21_1[deduped_4_2] = 0 then
                                return ListWithIdenticalEntries( deduped_3_2, deduped_29_1 );
                            else
                                return deduped_8_1[deduped_4_2];
                            fi;
                            return;
                        end )(  ), function ( row_3 )
                        return Concatenation( hoisted_1_2, List( row_3, Coefficient ), hoisted_2_2 );
                    end ) );
          end ) );
    hoisted_11_1 := Concatenation( List( deduped_24_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
              deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
              deduped_3_2 := deduped_20_1[deduped_4_2];
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_27_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_21_1[i_3], deduped_7_1[i_3] );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_21_1[i_3], deduped_7_1[i_3] );
                    end ) );
              return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_3_2 > 0 and deduped_21_1[deduped_4_2] = 0 then
                                return ListWithIdenticalEntries( deduped_3_2, deduped_29_1 );
                            else
                                return deduped_8_1[deduped_4_2];
                            fi;
                            return;
                        end )(  ), function ( row_3 )
                        return Concatenation( hoisted_1_2, List( row_3, Target ), hoisted_2_2 );
                    end ) );
          end ) );
    hoisted_10_1 := Concatenation( List( deduped_24_1, function ( m_i_2 )
              local deduped_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
              deduped_4_2 := deduped_20_1[deduped_5_2];
              deduped_1_2 := deduped_7_1[m_i_2];
              hoisted_3_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_27_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_21_1[i_3], deduped_1_2 );
                    end ) );
              hoisted_2_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_21_1[i_3], deduped_1_2 );
                    end ) );
              return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_4_2 > 0 and deduped_21_1[deduped_5_2] = 0 then
                                return ListWithIdenticalEntries( deduped_4_2, deduped_29_1 );
                            else
                                return deduped_8_1[deduped_5_2];
                            fi;
                            return;
                        end )(  ), function ( row_3 )
                        return Concatenation( hoisted_2_2, List( row_3, Source ), hoisted_3_2 );
                    end ) );
          end ) );
    hoisted_16_1 := List( [ 1 .. Sum( deduped_20_1 ) ], function ( i_2 )
            local hoisted_1_2, hoisted_2_2, hoisted_3_2;
            hoisted_3_2 := hoisted_13_1[i_2];
            hoisted_2_2 := hoisted_11_1[i_2];
            hoisted_1_2 := hoisted_10_1[i_2];
            return List( hoisted_15_1, function ( j_3 )
                    return CreateCapCategoryMorphismWithAttributes( deduped_23_1, hoisted_1_2[j_3], hoisted_2_2[j_3], Coefficient, hoisted_3_2[j_3] * hoisted_14_1 );
                end );
        end );
    deduped_2_1 := List( [ 0 .. Length( deduped_20_1 ) ], function ( i_2 )
            return Sum( deduped_20_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_25_1, deduped_26_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_20_1, List( deduped_24_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_17_1[obj_idx_2] + 1 .. deduped_17_1[deduped_2_2] ];
                  return List( [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_16_1[nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_21_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                        return List( row_3, Coefficient );
                    end ), deduped_20_1[deduped_2_2], deduped_21_1[deduped_2_2], deduped_28_1 );
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_19_1, CreateCapCategoryObjectWithAttributes( deduped_19_1, RankOfObject, NumberRows( deduped_1_2 ) ), CreateCapCategoryObjectWithAttributes( deduped_19_1, RankOfObject, NumberColumns( deduped_1_2 ) ), UnderlyingMatrix, deduped_1_2 ), deduped_2_2 );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.AdditiveInverseForMorphisms :=
        
########
function ( cat_1, alpha_1 )
    local deduped_2_1, hoisted_5_1, deduped_7_1, deduped_8_1, hoisted_11_1, hoisted_12_1, deduped_13_1, hoisted_14_1, hoisted_15_1, hoisted_16_1, hoisted_17_1, deduped_18_1, deduped_19_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1, deduped_30_1;
    deduped_30_1 := [  ];
    deduped_29_1 := UnderlyingRing( cat_1 );
    deduped_28_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_27_1 := Range( alpha_1 );
    deduped_26_1 := Source( alpha_1 );
    deduped_25_1 := [ 1 .. deduped_28_1 ];
    deduped_24_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
    deduped_23_1 := ListWithIdenticalEntries( deduped_28_1, 0 );
    deduped_22_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_27_1 ), deduped_23_1 );
    deduped_21_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_26_1 ), deduped_23_1 );
    deduped_19_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_18_1 := List( [ 0 .. Length( deduped_22_1 ) ], function ( i_2 )
            return Sum( deduped_22_1{[ 1 .. i_2 ]} );
        end );
    hoisted_16_1 := [ 1 .. Sum( deduped_22_1 ) ];
    hoisted_15_1 := MinusOne( deduped_29_1 );
    deduped_13_1 := ZeroImmutable( deduped_29_1 );
    hoisted_5_1 := UnderlyingCategory( deduped_24_1 );
    deduped_7_1 := List( deduped_25_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_24_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_5_1, IndexOfObject, i_2 ) );
        end );
    deduped_8_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := deduped_7_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_24_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), ListWithIdenticalEntries( deduped_28_1, deduped_30_1 ) );
    hoisted_14_1 := Concatenation( List( deduped_25_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2;
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_28_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_22_1[i_3], deduped_13_1 );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_22_1[i_3], deduped_13_1 );
                    end ) );
              return List( deduped_25_1, function ( i_3 )
                        local deduped_1_3;
                        deduped_1_3 := deduped_21_1[i_3];
                        return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                    if deduped_1_3 > 0 and deduped_22_1[i_3] = 0 then
                                        return ListWithIdenticalEntries( deduped_1_3, deduped_30_1 );
                                    else
                                        return deduped_8_1[i_3];
                                    fi;
                                    return;
                                end )(  ), function ( row_4 )
                                return Concatenation( hoisted_1_2, List( row_4, Coefficient ), hoisted_2_2 );
                            end );
                    end )[m_i_2];
          end ) );
    hoisted_12_1 := Concatenation( List( deduped_25_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2;
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_28_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_22_1[i_3], deduped_7_1[i_3] );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_22_1[i_3], deduped_7_1[i_3] );
                    end ) );
              return List( deduped_25_1, function ( i_3 )
                        local deduped_1_3;
                        deduped_1_3 := deduped_21_1[i_3];
                        return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                    if deduped_1_3 > 0 and deduped_22_1[i_3] = 0 then
                                        return ListWithIdenticalEntries( deduped_1_3, deduped_30_1 );
                                    else
                                        return deduped_8_1[i_3];
                                    fi;
                                    return;
                                end )(  ), function ( row_4 )
                                return Concatenation( hoisted_1_2, List( row_4, Target ), hoisted_2_2 );
                            end );
                    end )[m_i_2];
          end ) );
    hoisted_11_1 := Concatenation( List( deduped_25_1, function ( m_i_2 )
              local deduped_1_2, hoisted_2_2, hoisted_3_2;
              deduped_1_2 := deduped_7_1[m_i_2];
              hoisted_3_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_28_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_22_1[i_3], deduped_1_2 );
                    end ) );
              hoisted_2_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_22_1[i_3], deduped_1_2 );
                    end ) );
              return List( deduped_25_1, function ( i_3 )
                        local deduped_1_3;
                        deduped_1_3 := deduped_21_1[i_3];
                        return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                    if deduped_1_3 > 0 and deduped_22_1[i_3] = 0 then
                                        return ListWithIdenticalEntries( deduped_1_3, deduped_30_1 );
                                    else
                                        return deduped_8_1[i_3];
                                    fi;
                                    return;
                                end )(  ), function ( row_4 )
                                return Concatenation( hoisted_2_2, List( row_4, Source ), hoisted_3_2 );
                            end );
                    end )[m_i_2];
          end ) );
    hoisted_17_1 := List( [ 1 .. Sum( deduped_21_1 ) ], function ( i_2 )
            local hoisted_1_2, hoisted_2_2, hoisted_3_2;
            hoisted_3_2 := hoisted_14_1[i_2];
            hoisted_2_2 := hoisted_12_1[i_2];
            hoisted_1_2 := hoisted_11_1[i_2];
            return List( hoisted_16_1, function ( j_3 )
                    return CreateCapCategoryMorphismWithAttributes( deduped_24_1, hoisted_1_2[j_3], hoisted_2_2[j_3], Coefficient, hoisted_3_2[j_3] * hoisted_15_1 );
                end );
        end );
    deduped_2_1 := List( [ 0 .. Length( deduped_21_1 ) ], function ( i_2 )
            return Sum( deduped_21_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_26_1, deduped_27_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_21_1, List( deduped_25_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_18_1[obj_idx_2] + 1 .. deduped_18_1[deduped_2_2] ];
                  return List( [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_17_1[nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_22_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2, deduped_3_2;
              deduped_3_2 := pair_2[2];
              deduped_2_2 := deduped_22_1[deduped_3_2];
              deduped_1_2 := deduped_21_1[deduped_3_2];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_19_1, CreateCapCategoryObjectWithAttributes( deduped_19_1, RankOfObject, deduped_1_2 ), CreateCapCategoryObjectWithAttributes( deduped_19_1, RankOfObject, deduped_2_2 ), UnderlyingMatrix, HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                            return List( row_3, Coefficient );
                        end ), deduped_1_2, deduped_2_2, deduped_29_1 ) ), deduped_3_2 );
          end ) );
end
########
        
    ;
    
    ##
    AddCokernelObject( cat,
        
########
function ( cat_1, alpha_1 )
    local hoisted_1_1;
    hoisted_1_1 := UnderlyingCategoryOfRows( cat_1 );
    return CreateCapCategoryObjectWithAttributes( cat_1, ListOfPairsOfObjectAndIndex, Filtered( List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
                local deduped_1_2;
                deduped_1_2 := pair_2[1];
                return NTuple( 2, CreateCapCategoryObjectWithAttributes( hoisted_1_1, RankOfObject, RankOfObject( Range( deduped_1_2 ) ) - RowRankOfMatrix( UnderlyingMatrix( deduped_1_2 ) ) ), pair_2[2] );
            end ), function ( pair_2 )
              return not RankOfObject( pair_2[1] ) = 0;
          end ) );
end
########
        
    , 100 );
    
    ##
    AddCokernelProjectionWithGivenCokernelObject( cat,
        
########
function ( cat_1, alpha_1, P_1 )
    local deduped_1_1;
    deduped_1_1 := UnderlyingCategoryOfRows( cat_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, Target( alpha_1 ), P_1, ListOfPairsOfMorphismAndIndex, Filtered( List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
                local deduped_1_2, deduped_2_2;
                deduped_2_2 := pair_2[1];
                deduped_1_2 := SyzygiesOfColumns( UnderlyingMatrix( deduped_2_2 ) );
                return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_1_1, Range( deduped_2_2 ), CreateCapCategoryObjectWithAttributes( deduped_1_1, RankOfObject, NumberColumns( deduped_1_2 ) ), UnderlyingMatrix, deduped_1_2 ), pair_2[2] );
            end ), function ( pair_2 )
              local deduped_1_2;
              deduped_1_2 := pair_2[1];
              return not RankOfObject( Source( deduped_1_2 ) ) = 0 or not RankOfObject( Target( deduped_1_2 ) ) = 0;
          end ) );
end
########
        
    , 100 );
    
    ##
    AddColift( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    local hoisted_1_1, deduped_3_1, hoisted_4_1, hoisted_6_1, deduped_7_1, hoisted_8_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1;
    deduped_14_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_13_1 := Target( beta_1 );
    deduped_12_1 := Target( alpha_1 );
    deduped_11_1 := ListOfPairsOfObjectAndIndex( deduped_13_1 );
    deduped_10_1 := ListOfPairsOfObjectAndIndex( deduped_12_1 );
    hoisted_8_1 := ListOfPairsOfObjectAndIndex( Source( beta_1 ) );
    deduped_7_1 := UnderlyingRing( cat_1 );
    hoisted_6_1 := ListOfPairsOfObjectAndIndex( Source( alpha_1 ) );
    hoisted_4_1 := ListOfPairsOfMorphismAndIndex( beta_1 );
    deduped_3_1 := CreateCapCategoryObjectWithAttributes( deduped_14_1, RankOfObject, 0 );
    hoisted_1_1 := ListOfPairsOfMorphismAndIndex( alpha_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_12_1, deduped_13_1, ListOfPairsOfMorphismAndIndex, List( Union2( List( deduped_10_1, function ( elem_2 )
                  return elem_2[2];
              end ), List( deduped_11_1, function ( elem_2 )
                  return elem_2[2];
              end ) ), function ( index_2 )
              local deduped_1_2, deduped_2_2, deduped_3_2, deduped_4_2, deduped_5_2, deduped_6_2, deduped_7_2, deduped_8_2, deduped_9_2, deduped_10_2, deduped_11_2, deduped_12_2, deduped_13_2, deduped_14_2;
              deduped_14_2 := Filtered( hoisted_8_1, function ( pair_3 )
                      return pair_3[2] = index_2;
                  end );
              deduped_13_2 := Filtered( hoisted_6_1, function ( pair_3 )
                      return pair_3[2] = index_2;
                  end );
              deduped_12_2 := Filtered( deduped_11_1, function ( pair_3 )
                      return pair_3[2] = index_2;
                  end );
              deduped_11_2 := Filtered( hoisted_4_1, function ( pair_3 )
                      return pair_3[2] = index_2;
                  end );
              deduped_10_2 := Filtered( deduped_10_1, function ( pair_3 )
                      return pair_3[2] = index_2;
                  end );
              deduped_9_2 := Filtered( hoisted_1_1, function ( pair_3 )
                      return pair_3[2] = index_2;
                  end );
              deduped_8_2 := Length( deduped_12_2 ) = 0;
              deduped_7_2 := Length( deduped_11_2 ) = 0;
              deduped_6_2 := Length( deduped_10_2 ) = 0;
              deduped_5_2 := Length( deduped_9_2 ) = 0;
              deduped_4_2 := deduped_11_2[1][1];
              deduped_3_2 := deduped_12_2[1][1];
              deduped_2_2 := deduped_9_2[1][1];
              deduped_1_2 := deduped_10_2[1][1];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_14_1, CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_5_2 then
                                return CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                          if deduped_6_2 then
                                              return deduped_3_1;
                                          else
                                              return deduped_1_2;
                                          fi;
                                          return;
                                      end )(  );
                            else
                                return Range( deduped_2_2 );
                            fi;
                            return;
                        end )(  ), CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_7_2 then
                                return CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                          if deduped_8_2 then
                                              return deduped_3_1;
                                          else
                                              return deduped_3_2;
                                          fi;
                                          return;
                                      end )(  );
                            else
                                return Range( deduped_4_2 );
                            fi;
                            return;
                        end )(  ), UnderlyingMatrix, SafeLeftDivide( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                              if deduped_5_2 then
                                  return HomalgZeroMatrix( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                              if Length( deduped_13_2 ) = 0 then
                                                  return 0;
                                              else
                                                  return RankOfObject( deduped_13_2[1][1] );
                                              fi;
                                              return;
                                          end )(  ), CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                              if deduped_6_2 then
                                                  return 0;
                                              else
                                                  return RankOfObject( deduped_1_2 );
                                              fi;
                                              return;
                                          end )(  ), deduped_7_1 );
                              else
                                  return UnderlyingMatrix( deduped_2_2 );
                              fi;
                              return;
                          end )(  ), CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                              if deduped_7_2 then
                                  return HomalgZeroMatrix( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                              if Length( deduped_14_2 ) = 0 then
                                                  return 0;
                                              else
                                                  return RankOfObject( deduped_14_2[1][1] );
                                              fi;
                                              return;
                                          end )(  ), CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                              if deduped_8_2 then
                                                  return 0;
                                              else
                                                  return RankOfObject( deduped_3_2 );
                                              fi;
                                              return;
                                          end )(  ), deduped_7_1 );
                              else
                                  return UnderlyingMatrix( deduped_4_2 );
                              fi;
                              return;
                          end )(  ) ) ), index_2 );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddComponentOfMorphismFromDirectSum( cat,
        
########
function ( cat_1, alpha_1, S_1, i_1 )
    local deduped_2_1, hoisted_3_1, hoisted_6_1, deduped_8_1, hoisted_9_1, deduped_10_1, hoisted_13_1, hoisted_14_1, deduped_15_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1;
    deduped_28_1 := [  ];
    deduped_27_1 := UnderlyingRing( cat_1 );
    deduped_26_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_25_1 := Range( alpha_1 );
    deduped_24_1 := S_1[i_1];
    deduped_23_1 := [ 1 .. deduped_26_1 ];
    deduped_22_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
    deduped_21_1 := ListWithIdenticalEntries( deduped_26_1, 0 );
    deduped_20_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_25_1 ), deduped_21_1 );
    deduped_19_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( CAP_JIT_INCOMPLETE_LOGIC( deduped_24_1 ) ), deduped_21_1 );
    deduped_18_1 := CAP_JIT_INCOMPLETE_LOGIC( NTuple( 2, Sum( deduped_19_1 ), deduped_19_1 ) )[2];
    deduped_17_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_15_1 := List( [ 0 .. Length( deduped_20_1 ) ], function ( i_2 )
            return Sum( deduped_20_1{[ 1 .. i_2 ]} );
        end );
    deduped_10_1 := ZeroImmutable( deduped_27_1 );
    hoisted_6_1 := UnderlyingCategory( deduped_22_1 );
    deduped_8_1 := List( deduped_23_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_22_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_6_1, IndexOfObject, i_2 ) );
        end );
    hoisted_9_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := deduped_8_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_22_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), ListWithIdenticalEntries( deduped_26_1, deduped_28_1 ) );
    hoisted_3_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( alpha_1 ) ), deduped_21_1 );
    hoisted_14_1 := Concatenation( List( deduped_23_1, function ( m_i_2 )
              local deduped_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
              deduped_4_2 := hoisted_3_1[deduped_5_2];
              deduped_1_2 := deduped_8_1[m_i_2];
              hoisted_3_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_26_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_20_1[i_3], CreateCapCategoryMorphismWithAttributes( deduped_22_1, deduped_1_2, deduped_8_1[i_3], Coefficient, deduped_10_1 ) );
                    end ) );
              hoisted_2_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_20_1[i_3], CreateCapCategoryMorphismWithAttributes( deduped_22_1, deduped_1_2, deduped_8_1[i_3], Coefficient, deduped_10_1 ) );
                    end ) );
              return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_4_2 > 0 and deduped_20_1[deduped_5_2] = 0 then
                                return ListWithIdenticalEntries( deduped_4_2, deduped_28_1 );
                            else
                                return hoisted_9_1[deduped_5_2];
                            fi;
                            return;
                        end )(  ), function ( row_3 )
                        return Concatenation( hoisted_2_2, row_3, hoisted_3_2 );
                    end ) );
          end ) );
    hoisted_13_1 := Sum( List( S_1, function ( x_2 )
                return Sum( COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( x_2 ), deduped_21_1 ) );
            end ){[ 1 .. i_1 - 1 ]} );
    deduped_2_1 := List( [ 0 .. Length( deduped_18_1 ) ], function ( i_2 )
            return Sum( deduped_18_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_24_1, deduped_25_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_18_1, List( deduped_23_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_15_1[obj_idx_2] + 1 .. deduped_15_1[deduped_2_2] ];
                  return List( [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_14_1[hoisted_13_1 + nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_20_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                        return List( row_3, Coefficient );
                    end ), deduped_18_1[deduped_2_2], deduped_20_1[deduped_2_2], deduped_27_1 );
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_17_1, CreateCapCategoryObjectWithAttributes( deduped_17_1, RankOfObject, NumberRows( deduped_1_2 ) ), CreateCapCategoryObjectWithAttributes( deduped_17_1, RankOfObject, NumberColumns( deduped_1_2 ) ), UnderlyingMatrix, deduped_1_2 ), deduped_2_2 );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.ComponentOfMorphismFromDirectSum :=
        
########
function ( cat_1, alpha_1, S_1, i_1 )
    local deduped_3_1, hoisted_4_1, hoisted_7_1, deduped_9_1, hoisted_10_1, deduped_11_1, hoisted_14_1, hoisted_15_1, deduped_16_1, deduped_17_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1;
    deduped_27_1 := [  ];
    deduped_26_1 := UnderlyingRing( cat_1 );
    deduped_25_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_24_1 := Range( alpha_1 );
    deduped_23_1 := [ 1 .. deduped_25_1 ];
    deduped_22_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
    deduped_21_1 := ListWithIdenticalEntries( deduped_25_1, 0 );
    deduped_20_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_24_1 ), deduped_21_1 );
    deduped_19_1 := List( S_1, function ( x_2 )
                local deduped_1_2;
                deduped_1_2 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( x_2 ), deduped_21_1 );
                return NTuple( 2, Sum( deduped_1_2 ), deduped_1_2 );
            end )[i_1][2];
    deduped_17_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_16_1 := List( [ 0 .. Length( deduped_20_1 ) ], function ( i_2 )
            return Sum( deduped_20_1{[ 1 .. i_2 ]} );
        end );
    deduped_11_1 := ZeroImmutable( deduped_26_1 );
    hoisted_7_1 := UnderlyingCategory( deduped_22_1 );
    deduped_9_1 := List( deduped_23_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_22_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_7_1, IndexOfObject, i_2 ) );
        end );
    hoisted_10_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := deduped_9_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_22_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), ListWithIdenticalEntries( deduped_25_1, deduped_27_1 ) );
    hoisted_4_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( alpha_1 ) ), deduped_21_1 );
    hoisted_15_1 := Concatenation( List( deduped_23_1, function ( m_i_2 )
              local deduped_1_2, hoisted_2_2, hoisted_3_2;
              deduped_1_2 := deduped_9_1[m_i_2];
              hoisted_3_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_25_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_20_1[i_3], CreateCapCategoryMorphismWithAttributes( deduped_22_1, deduped_1_2, deduped_9_1[i_3], Coefficient, deduped_11_1 ) );
                    end ) );
              hoisted_2_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_20_1[i_3], CreateCapCategoryMorphismWithAttributes( deduped_22_1, deduped_1_2, deduped_9_1[i_3], Coefficient, deduped_11_1 ) );
                    end ) );
              return List( deduped_23_1, function ( i_3 )
                        local deduped_1_3;
                        deduped_1_3 := hoisted_4_1[i_3];
                        return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                    if deduped_1_3 > 0 and deduped_20_1[i_3] = 0 then
                                        return ListWithIdenticalEntries( deduped_1_3, deduped_27_1 );
                                    else
                                        return hoisted_10_1[i_3];
                                    fi;
                                    return;
                                end )(  ), function ( row_4 )
                                return Concatenation( hoisted_2_2, row_4, hoisted_3_2 );
                            end );
                    end )[m_i_2];
          end ) );
    hoisted_14_1 := Sum( List( S_1, function ( x_2 )
                return Sum( COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( x_2 ), deduped_21_1 ) );
            end ){[ 1 .. i_1 - 1 ]} );
    deduped_3_1 := List( [ 0 .. Length( deduped_19_1 ) ], function ( i_2 )
            return Sum( deduped_19_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, S_1[i_1], deduped_24_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_19_1, List( deduped_23_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_16_1[obj_idx_2] + 1 .. deduped_16_1[deduped_2_2] ];
                  return List( [ deduped_3_1[obj_idx_2] + 1 .. deduped_3_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_15_1[hoisted_14_1 + nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_20_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2, deduped_3_2;
              deduped_3_2 := pair_2[2];
              deduped_2_2 := deduped_20_1[deduped_3_2];
              deduped_1_2 := deduped_19_1[deduped_3_2];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_17_1, CreateCapCategoryObjectWithAttributes( deduped_17_1, RankOfObject, deduped_1_2 ), CreateCapCategoryObjectWithAttributes( deduped_17_1, RankOfObject, deduped_2_2 ), UnderlyingMatrix, HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                            return List( row_3, Coefficient );
                        end ), deduped_1_2, deduped_2_2, deduped_26_1 ) ), deduped_3_2 );
          end ) );
end
########
        
    ;
    
    ##
    AddComponentOfMorphismIntoDirectSum( cat,
        
########
function ( cat_1, alpha_1, S_1, i_1 )
    local deduped_2_1, deduped_3_1, hoisted_5_1, deduped_7_1, hoisted_8_1, deduped_9_1, hoisted_12_1, hoisted_13_1, deduped_15_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1, deduped_30_1;
    deduped_30_1 := [  ];
    deduped_29_1 := UnderlyingRing( cat_1 );
    deduped_28_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_27_1 := S_1[i_1];
    deduped_26_1 := Source( alpha_1 );
    deduped_25_1 := [ 1 .. deduped_28_1 ];
    deduped_24_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
    deduped_23_1 := ListWithIdenticalEntries( deduped_28_1, 0 );
    deduped_22_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_26_1 ), deduped_23_1 );
    deduped_21_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( CAP_JIT_INCOMPLETE_LOGIC( deduped_27_1 ) ), deduped_23_1 );
    deduped_20_1 := List( S_1, function ( x_2 )
            return Sum( COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( x_2 ), deduped_23_1 ) );
        end );
    deduped_19_1 := Sum( deduped_20_1{[ 1 .. i_1 - 1 ]} );
    deduped_18_1 := CAP_JIT_INCOMPLETE_LOGIC( NTuple( 2, Sum( deduped_21_1 ), deduped_21_1 ) )[2];
    deduped_17_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_15_1 := List( [ 0 .. Length( deduped_18_1 ) ], function ( i_2 )
            return Sum( deduped_18_1{[ 1 .. i_2 ]} );
        end );
    hoisted_12_1 := [ deduped_19_1 + 1 .. deduped_19_1 + deduped_20_1[i_1] ];
    deduped_9_1 := ZeroImmutable( deduped_29_1 );
    hoisted_5_1 := UnderlyingCategory( deduped_24_1 );
    deduped_7_1 := List( deduped_25_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_24_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_5_1, IndexOfObject, i_2 ) );
        end );
    hoisted_8_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := deduped_7_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_24_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), ListWithIdenticalEntries( deduped_28_1, deduped_30_1 ) );
    deduped_3_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( alpha_1 ) ), deduped_23_1 );
    hoisted_13_1 := Concatenation( List( deduped_25_1, function ( m_i_2 )
              local deduped_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
              deduped_4_2 := deduped_22_1[deduped_5_2];
              deduped_1_2 := deduped_7_1[m_i_2];
              hoisted_3_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_28_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_3_1[i_3], CreateCapCategoryMorphismWithAttributes( deduped_24_1, deduped_1_2, deduped_7_1[i_3], Coefficient, deduped_9_1 ) );
                    end ) );
              hoisted_2_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_3_1[i_3], CreateCapCategoryMorphismWithAttributes( deduped_24_1, deduped_1_2, deduped_7_1[i_3], Coefficient, deduped_9_1 ) );
                    end ) );
              return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_4_2 > 0 and deduped_3_1[deduped_5_2] = 0 then
                                return ListWithIdenticalEntries( deduped_4_2, deduped_30_1 );
                            else
                                return hoisted_8_1[deduped_5_2];
                            fi;
                            return;
                        end )(  ), function ( row_3 )
                        return Concatenation( hoisted_2_2, row_3, hoisted_3_2 ){hoisted_12_1};
                    end ) );
          end ) );
    deduped_2_1 := List( [ 0 .. Length( deduped_22_1 ) ], function ( i_2 )
            return Sum( deduped_22_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_26_1, deduped_27_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_22_1, List( deduped_25_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_15_1[obj_idx_2] + 1 .. deduped_15_1[deduped_2_2] ];
                  return List( [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_13_1[nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_18_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                        return List( row_3, Coefficient );
                    end ), deduped_22_1[deduped_2_2], deduped_18_1[deduped_2_2], deduped_29_1 );
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_17_1, CreateCapCategoryObjectWithAttributes( deduped_17_1, RankOfObject, NumberRows( deduped_1_2 ) ), CreateCapCategoryObjectWithAttributes( deduped_17_1, RankOfObject, NumberColumns( deduped_1_2 ) ), UnderlyingMatrix, deduped_1_2 ), deduped_2_2 );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.ComponentOfMorphismIntoDirectSum :=
        
########
function ( cat_1, alpha_1, S_1, i_1 )
    local deduped_2_1, deduped_3_1, hoisted_5_1, deduped_7_1, hoisted_8_1, deduped_9_1, hoisted_12_1, hoisted_14_1, deduped_16_1, deduped_17_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1;
    deduped_29_1 := [  ];
    deduped_28_1 := UnderlyingRing( cat_1 );
    deduped_27_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_26_1 := Source( alpha_1 );
    deduped_25_1 := [ 1 .. deduped_27_1 ];
    deduped_24_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
    deduped_23_1 := ListWithIdenticalEntries( deduped_27_1, 0 );
    deduped_22_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_26_1 ), deduped_23_1 );
    deduped_21_1 := List( S_1, function ( x_2 )
            return Sum( COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( x_2 ), deduped_23_1 ) );
        end );
    deduped_20_1 := Sum( deduped_21_1{[ 1 .. i_1 - 1 ]} );
    deduped_19_1 := List( S_1, function ( x_2 )
                local deduped_1_2;
                deduped_1_2 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( x_2 ), deduped_23_1 );
                return NTuple( 2, Sum( deduped_1_2 ), deduped_1_2 );
            end )[i_1][2];
    deduped_17_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_16_1 := List( [ 0 .. Length( deduped_19_1 ) ], function ( i_2 )
            return Sum( deduped_19_1{[ 1 .. i_2 ]} );
        end );
    hoisted_12_1 := [ deduped_20_1 + 1 .. deduped_20_1 + deduped_21_1[i_1] ];
    deduped_9_1 := ZeroImmutable( deduped_28_1 );
    hoisted_5_1 := UnderlyingCategory( deduped_24_1 );
    deduped_7_1 := List( deduped_25_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_24_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_5_1, IndexOfObject, i_2 ) );
        end );
    hoisted_8_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := deduped_7_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_24_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), ListWithIdenticalEntries( deduped_27_1, deduped_29_1 ) );
    deduped_3_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( alpha_1 ) ), deduped_23_1 );
    hoisted_14_1 := Concatenation( List( deduped_25_1, function ( m_i_2 )
              local deduped_1_2, hoisted_2_2, hoisted_3_2;
              deduped_1_2 := deduped_7_1[m_i_2];
              hoisted_3_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_27_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_3_1[i_3], CreateCapCategoryMorphismWithAttributes( deduped_24_1, deduped_1_2, deduped_7_1[i_3], Coefficient, deduped_9_1 ) );
                    end ) );
              hoisted_2_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_3_1[i_3], CreateCapCategoryMorphismWithAttributes( deduped_24_1, deduped_1_2, deduped_7_1[i_3], Coefficient, deduped_9_1 ) );
                    end ) );
              return List( deduped_25_1, function ( i_3 )
                        local deduped_1_3;
                        deduped_1_3 := deduped_22_1[i_3];
                        return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                    if deduped_1_3 > 0 and deduped_3_1[i_3] = 0 then
                                        return ListWithIdenticalEntries( deduped_1_3, deduped_29_1 );
                                    else
                                        return hoisted_8_1[i_3];
                                    fi;
                                    return;
                                end )(  ), function ( row_4 )
                                return Concatenation( hoisted_2_2, row_4, hoisted_3_2 ){hoisted_12_1};
                            end );
                    end )[m_i_2];
          end ) );
    deduped_2_1 := List( [ 0 .. Length( deduped_22_1 ) ], function ( i_2 )
            return Sum( deduped_22_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_26_1, S_1[i_1], ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_22_1, List( deduped_25_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_16_1[obj_idx_2] + 1 .. deduped_16_1[deduped_2_2] ];
                  return List( [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_14_1[nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_19_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2, deduped_3_2;
              deduped_3_2 := pair_2[2];
              deduped_2_2 := deduped_19_1[deduped_3_2];
              deduped_1_2 := deduped_22_1[deduped_3_2];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_17_1, CreateCapCategoryObjectWithAttributes( deduped_17_1, RankOfObject, deduped_1_2 ), CreateCapCategoryObjectWithAttributes( deduped_17_1, RankOfObject, deduped_2_2 ), UnderlyingMatrix, HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                            return List( row_3, Coefficient );
                        end ), deduped_1_2, deduped_2_2, deduped_28_1 ) ), deduped_3_2 );
          end ) );
end
########
        
    ;
    
    ##
    AddDirectSum( cat,
        
########
function ( cat_1, objects_1 )
    local hoisted_1_1;
    hoisted_1_1 := ListWithIdenticalEntries( NrOfSummandsOfCoproduct( cat_1 ), 0 );
    return CreateCapCategoryObjectWithAttributes( cat_1, ListOfPairsOfObjectAndIndex, COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseObjectListToSparseList( cat_1, Sum( List( objects_1, function ( x_2 )
                    local deduped_1_2;
                    deduped_1_2 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( x_2 ), hoisted_1_1 );
                    return NTuple( 2, Sum( deduped_1_2 ), deduped_1_2 );
                end ) )[2] ) );
end
########
        
    , 100 );
    
    ##
    AddIdentityMorphism( cat,
        
########
function ( cat_1, a_1 )
    local deduped_2_1, hoisted_3_1, deduped_4_1, deduped_5_1, hoisted_6_1, hoisted_7_1, hoisted_9_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1;
    deduped_17_1 := UnderlyingRing( cat_1 );
    deduped_16_1 := ModelingCategory( cat_1 );
    deduped_15_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_14_1 := [ 1 .. deduped_15_1 ];
    deduped_13_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( a_1 ), ListWithIdenticalEntries( deduped_15_1, 0 ) );
    deduped_12_1 := [ 1 .. Sum( deduped_13_1 ) ];
    deduped_11_1 := UnderlyingCategoryOfRows( cat_1 );
    hoisted_7_1 := ZeroImmutable( deduped_17_1 );
    hoisted_6_1 := OneImmutable( deduped_17_1 );
    deduped_5_1 := UnderlyingCategory( deduped_16_1 );
    hoisted_3_1 := ListOfObjectsOfUnderlyingCategory( ModelingCategory( deduped_16_1 ) );
    deduped_4_1 := Concatenation( List( deduped_14_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_13_1[i_2], hoisted_3_1[i_2] );
          end ) );
    hoisted_9_1 := List( deduped_12_1, function ( i_2 )
            local hoisted_1_2, deduped_3_2;
            deduped_3_2 := deduped_4_1[i_2];
            hoisted_1_2 := CreateCapCategoryMorphismWithAttributes( deduped_5_1, deduped_3_2, deduped_3_2, Coefficient, hoisted_6_1 );
            return List( deduped_12_1, function ( j_3 )
                    if i_2 = j_3 then
                        return hoisted_1_2;
                    else
                        return CreateCapCategoryMorphismWithAttributes( deduped_5_1, deduped_3_2, deduped_4_1[j_3], Coefficient, hoisted_7_1 );
                    fi;
                    return;
                end );
        end );
    deduped_2_1 := List( [ 0 .. Length( deduped_13_1 ) ], function ( i_2 )
            return Sum( deduped_13_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, a_1, a_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_13_1, List( deduped_14_1, function ( obj_idx_2 )
                  local deduped_2_2;
                  deduped_2_2 := [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[obj_idx_2 + 1] ];
                  return List( deduped_2_2, function ( nr_rows_3 )
                          return hoisted_9_1[nr_rows_3]{deduped_2_2};
                      end );
              end ), deduped_13_1 ), function ( pair_2 )
              local morphism_attr_1_2, deduped_2_2, deduped_3_2;
              deduped_3_2 := pair_2[2];
              deduped_2_2 := deduped_13_1[deduped_3_2];
              morphism_attr_1_2 := HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                        return List( row_3, Coefficient );
                    end ), deduped_2_2, deduped_2_2, deduped_17_1 );
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_11_1, CreateCapCategoryObjectWithAttributes( deduped_11_1, RankOfObject, NumberRows( morphism_attr_1_2 ) ), CreateCapCategoryObjectWithAttributes( deduped_11_1, RankOfObject, NumberColumns( morphism_attr_1_2 ) ), UnderlyingMatrix, morphism_attr_1_2 ), deduped_3_2 );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.IdentityMorphism :=
        
########
function ( cat_1, a_1 )
    local deduped_2_1, hoisted_3_1, deduped_4_1, deduped_5_1, hoisted_6_1, hoisted_7_1, hoisted_9_1, deduped_10_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1;
    deduped_17_1 := UnderlyingRing( cat_1 );
    deduped_16_1 := ModelingCategory( cat_1 );
    deduped_15_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_14_1 := [ 1 .. deduped_15_1 ];
    deduped_13_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( a_1 ), ListWithIdenticalEntries( deduped_15_1, 0 ) );
    deduped_12_1 := [ 1 .. Sum( deduped_13_1 ) ];
    deduped_10_1 := UnderlyingCategoryOfRows( cat_1 );
    hoisted_7_1 := ZeroImmutable( deduped_17_1 );
    hoisted_6_1 := OneImmutable( deduped_17_1 );
    deduped_5_1 := UnderlyingCategory( deduped_16_1 );
    hoisted_3_1 := ListOfObjectsOfUnderlyingCategory( ModelingCategory( deduped_16_1 ) );
    deduped_4_1 := Concatenation( List( deduped_14_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_13_1[i_2], hoisted_3_1[i_2] );
          end ) );
    hoisted_9_1 := List( deduped_12_1, function ( i_2 )
            local hoisted_1_2, deduped_3_2;
            deduped_3_2 := deduped_4_1[i_2];
            hoisted_1_2 := CreateCapCategoryMorphismWithAttributes( deduped_5_1, deduped_3_2, deduped_3_2, Coefficient, hoisted_6_1 );
            return List( deduped_12_1, function ( j_3 )
                    if i_2 = j_3 then
                        return hoisted_1_2;
                    else
                        return CreateCapCategoryMorphismWithAttributes( deduped_5_1, deduped_3_2, deduped_4_1[j_3], Coefficient, hoisted_7_1 );
                    fi;
                    return;
                end );
        end );
    deduped_2_1 := List( [ 0 .. Length( deduped_13_1 ) ], function ( i_2 )
            return Sum( deduped_13_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, a_1, a_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_13_1, List( deduped_14_1, function ( obj_idx_2 )
                  local deduped_2_2;
                  deduped_2_2 := [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[obj_idx_2 + 1] ];
                  return List( deduped_2_2, function ( nr_rows_3 )
                          return hoisted_9_1[nr_rows_3]{deduped_2_2};
                      end );
              end ), deduped_13_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2, deduped_3_2;
              deduped_3_2 := pair_2[2];
              deduped_2_2 := deduped_13_1[deduped_3_2];
              deduped_1_2 := CreateCapCategoryObjectWithAttributes( deduped_10_1, RankOfObject, deduped_2_2 );
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_10_1, deduped_1_2, deduped_1_2, UnderlyingMatrix, HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                            return List( row_3, Coefficient );
                        end ), deduped_2_2, deduped_2_2, deduped_17_1 ) ), deduped_3_2 );
          end ) );
end
########
        
    ;
    
    ##
    AddIsCongruentForMorphisms( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_4_1, deduped_6_1, deduped_7_1, hoisted_9_1, deduped_12_1, hoisted_13_1, hoisted_14_1, hoisted_15_1, deduped_16_1, hoisted_17_1, hoisted_18_1, hoisted_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1, deduped_30_1, deduped_31_1;
    deduped_30_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_26_1 := ListWithIdenticalEntries( deduped_30_1, 0 );
    deduped_25_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( arg3_1 ) ), deduped_26_1 );
    deduped_24_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( arg2_1 ) ), deduped_26_1 );
    deduped_23_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( arg3_1 ) ), deduped_26_1 );
    deduped_22_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( arg2_1 ) ), deduped_26_1 );
    deduped_21_1 := Sum( deduped_24_1 );
    deduped_20_1 := Sum( deduped_22_1 );
    if deduped_20_1 <> Sum( deduped_23_1 ) then
        return false;
    elif deduped_21_1 <> Sum( deduped_25_1 ) then
        return false;
    else
        deduped_31_1 := [  ];
        deduped_29_1 := [ 1 .. deduped_30_1 ];
        deduped_28_1 := ListWithIdenticalEntries( deduped_30_1, deduped_31_1 );
        deduped_27_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
        hoisted_19_1 := [ 1 .. deduped_21_1 ];
        deduped_16_1 := ZeroImmutable( UnderlyingRing( cat_1 ) );
        hoisted_4_1 := UnderlyingCategory( deduped_27_1 );
        deduped_6_1 := List( deduped_29_1, function ( i_2 )
                return CreateCapCategoryObjectWithAttributes( deduped_27_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_4_1, IndexOfObject, i_2 ) );
            end );
        deduped_12_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( arg3_1 ), function ( pair_2 )
                  local deduped_1_2, deduped_2_2;
                  deduped_2_2 := pair_2[2];
                  deduped_1_2 := deduped_6_1[deduped_2_2];
                  return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                            return List( row_3, function ( c_4 )
                                    return CreateCapCategoryMorphismWithAttributes( deduped_27_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                                end );
                        end ), deduped_2_2 );
              end ), deduped_28_1 );
        hoisted_18_1 := Concatenation( List( deduped_29_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
                  deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
                  deduped_3_2 := deduped_23_1[deduped_4_2];
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_30_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], deduped_16_1 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], deduped_16_1 );
                        end ) );
                  return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                if deduped_3_2 > 0 and deduped_25_1[deduped_4_2] = 0 then
                                    return ListWithIdenticalEntries( deduped_3_2, deduped_31_1 );
                                else
                                    return deduped_12_1[deduped_4_2];
                                fi;
                                return;
                            end )(  ), function ( row_3 )
                            return Concatenation( hoisted_1_2, List( row_3, Coefficient ), hoisted_2_2 );
                        end ) );
              end ) );
        deduped_7_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( arg2_1 ), function ( pair_2 )
                  local deduped_1_2, deduped_2_2;
                  deduped_2_2 := pair_2[2];
                  deduped_1_2 := deduped_6_1[deduped_2_2];
                  return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                            return List( row_3, function ( c_4 )
                                    return CreateCapCategoryMorphismWithAttributes( deduped_27_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                                end );
                        end ), deduped_2_2 );
              end ), deduped_28_1 );
        hoisted_17_1 := Concatenation( List( deduped_29_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
                  deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
                  deduped_3_2 := deduped_22_1[deduped_4_2];
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_30_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_24_1[i_3], deduped_16_1 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_24_1[i_3], deduped_16_1 );
                        end ) );
                  return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                if deduped_3_2 > 0 and deduped_24_1[deduped_4_2] = 0 then
                                    return ListWithIdenticalEntries( deduped_3_2, deduped_31_1 );
                                else
                                    return deduped_7_1[deduped_4_2];
                                fi;
                                return;
                            end )(  ), function ( row_3 )
                            return Concatenation( hoisted_1_2, List( row_3, Coefficient ), hoisted_2_2 );
                        end ) );
              end ) );
        hoisted_15_1 := Concatenation( List( deduped_29_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
                  deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
                  deduped_3_2 := deduped_23_1[deduped_4_2];
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_30_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], i_3 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], i_3 );
                        end ) );
                  return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                if deduped_3_2 > 0 and deduped_25_1[deduped_4_2] = 0 then
                                    return ListWithIdenticalEntries( deduped_3_2, deduped_31_1 );
                                else
                                    return deduped_12_1[deduped_4_2];
                                fi;
                                return;
                            end )(  ), function ( row_3 )
                            return Concatenation( hoisted_1_2, List( row_3, function ( logic_new_func_x_4 )
                                      return IndexOfObject( UnderlyingOriginalObject( Target( logic_new_func_x_4 ) ) );
                                  end ), hoisted_2_2 );
                        end ) );
              end ) );
        hoisted_14_1 := Concatenation( List( deduped_29_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
                  deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
                  deduped_3_2 := deduped_22_1[deduped_4_2];
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_30_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_24_1[i_3], i_3 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_24_1[i_3], i_3 );
                        end ) );
                  return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                if deduped_3_2 > 0 and deduped_24_1[deduped_4_2] = 0 then
                                    return ListWithIdenticalEntries( deduped_3_2, deduped_31_1 );
                                else
                                    return deduped_7_1[deduped_4_2];
                                fi;
                                return;
                            end )(  ), function ( row_3 )
                            return Concatenation( hoisted_1_2, List( row_3, function ( logic_new_func_x_4 )
                                      return IndexOfObject( UnderlyingOriginalObject( Target( logic_new_func_x_4 ) ) );
                                  end ), hoisted_2_2 );
                        end ) );
              end ) );
        hoisted_13_1 := Concatenation( List( deduped_29_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
                  deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
                  deduped_3_2 := deduped_23_1[deduped_4_2];
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_30_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], m_i_2 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], m_i_2 );
                        end ) );
                  return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                if deduped_3_2 > 0 and deduped_25_1[deduped_4_2] = 0 then
                                    return ListWithIdenticalEntries( deduped_3_2, deduped_31_1 );
                                else
                                    return deduped_12_1[deduped_4_2];
                                fi;
                                return;
                            end )(  ), function ( row_3 )
                            return Concatenation( hoisted_1_2, List( row_3, function ( logic_new_func_x_4 )
                                      return IndexOfObject( UnderlyingOriginalObject( Source( logic_new_func_x_4 ) ) );
                                  end ), hoisted_2_2 );
                        end ) );
              end ) );
        hoisted_9_1 := Concatenation( List( deduped_29_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
                  deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
                  deduped_3_2 := deduped_22_1[deduped_4_2];
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_30_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_24_1[i_3], m_i_2 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_24_1[i_3], m_i_2 );
                        end ) );
                  return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                if deduped_3_2 > 0 and deduped_24_1[deduped_4_2] = 0 then
                                    return ListWithIdenticalEntries( deduped_3_2, deduped_31_1 );
                                else
                                    return deduped_7_1[deduped_4_2];
                                fi;
                                return;
                            end )(  ), function ( row_3 )
                            return Concatenation( hoisted_1_2, List( row_3, function ( logic_new_func_x_4 )
                                      return IndexOfObject( UnderlyingOriginalObject( Source( logic_new_func_x_4 ) ) );
                                  end ), hoisted_2_2 );
                        end ) );
              end ) );
        return ForAll( [ 1 .. deduped_20_1 ], function ( i_2 )
                local hoisted_1_2, hoisted_2_2, hoisted_3_2, hoisted_4_2, hoisted_5_2, hoisted_6_2;
                hoisted_6_2 := hoisted_18_1[i_2];
                hoisted_5_2 := hoisted_17_1[i_2];
                hoisted_4_2 := hoisted_15_1[i_2];
                hoisted_3_2 := hoisted_14_1[i_2];
                hoisted_2_2 := hoisted_13_1[i_2];
                hoisted_1_2 := hoisted_9_1[i_2];
                return ForAll( hoisted_19_1, function ( j_3 )
                        return hoisted_1_2[j_3] = hoisted_2_2[j_3] and hoisted_3_2[j_3] = hoisted_4_2[j_3] and hoisted_5_2[j_3] = hoisted_6_2[j_3];
                    end );
            end );
    fi;
    return;
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.IsCongruentForMorphisms :=
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_4_1, deduped_6_1, deduped_7_1, hoisted_10_1, deduped_13_1, hoisted_14_1, hoisted_15_1, hoisted_16_1, deduped_17_1, hoisted_18_1, hoisted_19_1, hoisted_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1, deduped_30_1, deduped_31_1, deduped_32_1;
    deduped_31_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_27_1 := ListWithIdenticalEntries( deduped_31_1, 0 );
    deduped_26_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( arg3_1 ) ), deduped_27_1 );
    deduped_25_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( arg2_1 ) ), deduped_27_1 );
    deduped_24_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( arg3_1 ) ), deduped_27_1 );
    deduped_23_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( arg2_1 ) ), deduped_27_1 );
    deduped_22_1 := Sum( deduped_25_1 );
    deduped_21_1 := Sum( deduped_23_1 );
    if deduped_21_1 <> Sum( deduped_24_1 ) then
        return false;
    elif deduped_22_1 <> Sum( deduped_26_1 ) then
        return false;
    else
        deduped_32_1 := [  ];
        deduped_30_1 := [ 1 .. deduped_31_1 ];
        deduped_29_1 := ListWithIdenticalEntries( deduped_31_1, deduped_32_1 );
        deduped_28_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
        hoisted_20_1 := [ 1 .. deduped_22_1 ];
        deduped_17_1 := ZeroImmutable( UnderlyingRing( cat_1 ) );
        hoisted_4_1 := UnderlyingCategory( deduped_28_1 );
        deduped_6_1 := List( deduped_30_1, function ( i_2 )
                return CreateCapCategoryObjectWithAttributes( deduped_28_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_4_1, IndexOfObject, i_2 ) );
            end );
        deduped_13_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( arg3_1 ), function ( pair_2 )
                  local deduped_1_2, deduped_2_2;
                  deduped_2_2 := pair_2[2];
                  deduped_1_2 := deduped_6_1[deduped_2_2];
                  return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                            return List( row_3, function ( c_4 )
                                    return CreateCapCategoryMorphismWithAttributes( deduped_28_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                                end );
                        end ), deduped_2_2 );
              end ), deduped_29_1 );
        hoisted_19_1 := Concatenation( List( deduped_30_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2;
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_31_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_26_1[i_3], deduped_17_1 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_26_1[i_3], deduped_17_1 );
                        end ) );
                  return List( deduped_30_1, function ( i_3 )
                            local deduped_1_3;
                            deduped_1_3 := deduped_24_1[i_3];
                            return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                        if deduped_1_3 > 0 and deduped_26_1[i_3] = 0 then
                                            return ListWithIdenticalEntries( deduped_1_3, deduped_32_1 );
                                        else
                                            return deduped_13_1[i_3];
                                        fi;
                                        return;
                                    end )(  ), function ( row_4 )
                                    return Concatenation( hoisted_1_2, List( row_4, Coefficient ), hoisted_2_2 );
                                end );
                        end )[m_i_2];
              end ) );
        deduped_7_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( arg2_1 ), function ( pair_2 )
                  local deduped_1_2, deduped_2_2;
                  deduped_2_2 := pair_2[2];
                  deduped_1_2 := deduped_6_1[deduped_2_2];
                  return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                            return List( row_3, function ( c_4 )
                                    return CreateCapCategoryMorphismWithAttributes( deduped_28_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                                end );
                        end ), deduped_2_2 );
              end ), deduped_29_1 );
        hoisted_18_1 := Concatenation( List( deduped_30_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2;
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_31_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], deduped_17_1 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], deduped_17_1 );
                        end ) );
                  return List( deduped_30_1, function ( i_3 )
                            local deduped_1_3;
                            deduped_1_3 := deduped_23_1[i_3];
                            return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                        if deduped_1_3 > 0 and deduped_25_1[i_3] = 0 then
                                            return ListWithIdenticalEntries( deduped_1_3, deduped_32_1 );
                                        else
                                            return deduped_7_1[i_3];
                                        fi;
                                        return;
                                    end )(  ), function ( row_4 )
                                    return Concatenation( hoisted_1_2, List( row_4, Coefficient ), hoisted_2_2 );
                                end );
                        end )[m_i_2];
              end ) );
        hoisted_16_1 := Concatenation( List( deduped_30_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2;
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_31_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_26_1[i_3], i_3 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_26_1[i_3], i_3 );
                        end ) );
                  return List( deduped_30_1, function ( i_3 )
                            local deduped_1_3;
                            deduped_1_3 := deduped_24_1[i_3];
                            return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                        if deduped_1_3 > 0 and deduped_26_1[i_3] = 0 then
                                            return ListWithIdenticalEntries( deduped_1_3, deduped_32_1 );
                                        else
                                            return deduped_13_1[i_3];
                                        fi;
                                        return;
                                    end )(  ), function ( row_4 )
                                    return Concatenation( hoisted_1_2, List( row_4, function ( logic_new_func_x_5 )
                                              return IndexOfObject( UnderlyingOriginalObject( Target( logic_new_func_x_5 ) ) );
                                          end ), hoisted_2_2 );
                                end );
                        end )[m_i_2];
              end ) );
        hoisted_15_1 := Concatenation( List( deduped_30_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2;
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_31_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], i_3 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], i_3 );
                        end ) );
                  return List( deduped_30_1, function ( i_3 )
                            local deduped_1_3;
                            deduped_1_3 := deduped_23_1[i_3];
                            return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                        if deduped_1_3 > 0 and deduped_25_1[i_3] = 0 then
                                            return ListWithIdenticalEntries( deduped_1_3, deduped_32_1 );
                                        else
                                            return deduped_7_1[i_3];
                                        fi;
                                        return;
                                    end )(  ), function ( row_4 )
                                    return Concatenation( hoisted_1_2, List( row_4, function ( logic_new_func_x_5 )
                                              return IndexOfObject( UnderlyingOriginalObject( Target( logic_new_func_x_5 ) ) );
                                          end ), hoisted_2_2 );
                                end );
                        end )[m_i_2];
              end ) );
        hoisted_14_1 := Concatenation( List( deduped_30_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2;
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_31_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_26_1[i_3], m_i_2 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_26_1[i_3], m_i_2 );
                        end ) );
                  return List( deduped_30_1, function ( i_3 )
                            local deduped_1_3;
                            deduped_1_3 := deduped_24_1[i_3];
                            return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                        if deduped_1_3 > 0 and deduped_26_1[i_3] = 0 then
                                            return ListWithIdenticalEntries( deduped_1_3, deduped_32_1 );
                                        else
                                            return deduped_13_1[i_3];
                                        fi;
                                        return;
                                    end )(  ), function ( row_4 )
                                    return Concatenation( hoisted_1_2, List( row_4, function ( logic_new_func_x_5 )
                                              return IndexOfObject( UnderlyingOriginalObject( Source( logic_new_func_x_5 ) ) );
                                          end ), hoisted_2_2 );
                                end );
                        end )[m_i_2];
              end ) );
        hoisted_10_1 := Concatenation( List( deduped_30_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2;
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_31_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], m_i_2 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], m_i_2 );
                        end ) );
                  return List( deduped_30_1, function ( i_3 )
                            local deduped_1_3;
                            deduped_1_3 := deduped_23_1[i_3];
                            return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                        if deduped_1_3 > 0 and deduped_25_1[i_3] = 0 then
                                            return ListWithIdenticalEntries( deduped_1_3, deduped_32_1 );
                                        else
                                            return deduped_7_1[i_3];
                                        fi;
                                        return;
                                    end )(  ), function ( row_4 )
                                    return Concatenation( hoisted_1_2, List( row_4, function ( logic_new_func_x_5 )
                                              return IndexOfObject( UnderlyingOriginalObject( Source( logic_new_func_x_5 ) ) );
                                          end ), hoisted_2_2 );
                                end );
                        end )[m_i_2];
              end ) );
        return ForAll( [ 1 .. deduped_21_1 ], function ( i_2 )
                local hoisted_1_2, hoisted_2_2, hoisted_3_2, hoisted_4_2, hoisted_5_2, hoisted_6_2;
                hoisted_6_2 := hoisted_19_1[i_2];
                hoisted_5_2 := hoisted_18_1[i_2];
                hoisted_4_2 := hoisted_16_1[i_2];
                hoisted_3_2 := hoisted_15_1[i_2];
                hoisted_2_2 := hoisted_14_1[i_2];
                hoisted_1_2 := hoisted_10_1[i_2];
                return ForAll( hoisted_20_1, function ( j_3 )
                        return hoisted_1_2[j_3] = hoisted_2_2[j_3] and hoisted_3_2[j_3] = hoisted_4_2[j_3] and hoisted_5_2[j_3] = hoisted_6_2[j_3];
                    end );
            end );
    fi;
    return;
end
########
        
    ;
    
    ##
    AddIsEqualForMorphisms( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_4_1, deduped_6_1, deduped_7_1, hoisted_9_1, deduped_12_1, hoisted_13_1, hoisted_14_1, hoisted_15_1, deduped_16_1, hoisted_17_1, hoisted_18_1, hoisted_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1, deduped_30_1, deduped_31_1;
    deduped_30_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_26_1 := ListWithIdenticalEntries( deduped_30_1, 0 );
    deduped_25_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( arg3_1 ) ), deduped_26_1 );
    deduped_24_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( arg2_1 ) ), deduped_26_1 );
    deduped_23_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( arg3_1 ) ), deduped_26_1 );
    deduped_22_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( arg2_1 ) ), deduped_26_1 );
    deduped_21_1 := Sum( deduped_24_1 );
    deduped_20_1 := Sum( deduped_22_1 );
    if deduped_20_1 <> Sum( deduped_23_1 ) then
        return false;
    elif deduped_21_1 <> Sum( deduped_25_1 ) then
        return false;
    else
        deduped_31_1 := [  ];
        deduped_29_1 := [ 1 .. deduped_30_1 ];
        deduped_28_1 := ListWithIdenticalEntries( deduped_30_1, deduped_31_1 );
        deduped_27_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
        hoisted_19_1 := [ 1 .. deduped_21_1 ];
        deduped_16_1 := ZeroImmutable( UnderlyingRing( cat_1 ) );
        hoisted_4_1 := UnderlyingCategory( deduped_27_1 );
        deduped_6_1 := List( deduped_29_1, function ( i_2 )
                return CreateCapCategoryObjectWithAttributes( deduped_27_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_4_1, IndexOfObject, i_2 ) );
            end );
        deduped_12_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( arg3_1 ), function ( pair_2 )
                  local deduped_1_2, deduped_2_2;
                  deduped_2_2 := pair_2[2];
                  deduped_1_2 := deduped_6_1[deduped_2_2];
                  return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                            return List( row_3, function ( c_4 )
                                    return CreateCapCategoryMorphismWithAttributes( deduped_27_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                                end );
                        end ), deduped_2_2 );
              end ), deduped_28_1 );
        hoisted_18_1 := Concatenation( List( deduped_29_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
                  deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
                  deduped_3_2 := deduped_23_1[deduped_4_2];
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_30_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], deduped_16_1 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], deduped_16_1 );
                        end ) );
                  return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                if deduped_3_2 > 0 and deduped_25_1[deduped_4_2] = 0 then
                                    return ListWithIdenticalEntries( deduped_3_2, deduped_31_1 );
                                else
                                    return deduped_12_1[deduped_4_2];
                                fi;
                                return;
                            end )(  ), function ( row_3 )
                            return Concatenation( hoisted_1_2, List( row_3, Coefficient ), hoisted_2_2 );
                        end ) );
              end ) );
        deduped_7_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( arg2_1 ), function ( pair_2 )
                  local deduped_1_2, deduped_2_2;
                  deduped_2_2 := pair_2[2];
                  deduped_1_2 := deduped_6_1[deduped_2_2];
                  return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                            return List( row_3, function ( c_4 )
                                    return CreateCapCategoryMorphismWithAttributes( deduped_27_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                                end );
                        end ), deduped_2_2 );
              end ), deduped_28_1 );
        hoisted_17_1 := Concatenation( List( deduped_29_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
                  deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
                  deduped_3_2 := deduped_22_1[deduped_4_2];
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_30_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_24_1[i_3], deduped_16_1 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_24_1[i_3], deduped_16_1 );
                        end ) );
                  return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                if deduped_3_2 > 0 and deduped_24_1[deduped_4_2] = 0 then
                                    return ListWithIdenticalEntries( deduped_3_2, deduped_31_1 );
                                else
                                    return deduped_7_1[deduped_4_2];
                                fi;
                                return;
                            end )(  ), function ( row_3 )
                            return Concatenation( hoisted_1_2, List( row_3, Coefficient ), hoisted_2_2 );
                        end ) );
              end ) );
        hoisted_15_1 := Concatenation( List( deduped_29_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
                  deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
                  deduped_3_2 := deduped_23_1[deduped_4_2];
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_30_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], i_3 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], i_3 );
                        end ) );
                  return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                if deduped_3_2 > 0 and deduped_25_1[deduped_4_2] = 0 then
                                    return ListWithIdenticalEntries( deduped_3_2, deduped_31_1 );
                                else
                                    return deduped_12_1[deduped_4_2];
                                fi;
                                return;
                            end )(  ), function ( row_3 )
                            return Concatenation( hoisted_1_2, List( row_3, function ( logic_new_func_x_4 )
                                      return IndexOfObject( UnderlyingOriginalObject( Target( logic_new_func_x_4 ) ) );
                                  end ), hoisted_2_2 );
                        end ) );
              end ) );
        hoisted_14_1 := Concatenation( List( deduped_29_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
                  deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
                  deduped_3_2 := deduped_22_1[deduped_4_2];
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_30_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_24_1[i_3], i_3 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_24_1[i_3], i_3 );
                        end ) );
                  return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                if deduped_3_2 > 0 and deduped_24_1[deduped_4_2] = 0 then
                                    return ListWithIdenticalEntries( deduped_3_2, deduped_31_1 );
                                else
                                    return deduped_7_1[deduped_4_2];
                                fi;
                                return;
                            end )(  ), function ( row_3 )
                            return Concatenation( hoisted_1_2, List( row_3, function ( logic_new_func_x_4 )
                                      return IndexOfObject( UnderlyingOriginalObject( Target( logic_new_func_x_4 ) ) );
                                  end ), hoisted_2_2 );
                        end ) );
              end ) );
        hoisted_13_1 := Concatenation( List( deduped_29_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
                  deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
                  deduped_3_2 := deduped_23_1[deduped_4_2];
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_30_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], m_i_2 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], m_i_2 );
                        end ) );
                  return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                if deduped_3_2 > 0 and deduped_25_1[deduped_4_2] = 0 then
                                    return ListWithIdenticalEntries( deduped_3_2, deduped_31_1 );
                                else
                                    return deduped_12_1[deduped_4_2];
                                fi;
                                return;
                            end )(  ), function ( row_3 )
                            return Concatenation( hoisted_1_2, List( row_3, function ( logic_new_func_x_4 )
                                      return IndexOfObject( UnderlyingOriginalObject( Source( logic_new_func_x_4 ) ) );
                                  end ), hoisted_2_2 );
                        end ) );
              end ) );
        hoisted_9_1 := Concatenation( List( deduped_29_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
                  deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
                  deduped_3_2 := deduped_22_1[deduped_4_2];
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_30_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_24_1[i_3], m_i_2 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_24_1[i_3], m_i_2 );
                        end ) );
                  return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                if deduped_3_2 > 0 and deduped_24_1[deduped_4_2] = 0 then
                                    return ListWithIdenticalEntries( deduped_3_2, deduped_31_1 );
                                else
                                    return deduped_7_1[deduped_4_2];
                                fi;
                                return;
                            end )(  ), function ( row_3 )
                            return Concatenation( hoisted_1_2, List( row_3, function ( logic_new_func_x_4 )
                                      return IndexOfObject( UnderlyingOriginalObject( Source( logic_new_func_x_4 ) ) );
                                  end ), hoisted_2_2 );
                        end ) );
              end ) );
        return ForAll( [ 1 .. deduped_20_1 ], function ( i_2 )
                local hoisted_1_2, hoisted_2_2, hoisted_3_2, hoisted_4_2, hoisted_5_2, hoisted_6_2;
                hoisted_6_2 := hoisted_18_1[i_2];
                hoisted_5_2 := hoisted_17_1[i_2];
                hoisted_4_2 := hoisted_15_1[i_2];
                hoisted_3_2 := hoisted_14_1[i_2];
                hoisted_2_2 := hoisted_13_1[i_2];
                hoisted_1_2 := hoisted_9_1[i_2];
                return ForAll( hoisted_19_1, function ( j_3 )
                        return hoisted_1_2[j_3] = hoisted_2_2[j_3] and hoisted_3_2[j_3] = hoisted_4_2[j_3] and hoisted_5_2[j_3] = hoisted_6_2[j_3];
                    end );
            end );
    fi;
    return;
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.IsEqualForMorphisms :=
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_4_1, deduped_6_1, deduped_7_1, hoisted_10_1, deduped_13_1, hoisted_14_1, hoisted_15_1, hoisted_16_1, deduped_17_1, hoisted_18_1, hoisted_19_1, hoisted_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1, deduped_30_1, deduped_31_1, deduped_32_1;
    deduped_31_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_27_1 := ListWithIdenticalEntries( deduped_31_1, 0 );
    deduped_26_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( arg3_1 ) ), deduped_27_1 );
    deduped_25_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( arg2_1 ) ), deduped_27_1 );
    deduped_24_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( arg3_1 ) ), deduped_27_1 );
    deduped_23_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( arg2_1 ) ), deduped_27_1 );
    deduped_22_1 := Sum( deduped_25_1 );
    deduped_21_1 := Sum( deduped_23_1 );
    if deduped_21_1 <> Sum( deduped_24_1 ) then
        return false;
    elif deduped_22_1 <> Sum( deduped_26_1 ) then
        return false;
    else
        deduped_32_1 := [  ];
        deduped_30_1 := [ 1 .. deduped_31_1 ];
        deduped_29_1 := ListWithIdenticalEntries( deduped_31_1, deduped_32_1 );
        deduped_28_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
        hoisted_20_1 := [ 1 .. deduped_22_1 ];
        deduped_17_1 := ZeroImmutable( UnderlyingRing( cat_1 ) );
        hoisted_4_1 := UnderlyingCategory( deduped_28_1 );
        deduped_6_1 := List( deduped_30_1, function ( i_2 )
                return CreateCapCategoryObjectWithAttributes( deduped_28_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_4_1, IndexOfObject, i_2 ) );
            end );
        deduped_13_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( arg3_1 ), function ( pair_2 )
                  local deduped_1_2, deduped_2_2;
                  deduped_2_2 := pair_2[2];
                  deduped_1_2 := deduped_6_1[deduped_2_2];
                  return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                            return List( row_3, function ( c_4 )
                                    return CreateCapCategoryMorphismWithAttributes( deduped_28_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                                end );
                        end ), deduped_2_2 );
              end ), deduped_29_1 );
        hoisted_19_1 := Concatenation( List( deduped_30_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2;
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_31_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_26_1[i_3], deduped_17_1 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_26_1[i_3], deduped_17_1 );
                        end ) );
                  return List( deduped_30_1, function ( i_3 )
                            local deduped_1_3;
                            deduped_1_3 := deduped_24_1[i_3];
                            return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                        if deduped_1_3 > 0 and deduped_26_1[i_3] = 0 then
                                            return ListWithIdenticalEntries( deduped_1_3, deduped_32_1 );
                                        else
                                            return deduped_13_1[i_3];
                                        fi;
                                        return;
                                    end )(  ), function ( row_4 )
                                    return Concatenation( hoisted_1_2, List( row_4, Coefficient ), hoisted_2_2 );
                                end );
                        end )[m_i_2];
              end ) );
        deduped_7_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( arg2_1 ), function ( pair_2 )
                  local deduped_1_2, deduped_2_2;
                  deduped_2_2 := pair_2[2];
                  deduped_1_2 := deduped_6_1[deduped_2_2];
                  return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                            return List( row_3, function ( c_4 )
                                    return CreateCapCategoryMorphismWithAttributes( deduped_28_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                                end );
                        end ), deduped_2_2 );
              end ), deduped_29_1 );
        hoisted_18_1 := Concatenation( List( deduped_30_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2;
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_31_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], deduped_17_1 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], deduped_17_1 );
                        end ) );
                  return List( deduped_30_1, function ( i_3 )
                            local deduped_1_3;
                            deduped_1_3 := deduped_23_1[i_3];
                            return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                        if deduped_1_3 > 0 and deduped_25_1[i_3] = 0 then
                                            return ListWithIdenticalEntries( deduped_1_3, deduped_32_1 );
                                        else
                                            return deduped_7_1[i_3];
                                        fi;
                                        return;
                                    end )(  ), function ( row_4 )
                                    return Concatenation( hoisted_1_2, List( row_4, Coefficient ), hoisted_2_2 );
                                end );
                        end )[m_i_2];
              end ) );
        hoisted_16_1 := Concatenation( List( deduped_30_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2;
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_31_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_26_1[i_3], i_3 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_26_1[i_3], i_3 );
                        end ) );
                  return List( deduped_30_1, function ( i_3 )
                            local deduped_1_3;
                            deduped_1_3 := deduped_24_1[i_3];
                            return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                        if deduped_1_3 > 0 and deduped_26_1[i_3] = 0 then
                                            return ListWithIdenticalEntries( deduped_1_3, deduped_32_1 );
                                        else
                                            return deduped_13_1[i_3];
                                        fi;
                                        return;
                                    end )(  ), function ( row_4 )
                                    return Concatenation( hoisted_1_2, List( row_4, function ( logic_new_func_x_5 )
                                              return IndexOfObject( UnderlyingOriginalObject( Target( logic_new_func_x_5 ) ) );
                                          end ), hoisted_2_2 );
                                end );
                        end )[m_i_2];
              end ) );
        hoisted_15_1 := Concatenation( List( deduped_30_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2;
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_31_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], i_3 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], i_3 );
                        end ) );
                  return List( deduped_30_1, function ( i_3 )
                            local deduped_1_3;
                            deduped_1_3 := deduped_23_1[i_3];
                            return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                        if deduped_1_3 > 0 and deduped_25_1[i_3] = 0 then
                                            return ListWithIdenticalEntries( deduped_1_3, deduped_32_1 );
                                        else
                                            return deduped_7_1[i_3];
                                        fi;
                                        return;
                                    end )(  ), function ( row_4 )
                                    return Concatenation( hoisted_1_2, List( row_4, function ( logic_new_func_x_5 )
                                              return IndexOfObject( UnderlyingOriginalObject( Target( logic_new_func_x_5 ) ) );
                                          end ), hoisted_2_2 );
                                end );
                        end )[m_i_2];
              end ) );
        hoisted_14_1 := Concatenation( List( deduped_30_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2;
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_31_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_26_1[i_3], m_i_2 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_26_1[i_3], m_i_2 );
                        end ) );
                  return List( deduped_30_1, function ( i_3 )
                            local deduped_1_3;
                            deduped_1_3 := deduped_24_1[i_3];
                            return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                        if deduped_1_3 > 0 and deduped_26_1[i_3] = 0 then
                                            return ListWithIdenticalEntries( deduped_1_3, deduped_32_1 );
                                        else
                                            return deduped_13_1[i_3];
                                        fi;
                                        return;
                                    end )(  ), function ( row_4 )
                                    return Concatenation( hoisted_1_2, List( row_4, function ( logic_new_func_x_5 )
                                              return IndexOfObject( UnderlyingOriginalObject( Source( logic_new_func_x_5 ) ) );
                                          end ), hoisted_2_2 );
                                end );
                        end )[m_i_2];
              end ) );
        hoisted_10_1 := Concatenation( List( deduped_30_1, function ( m_i_2 )
                  local hoisted_1_2, hoisted_2_2;
                  hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_31_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], m_i_2 );
                        end ) );
                  hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_25_1[i_3], m_i_2 );
                        end ) );
                  return List( deduped_30_1, function ( i_3 )
                            local deduped_1_3;
                            deduped_1_3 := deduped_23_1[i_3];
                            return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                        if deduped_1_3 > 0 and deduped_25_1[i_3] = 0 then
                                            return ListWithIdenticalEntries( deduped_1_3, deduped_32_1 );
                                        else
                                            return deduped_7_1[i_3];
                                        fi;
                                        return;
                                    end )(  ), function ( row_4 )
                                    return Concatenation( hoisted_1_2, List( row_4, function ( logic_new_func_x_5 )
                                              return IndexOfObject( UnderlyingOriginalObject( Source( logic_new_func_x_5 ) ) );
                                          end ), hoisted_2_2 );
                                end );
                        end )[m_i_2];
              end ) );
        return ForAll( [ 1 .. deduped_21_1 ], function ( i_2 )
                local hoisted_1_2, hoisted_2_2, hoisted_3_2, hoisted_4_2, hoisted_5_2, hoisted_6_2;
                hoisted_6_2 := hoisted_19_1[i_2];
                hoisted_5_2 := hoisted_18_1[i_2];
                hoisted_4_2 := hoisted_16_1[i_2];
                hoisted_3_2 := hoisted_15_1[i_2];
                hoisted_2_2 := hoisted_14_1[i_2];
                hoisted_1_2 := hoisted_10_1[i_2];
                return ForAll( hoisted_20_1, function ( j_3 )
                        return hoisted_1_2[j_3] = hoisted_2_2[j_3] and hoisted_3_2[j_3] = hoisted_4_2[j_3] and hoisted_5_2[j_3] = hoisted_6_2[j_3];
                    end );
            end );
    fi;
    return;
end
########
        
    ;
    
    ##
    AddIsEqualForObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_1_1, deduped_2_1, deduped_3_1;
    deduped_3_1 := ListWithIdenticalEntries( NrOfSummandsOfCoproduct( cat_1 ), 0 );
    deduped_2_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( arg3_1 ), deduped_3_1 );
    deduped_1_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( arg2_1 ), deduped_3_1 );
    return NTuple( 2, Sum( deduped_1_1 ), deduped_1_1 ) = NTuple( 2, Sum( deduped_2_1 ), deduped_2_1 );
end
########
        
    , 100 );
    
    ##
    AddIsWellDefinedForMorphisms( cat,
        
########
function ( cat_1, alpha_1 )
    local hoisted_3_1, deduped_5_1, hoisted_6_1, deduped_9_1, hoisted_13_1, deduped_14_1, hoisted_15_1, hoisted_16_1, hoisted_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1, deduped_30_1;
    deduped_30_1 := [  ];
    deduped_29_1 := UnderlyingRing( cat_1 );
    deduped_28_1 := ModelingCategory( cat_1 );
    deduped_27_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_26_1 := [ 1 .. deduped_27_1 ];
    deduped_25_1 := UnderlyingCategory( deduped_28_1 );
    deduped_24_1 := ListWithIdenticalEntries( deduped_27_1, 0 );
    deduped_23_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( alpha_1 ) ), deduped_24_1 );
    deduped_22_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( alpha_1 ) ), deduped_24_1 );
    deduped_21_1 := Sum( deduped_23_1 );
    deduped_20_1 := Sum( deduped_22_1 );
    hoisted_3_1 := UnderlyingCategory( deduped_25_1 );
    deduped_5_1 := List( deduped_26_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_25_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_3_1, IndexOfObject, i_2 ) );
        end );
    deduped_19_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := deduped_5_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_25_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), ListWithIdenticalEntries( deduped_27_1, deduped_30_1 ) );
    deduped_9_1 := ZeroImmutable( deduped_29_1 );
    deduped_18_1 := Concatenation( List( deduped_26_1, function ( m_i_2 )
              local deduped_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
              deduped_4_2 := deduped_22_1[deduped_5_2];
              deduped_1_2 := deduped_5_1[m_i_2];
              hoisted_3_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_27_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_23_1[i_3], CreateCapCategoryMorphismWithAttributes( deduped_25_1, deduped_1_2, deduped_5_1[i_3], Coefficient, deduped_9_1 ) );
                    end ) );
              hoisted_2_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_23_1[i_3], CreateCapCategoryMorphismWithAttributes( deduped_25_1, deduped_1_2, deduped_5_1[i_3], Coefficient, deduped_9_1 ) );
                    end ) );
              return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_4_2 > 0 and deduped_23_1[deduped_5_2] = 0 then
                                return ListWithIdenticalEntries( deduped_4_2, deduped_30_1 );
                            else
                                return deduped_19_1[deduped_5_2];
                            fi;
                            return;
                        end )(  ), function ( row_3 )
                        return Concatenation( hoisted_2_2, row_3, hoisted_3_2 );
                    end ) );
          end ) );
    hoisted_17_1 := [ 1 .. deduped_21_1 ];
    deduped_14_1 := ListOfObjectsOfUnderlyingCategory( ModelingCategory( deduped_28_1 ) );
    hoisted_16_1 := Concatenation( List( deduped_26_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_23_1[i_2], UnderlyingOriginalObject( deduped_14_1[i_2] ) );
          end ) );
    hoisted_15_1 := Concatenation( List( deduped_26_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_22_1[i_2], UnderlyingOriginalObject( deduped_14_1[i_2] ) );
          end ) );
    hoisted_13_1 := RingElementFilter( deduped_29_1 );
    hoisted_6_1 := List( deduped_19_1, Length );
    if Sum( List( deduped_26_1, function ( m_i_2 )
                  local deduped_1_2, deduped_2_2;
                  deduped_2_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
                  deduped_1_2 := deduped_22_1[deduped_2_2];
                  return CAP_JIT_INCOMPLETE_LOGIC( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                              if (deduped_1_2 > 0 and deduped_23_1[deduped_2_2] = 0) then
                                  return deduped_1_2;
                              else
                                  return hoisted_6_1[deduped_2_2];
                              fi;
                              return;
                          end )(  ) );
              end ) ) <> deduped_20_1 then
        return false;
    elif ForAny( deduped_18_1, function ( row_2 )
              return Length( row_2 ) <> deduped_21_1;
          end ) then
        return false;
    elif not ForAll( [ 1 .. deduped_20_1 ], function ( i_2 )
                 local hoisted_1_2, hoisted_2_2;
                 hoisted_2_2 := IndexOfObject( hoisted_15_1[i_2] );
                 hoisted_1_2 := deduped_18_1[i_2];
                 return ForAll( hoisted_17_1, function ( j_3 )
                         local deduped_1_3;
                         deduped_1_3 := hoisted_1_2[j_3];
                         return (CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                       if hoisted_13_1( Coefficient( deduped_1_3 ) ) then
                                           return true;
                                       else
                                           return false;
                                       fi;
                                       return;
                                   end )(  ) and IndexOfObject( UnderlyingOriginalObject( Source( deduped_1_3 ) ) ) = hoisted_2_2 and IndexOfObject( UnderlyingOriginalObject( Range( deduped_1_3 ) ) ) = IndexOfObject( hoisted_16_1[j_3] ));
                     end );
             end ) then
        return false;
    else
        return true;
    fi;
    return;
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.IsWellDefinedForMorphisms :=
        
########
function ( cat_1, alpha_1 )
    local hoisted_3_1, deduped_5_1, hoisted_6_1, hoisted_7_1, deduped_10_1, hoisted_14_1, hoisted_15_1, deduped_16_1, hoisted_17_1, hoisted_18_1, hoisted_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1, deduped_30_1, deduped_31_1;
    deduped_31_1 := [  ];
    deduped_30_1 := UnderlyingRing( cat_1 );
    deduped_29_1 := ModelingCategory( cat_1 );
    deduped_28_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_27_1 := [ 1 .. deduped_28_1 ];
    deduped_26_1 := UnderlyingCategory( deduped_29_1 );
    deduped_25_1 := ListWithIdenticalEntries( deduped_28_1, 0 );
    deduped_24_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( alpha_1 ) ), deduped_25_1 );
    deduped_23_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( alpha_1 ) ), deduped_25_1 );
    deduped_22_1 := Sum( deduped_24_1 );
    deduped_21_1 := Sum( deduped_23_1 );
    hoisted_3_1 := UnderlyingCategory( deduped_26_1 );
    deduped_5_1 := List( deduped_27_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_26_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_3_1, IndexOfObject, i_2 ) );
        end );
    deduped_20_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := deduped_5_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_26_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), ListWithIdenticalEntries( deduped_28_1, deduped_31_1 ) );
    hoisted_19_1 := [ 1 .. deduped_22_1 ];
    deduped_16_1 := ListOfObjectsOfUnderlyingCategory( ModelingCategory( deduped_29_1 ) );
    hoisted_18_1 := Concatenation( List( deduped_27_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_24_1[i_2], UnderlyingOriginalObject( deduped_16_1[i_2] ) );
          end ) );
    hoisted_17_1 := Concatenation( List( deduped_27_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_23_1[i_2], UnderlyingOriginalObject( deduped_16_1[i_2] ) );
          end ) );
    hoisted_15_1 := RingElementFilter( deduped_30_1 );
    deduped_10_1 := ZeroImmutable( deduped_30_1 );
    hoisted_14_1 := Concatenation( List( deduped_27_1, function ( m_i_2 )
              local deduped_1_2, hoisted_2_2, hoisted_3_2;
              deduped_1_2 := deduped_5_1[m_i_2];
              hoisted_3_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_28_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_24_1[i_3], CreateCapCategoryMorphismWithAttributes( deduped_26_1, deduped_1_2, deduped_5_1[i_3], Coefficient, deduped_10_1 ) );
                    end ) );
              hoisted_2_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_24_1[i_3], CreateCapCategoryMorphismWithAttributes( deduped_26_1, deduped_1_2, deduped_5_1[i_3], Coefficient, deduped_10_1 ) );
                    end ) );
              return List( deduped_27_1, function ( i_3 )
                        local deduped_1_3;
                        deduped_1_3 := deduped_23_1[i_3];
                        return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                    if deduped_1_3 > 0 and deduped_24_1[i_3] = 0 then
                                        return ListWithIdenticalEntries( deduped_1_3, deduped_31_1 );
                                    else
                                        return deduped_20_1[i_3];
                                    fi;
                                    return;
                                end )(  ), function ( row_4 )
                                return Concatenation( hoisted_2_2, row_4, hoisted_3_2 );
                            end );
                    end )[m_i_2];
          end ) );
    hoisted_6_1 := List( deduped_20_1, Length );
    hoisted_7_1 := List( deduped_27_1, function ( i_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_23_1[i_2];
            if deduped_1_2 > 0 and deduped_24_1[i_2] = 0 then
                return deduped_1_2;
            else
                return hoisted_6_1[i_2];
            fi;
            return;
        end );
    if Sum( List( deduped_27_1, function ( m_i_2 )
                  return hoisted_7_1[m_i_2];
              end ) ) <> deduped_21_1 then
        return false;
    elif ForAny( Concatenation( List( deduped_27_1, function ( m_i_2 )
                  local deduped_1_2, hoisted_2_2, hoisted_3_2;
                  deduped_1_2 := deduped_5_1[m_i_2];
                  hoisted_3_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_28_1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_24_1[i_3], CreateCapCategoryMorphismWithAttributes( deduped_26_1, deduped_1_2, deduped_5_1[i_3], Coefficient, deduped_10_1 ) );
                        end ) );
                  hoisted_2_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                            return ListWithIdenticalEntries( deduped_24_1[i_3], CreateCapCategoryMorphismWithAttributes( deduped_26_1, deduped_1_2, deduped_5_1[i_3], Coefficient, deduped_10_1 ) );
                        end ) );
                  return List( deduped_27_1, function ( i_3 )
                            local deduped_1_3;
                            deduped_1_3 := deduped_23_1[i_3];
                            return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                        if deduped_1_3 > 0 and deduped_24_1[i_3] = 0 then
                                            return ListWithIdenticalEntries( deduped_1_3, deduped_31_1 );
                                        else
                                            return deduped_20_1[i_3];
                                        fi;
                                        return;
                                    end )(  ), function ( row_4 )
                                    return Concatenation( hoisted_2_2, row_4, hoisted_3_2 );
                                end );
                        end )[m_i_2];
              end ) ), function ( row_2 )
              return Length( row_2 ) <> deduped_22_1;
          end ) then
        return false;
    elif not ForAll( [ 1 .. deduped_21_1 ], function ( i_2 )
                 local hoisted_1_2, hoisted_2_2;
                 hoisted_2_2 := IndexOfObject( hoisted_17_1[i_2] );
                 hoisted_1_2 := hoisted_14_1[i_2];
                 return ForAll( hoisted_19_1, function ( j_3 )
                         local deduped_1_3;
                         deduped_1_3 := hoisted_1_2[j_3];
                         return (CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                       if hoisted_15_1( Coefficient( deduped_1_3 ) ) then
                                           return true;
                                       else
                                           return false;
                                       fi;
                                       return;
                                   end )(  ) and IndexOfObject( UnderlyingOriginalObject( Source( deduped_1_3 ) ) ) = hoisted_2_2 and IndexOfObject( UnderlyingOriginalObject( Range( deduped_1_3 ) ) ) = IndexOfObject( hoisted_18_1[j_3] ));
                     end );
             end ) then
        return false;
    else
        return true;
    fi;
    return;
end
########
        
    ;
    
    ##
    AddIsWellDefinedForObjects( cat,
        
########
function ( cat_1, arg2_1 )
    local deduped_1_1, deduped_2_1;
    deduped_2_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_1_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( arg2_1 ), ListWithIdenticalEntries( deduped_2_1, 0 ) );
    if not true then
        return false;
    elif not Length( deduped_1_1 ) = deduped_2_1 then
        return false;
    elif ForAny( deduped_1_1, function ( multiplicity_2 )
              return multiplicity_2 < 0;
          end ) then
        return false;
    else
        return true;
    fi;
    return;
end
########
        
    , 100 );
    
    ##
    AddIsZeroForMorphisms( cat,
        
########
function ( cat_1, arg2_1 )
    local hoisted_4_1, hoisted_6_1, hoisted_7_1, deduped_8_1, hoisted_10_1, hoisted_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1;
    deduped_18_1 := [  ];
    deduped_17_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_16_1 := [ 1 .. deduped_17_1 ];
    deduped_15_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
    deduped_14_1 := ListWithIdenticalEntries( deduped_17_1, 0 );
    deduped_13_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( arg2_1 ) ), deduped_14_1 );
    deduped_12_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( arg2_1 ) ), deduped_14_1 );
    hoisted_11_1 := [ 1 .. Sum( deduped_13_1 ) ];
    deduped_8_1 := ZeroImmutable( UnderlyingRing( cat_1 ) );
    hoisted_4_1 := UnderlyingCategory( deduped_15_1 );
    hoisted_6_1 := List( deduped_16_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_15_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_4_1, IndexOfObject, i_2 ) );
        end );
    hoisted_7_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( arg2_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := hoisted_6_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_15_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), ListWithIdenticalEntries( deduped_17_1, deduped_18_1 ) );
    hoisted_10_1 := Concatenation( List( deduped_16_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
              deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
              deduped_3_2 := deduped_12_1[deduped_4_2];
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_17_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_13_1[i_3], deduped_8_1 );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_13_1[i_3], deduped_8_1 );
                    end ) );
              return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_3_2 > 0 and deduped_13_1[deduped_4_2] = 0 then
                                return ListWithIdenticalEntries( deduped_3_2, deduped_18_1 );
                            else
                                return hoisted_7_1[deduped_4_2];
                            fi;
                            return;
                        end )(  ), function ( row_3 )
                        return Concatenation( hoisted_1_2, List( row_3, Coefficient ), hoisted_2_2 );
                    end ) );
          end ) );
    return ForAll( [ 1 .. Sum( deduped_12_1 ) ], function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := hoisted_10_1[i_2];
            return ForAll( hoisted_11_1, function ( j_3 )
                    return hoisted_1_2[j_3] = deduped_8_1;
                end );
        end );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.IsZeroForMorphisms :=
        
########
function ( cat_1, arg2_1 )
    local hoisted_4_1, hoisted_6_1, hoisted_7_1, deduped_8_1, hoisted_11_1, hoisted_12_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1;
    deduped_19_1 := [  ];
    deduped_18_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_17_1 := [ 1 .. deduped_18_1 ];
    deduped_16_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
    deduped_15_1 := ListWithIdenticalEntries( deduped_18_1, 0 );
    deduped_14_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( arg2_1 ) ), deduped_15_1 );
    deduped_13_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( arg2_1 ) ), deduped_15_1 );
    hoisted_12_1 := [ 1 .. Sum( deduped_14_1 ) ];
    deduped_8_1 := ZeroImmutable( UnderlyingRing( cat_1 ) );
    hoisted_4_1 := UnderlyingCategory( deduped_16_1 );
    hoisted_6_1 := List( deduped_17_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_16_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_4_1, IndexOfObject, i_2 ) );
        end );
    hoisted_7_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( arg2_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := hoisted_6_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_16_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), ListWithIdenticalEntries( deduped_18_1, deduped_19_1 ) );
    hoisted_11_1 := Concatenation( List( deduped_17_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2;
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_18_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_14_1[i_3], deduped_8_1 );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_14_1[i_3], deduped_8_1 );
                    end ) );
              return List( deduped_17_1, function ( i_3 )
                        local deduped_1_3;
                        deduped_1_3 := deduped_13_1[i_3];
                        return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                    if deduped_1_3 > 0 and deduped_14_1[i_3] = 0 then
                                        return ListWithIdenticalEntries( deduped_1_3, deduped_19_1 );
                                    else
                                        return hoisted_7_1[i_3];
                                    fi;
                                    return;
                                end )(  ), function ( row_4 )
                                return Concatenation( hoisted_1_2, List( row_4, Coefficient ), hoisted_2_2 );
                            end );
                    end )[m_i_2];
          end ) );
    return ForAll( [ 1 .. Sum( deduped_13_1 ) ], function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := hoisted_11_1[i_2];
            return ForAll( hoisted_12_1, function ( j_3 )
                    return hoisted_1_2[j_3] = deduped_8_1;
                end );
        end );
end
########
        
    ;
    
    ##
    AddKernelEmbeddingWithGivenKernelObject( cat,
        
########
function ( cat_1, alpha_1, P_1 )
    local deduped_1_1;
    deduped_1_1 := UnderlyingCategoryOfRows( cat_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, P_1, Source( alpha_1 ), ListOfPairsOfMorphismAndIndex, Filtered( List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
                local deduped_1_2, deduped_2_2;
                deduped_2_2 := pair_2[1];
                deduped_1_2 := SyzygiesOfRows( UnderlyingMatrix( deduped_2_2 ) );
                return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_1_1, CreateCapCategoryObjectWithAttributes( deduped_1_1, RankOfObject, NumberRows( deduped_1_2 ) ), Source( deduped_2_2 ), UnderlyingMatrix, deduped_1_2 ), pair_2[2] );
            end ), function ( pair_2 )
              local deduped_1_2;
              deduped_1_2 := pair_2[1];
              return not RankOfObject( Source( deduped_1_2 ) ) = 0 or not RankOfObject( Target( deduped_1_2 ) ) = 0;
          end ) );
end
########
        
    , 100 );
    
    ##
    AddKernelObject( cat,
        
########
function ( cat_1, alpha_1 )
    local hoisted_1_1;
    hoisted_1_1 := UnderlyingCategoryOfRows( cat_1 );
    return CreateCapCategoryObjectWithAttributes( cat_1, ListOfPairsOfObjectAndIndex, Filtered( List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
                local deduped_1_2;
                deduped_1_2 := pair_2[1];
                return NTuple( 2, CreateCapCategoryObjectWithAttributes( hoisted_1_1, RankOfObject, RankOfObject( Source( deduped_1_2 ) ) - RowRankOfMatrix( UnderlyingMatrix( deduped_1_2 ) ) ), pair_2[2] );
            end ), function ( pair_2 )
              return not RankOfObject( pair_2[1] ) = 0;
          end ) );
end
########
        
    , 100 );
    
    ##
    AddLift( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    local hoisted_1_1, deduped_3_1, hoisted_4_1, hoisted_6_1, deduped_7_1, hoisted_8_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1;
    deduped_14_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_13_1 := Source( beta_1 );
    deduped_12_1 := Source( alpha_1 );
    deduped_11_1 := ListOfPairsOfObjectAndIndex( deduped_13_1 );
    deduped_10_1 := ListOfPairsOfObjectAndIndex( deduped_12_1 );
    hoisted_8_1 := ListOfPairsOfObjectAndIndex( Target( beta_1 ) );
    deduped_7_1 := UnderlyingRing( cat_1 );
    hoisted_6_1 := ListOfPairsOfObjectAndIndex( Target( alpha_1 ) );
    hoisted_4_1 := ListOfPairsOfMorphismAndIndex( beta_1 );
    deduped_3_1 := CreateCapCategoryObjectWithAttributes( deduped_14_1, RankOfObject, 0 );
    hoisted_1_1 := ListOfPairsOfMorphismAndIndex( alpha_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_12_1, deduped_13_1, ListOfPairsOfMorphismAndIndex, List( Union2( List( deduped_10_1, function ( elem_2 )
                  return elem_2[2];
              end ), List( deduped_11_1, function ( elem_2 )
                  return elem_2[2];
              end ) ), function ( index_2 )
              local deduped_1_2, deduped_2_2, deduped_3_2, deduped_4_2, deduped_5_2, deduped_6_2, deduped_7_2, deduped_8_2, deduped_9_2, deduped_10_2, deduped_11_2, deduped_12_2, deduped_13_2, deduped_14_2;
              deduped_14_2 := Filtered( hoisted_8_1, function ( pair_3 )
                      return pair_3[2] = index_2;
                  end );
              deduped_13_2 := Filtered( hoisted_6_1, function ( pair_3 )
                      return pair_3[2] = index_2;
                  end );
              deduped_12_2 := Filtered( deduped_11_1, function ( pair_3 )
                      return pair_3[2] = index_2;
                  end );
              deduped_11_2 := Filtered( hoisted_4_1, function ( pair_3 )
                      return pair_3[2] = index_2;
                  end );
              deduped_10_2 := Filtered( deduped_10_1, function ( pair_3 )
                      return pair_3[2] = index_2;
                  end );
              deduped_9_2 := Filtered( hoisted_1_1, function ( pair_3 )
                      return pair_3[2] = index_2;
                  end );
              deduped_8_2 := Length( deduped_12_2 ) = 0;
              deduped_7_2 := Length( deduped_11_2 ) = 0;
              deduped_6_2 := Length( deduped_10_2 ) = 0;
              deduped_5_2 := Length( deduped_9_2 ) = 0;
              deduped_4_2 := deduped_11_2[1][1];
              deduped_3_2 := deduped_12_2[1][1];
              deduped_2_2 := deduped_9_2[1][1];
              deduped_1_2 := deduped_10_2[1][1];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_14_1, CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_5_2 then
                                return CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                          if deduped_6_2 then
                                              return deduped_3_1;
                                          else
                                              return deduped_1_2;
                                          fi;
                                          return;
                                      end )(  );
                            else
                                return Source( deduped_2_2 );
                            fi;
                            return;
                        end )(  ), CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_7_2 then
                                return CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                          if deduped_8_2 then
                                              return deduped_3_1;
                                          else
                                              return deduped_3_2;
                                          fi;
                                          return;
                                      end )(  );
                            else
                                return Source( deduped_4_2 );
                            fi;
                            return;
                        end )(  ), UnderlyingMatrix, SafeRightDivide( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                              if deduped_5_2 then
                                  return HomalgZeroMatrix( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                              if deduped_6_2 then
                                                  return 0;
                                              else
                                                  return RankOfObject( deduped_1_2 );
                                              fi;
                                              return;
                                          end )(  ), CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                              if Length( deduped_13_2 ) = 0 then
                                                  return 0;
                                              else
                                                  return RankOfObject( deduped_13_2[1][1] );
                                              fi;
                                              return;
                                          end )(  ), deduped_7_1 );
                              else
                                  return UnderlyingMatrix( deduped_2_2 );
                              fi;
                              return;
                          end )(  ), CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                              if deduped_7_2 then
                                  return HomalgZeroMatrix( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                              if deduped_8_2 then
                                                  return 0;
                                              else
                                                  return RankOfObject( deduped_3_2 );
                                              fi;
                                              return;
                                          end )(  ), CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                              if Length( deduped_14_2 ) = 0 then
                                                  return 0;
                                              else
                                                  return RankOfObject( deduped_14_2[1][1] );
                                              fi;
                                              return;
                                          end )(  ), deduped_7_1 );
                              else
                                  return UnderlyingMatrix( deduped_4_2 );
                              fi;
                              return;
                          end )(  ) ) ), index_2 );
          end ) );
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
    AddMorphismDatum( cat,
        
########
function ( cat_1, arg2_1 )
    return ListOfPairsOfMorphismAndIndex( arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddMultiplyWithElementOfCommutativeRingForMorphisms( cat,
        
########
function ( cat_1, r_1, alpha_1 )
    local deduped_2_1, hoisted_5_1, deduped_7_1, deduped_8_1, hoisted_10_1, hoisted_11_1, deduped_12_1, hoisted_13_1, hoisted_14_1, hoisted_15_1, deduped_16_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1;
    deduped_28_1 := [  ];
    deduped_27_1 := UnderlyingRing( cat_1 );
    deduped_26_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_25_1 := Range( alpha_1 );
    deduped_24_1 := Source( alpha_1 );
    deduped_23_1 := [ 1 .. deduped_26_1 ];
    deduped_22_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
    deduped_21_1 := ListWithIdenticalEntries( deduped_26_1, 0 );
    deduped_20_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_25_1 ), deduped_21_1 );
    deduped_19_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_24_1 ), deduped_21_1 );
    deduped_18_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_16_1 := List( [ 0 .. Length( deduped_20_1 ) ], function ( i_2 )
            return Sum( deduped_20_1{[ 1 .. i_2 ]} );
        end );
    hoisted_14_1 := [ 1 .. Sum( deduped_20_1 ) ];
    deduped_12_1 := ZeroImmutable( deduped_27_1 );
    hoisted_5_1 := UnderlyingCategory( deduped_22_1 );
    deduped_7_1 := List( deduped_23_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_22_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_5_1, IndexOfObject, i_2 ) );
        end );
    deduped_8_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := deduped_7_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_22_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), ListWithIdenticalEntries( deduped_26_1, deduped_28_1 ) );
    hoisted_13_1 := Concatenation( List( deduped_23_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
              deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
              deduped_3_2 := deduped_19_1[deduped_4_2];
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_26_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_20_1[i_3], deduped_12_1 );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_20_1[i_3], deduped_12_1 );
                    end ) );
              return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_3_2 > 0 and deduped_20_1[deduped_4_2] = 0 then
                                return ListWithIdenticalEntries( deduped_3_2, deduped_28_1 );
                            else
                                return deduped_8_1[deduped_4_2];
                            fi;
                            return;
                        end )(  ), function ( row_3 )
                        return Concatenation( hoisted_1_2, List( row_3, Coefficient ), hoisted_2_2 );
                    end ) );
          end ) );
    hoisted_11_1 := Concatenation( List( deduped_23_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
              deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
              deduped_3_2 := deduped_19_1[deduped_4_2];
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_26_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_20_1[i_3], deduped_7_1[i_3] );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_20_1[i_3], deduped_7_1[i_3] );
                    end ) );
              return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_3_2 > 0 and deduped_20_1[deduped_4_2] = 0 then
                                return ListWithIdenticalEntries( deduped_3_2, deduped_28_1 );
                            else
                                return deduped_8_1[deduped_4_2];
                            fi;
                            return;
                        end )(  ), function ( row_3 )
                        return Concatenation( hoisted_1_2, List( row_3, Target ), hoisted_2_2 );
                    end ) );
          end ) );
    hoisted_10_1 := Concatenation( List( deduped_23_1, function ( m_i_2 )
              local deduped_1_2, hoisted_2_2, hoisted_3_2, deduped_4_2, deduped_5_2;
              deduped_5_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
              deduped_4_2 := deduped_19_1[deduped_5_2];
              deduped_1_2 := deduped_7_1[m_i_2];
              hoisted_3_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_26_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_20_1[i_3], deduped_1_2 );
                    end ) );
              hoisted_2_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_20_1[i_3], deduped_1_2 );
                    end ) );
              return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_4_2 > 0 and deduped_20_1[deduped_5_2] = 0 then
                                return ListWithIdenticalEntries( deduped_4_2, deduped_28_1 );
                            else
                                return deduped_8_1[deduped_5_2];
                            fi;
                            return;
                        end )(  ), function ( row_3 )
                        return Concatenation( hoisted_2_2, List( row_3, Source ), hoisted_3_2 );
                    end ) );
          end ) );
    hoisted_15_1 := List( [ 1 .. Sum( deduped_19_1 ) ], function ( i_2 )
            local hoisted_1_2, hoisted_2_2, hoisted_3_2;
            hoisted_3_2 := hoisted_13_1[i_2];
            hoisted_2_2 := hoisted_11_1[i_2];
            hoisted_1_2 := hoisted_10_1[i_2];
            return List( hoisted_14_1, function ( j_3 )
                    return CreateCapCategoryMorphismWithAttributes( deduped_22_1, hoisted_1_2[j_3], hoisted_2_2[j_3], Coefficient, r_1 * hoisted_3_2[j_3] );
                end );
        end );
    deduped_2_1 := List( [ 0 .. Length( deduped_19_1 ) ], function ( i_2 )
            return Sum( deduped_19_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_24_1, deduped_25_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_19_1, List( deduped_23_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_16_1[obj_idx_2] + 1 .. deduped_16_1[deduped_2_2] ];
                  return List( [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_15_1[nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_20_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                        return List( row_3, Coefficient );
                    end ), deduped_19_1[deduped_2_2], deduped_20_1[deduped_2_2], deduped_27_1 );
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_18_1, CreateCapCategoryObjectWithAttributes( deduped_18_1, RankOfObject, NumberRows( deduped_1_2 ) ), CreateCapCategoryObjectWithAttributes( deduped_18_1, RankOfObject, NumberColumns( deduped_1_2 ) ), UnderlyingMatrix, deduped_1_2 ), deduped_2_2 );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.MultiplyWithElementOfCommutativeRingForMorphisms :=
        
########
function ( cat_1, r_1, alpha_1 )
    local deduped_2_1, hoisted_5_1, deduped_7_1, deduped_8_1, hoisted_11_1, hoisted_12_1, deduped_13_1, hoisted_14_1, hoisted_15_1, hoisted_16_1, deduped_17_1, deduped_18_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1;
    deduped_29_1 := [  ];
    deduped_28_1 := UnderlyingRing( cat_1 );
    deduped_27_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_26_1 := Range( alpha_1 );
    deduped_25_1 := Source( alpha_1 );
    deduped_24_1 := [ 1 .. deduped_27_1 ];
    deduped_23_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
    deduped_22_1 := ListWithIdenticalEntries( deduped_27_1, 0 );
    deduped_21_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_26_1 ), deduped_22_1 );
    deduped_20_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_25_1 ), deduped_22_1 );
    deduped_18_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_17_1 := List( [ 0 .. Length( deduped_21_1 ) ], function ( i_2 )
            return Sum( deduped_21_1{[ 1 .. i_2 ]} );
        end );
    hoisted_15_1 := [ 1 .. Sum( deduped_21_1 ) ];
    deduped_13_1 := ZeroImmutable( deduped_28_1 );
    hoisted_5_1 := UnderlyingCategory( deduped_23_1 );
    deduped_7_1 := List( deduped_24_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_23_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_5_1, IndexOfObject, i_2 ) );
        end );
    deduped_8_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := deduped_7_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_23_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), ListWithIdenticalEntries( deduped_27_1, deduped_29_1 ) );
    hoisted_14_1 := Concatenation( List( deduped_24_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2;
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_27_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_21_1[i_3], deduped_13_1 );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_21_1[i_3], deduped_13_1 );
                    end ) );
              return List( deduped_24_1, function ( i_3 )
                        local deduped_1_3;
                        deduped_1_3 := deduped_20_1[i_3];
                        return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                    if deduped_1_3 > 0 and deduped_21_1[i_3] = 0 then
                                        return ListWithIdenticalEntries( deduped_1_3, deduped_29_1 );
                                    else
                                        return deduped_8_1[i_3];
                                    fi;
                                    return;
                                end )(  ), function ( row_4 )
                                return Concatenation( hoisted_1_2, List( row_4, Coefficient ), hoisted_2_2 );
                            end );
                    end )[m_i_2];
          end ) );
    hoisted_12_1 := Concatenation( List( deduped_24_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2;
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_27_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_21_1[i_3], deduped_7_1[i_3] );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_21_1[i_3], deduped_7_1[i_3] );
                    end ) );
              return List( deduped_24_1, function ( i_3 )
                        local deduped_1_3;
                        deduped_1_3 := deduped_20_1[i_3];
                        return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                    if deduped_1_3 > 0 and deduped_21_1[i_3] = 0 then
                                        return ListWithIdenticalEntries( deduped_1_3, deduped_29_1 );
                                    else
                                        return deduped_8_1[i_3];
                                    fi;
                                    return;
                                end )(  ), function ( row_4 )
                                return Concatenation( hoisted_1_2, List( row_4, Target ), hoisted_2_2 );
                            end );
                    end )[m_i_2];
          end ) );
    hoisted_11_1 := Concatenation( List( deduped_24_1, function ( m_i_2 )
              local deduped_1_2, hoisted_2_2, hoisted_3_2;
              deduped_1_2 := deduped_7_1[m_i_2];
              hoisted_3_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_27_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_21_1[i_3], deduped_1_2 );
                    end ) );
              hoisted_2_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_21_1[i_3], deduped_1_2 );
                    end ) );
              return List( deduped_24_1, function ( i_3 )
                        local deduped_1_3;
                        deduped_1_3 := deduped_20_1[i_3];
                        return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                    if deduped_1_3 > 0 and deduped_21_1[i_3] = 0 then
                                        return ListWithIdenticalEntries( deduped_1_3, deduped_29_1 );
                                    else
                                        return deduped_8_1[i_3];
                                    fi;
                                    return;
                                end )(  ), function ( row_4 )
                                return Concatenation( hoisted_2_2, List( row_4, Source ), hoisted_3_2 );
                            end );
                    end )[m_i_2];
          end ) );
    hoisted_16_1 := List( [ 1 .. Sum( deduped_20_1 ) ], function ( i_2 )
            local hoisted_1_2, hoisted_2_2, hoisted_3_2;
            hoisted_3_2 := hoisted_14_1[i_2];
            hoisted_2_2 := hoisted_12_1[i_2];
            hoisted_1_2 := hoisted_11_1[i_2];
            return List( hoisted_15_1, function ( j_3 )
                    return CreateCapCategoryMorphismWithAttributes( deduped_23_1, hoisted_1_2[j_3], hoisted_2_2[j_3], Coefficient, r_1 * hoisted_3_2[j_3] );
                end );
        end );
    deduped_2_1 := List( [ 0 .. Length( deduped_20_1 ) ], function ( i_2 )
            return Sum( deduped_20_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_25_1, deduped_26_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_20_1, List( deduped_24_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_17_1[obj_idx_2] + 1 .. deduped_17_1[deduped_2_2] ];
                  return List( [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_16_1[nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_21_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2, deduped_3_2;
              deduped_3_2 := pair_2[2];
              deduped_2_2 := deduped_21_1[deduped_3_2];
              deduped_1_2 := deduped_20_1[deduped_3_2];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_18_1, CreateCapCategoryObjectWithAttributes( deduped_18_1, RankOfObject, deduped_1_2 ), CreateCapCategoryObjectWithAttributes( deduped_18_1, RankOfObject, deduped_2_2 ), UnderlyingMatrix, HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                            return List( row_3, Coefficient );
                        end ), deduped_1_2, deduped_2_2, deduped_28_1 ) ), deduped_3_2 );
          end ) );
end
########
        
    ;
    
    ##
    AddObjectConstructor( cat,
        
########
function ( cat_1, arg2_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, ListOfPairsOfObjectAndIndex, arg2_1 );
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
    AddPreCompose( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    local deduped_2_1, deduped_3_1, hoisted_4_1, hoisted_6_1, hoisted_9_1, deduped_11_1, hoisted_12_1, deduped_13_1, hoisted_15_1, hoisted_16_1, hoisted_17_1, hoisted_18_1, hoisted_19_1, hoisted_20_1, hoisted_21_1, deduped_22_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1, deduped_30_1, deduped_31_1, deduped_32_1, deduped_33_1, deduped_34_1, deduped_35_1, deduped_36_1, deduped_37_1;
    deduped_37_1 := [  ];
    deduped_36_1 := UnderlyingRing( cat_1 );
    deduped_35_1 := ModelingCategory( cat_1 );
    deduped_34_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_33_1 := Range( beta_1 );
    deduped_32_1 := Source( alpha_1 );
    deduped_31_1 := [ 1 .. deduped_34_1 ];
    deduped_30_1 := ListWithIdenticalEntries( deduped_34_1, deduped_37_1 );
    deduped_29_1 := UnderlyingCategory( deduped_35_1 );
    deduped_28_1 := ListWithIdenticalEntries( deduped_34_1, 0 );
    deduped_27_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( alpha_1 ) ), deduped_28_1 );
    deduped_26_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_33_1 ), deduped_28_1 );
    deduped_25_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_32_1 ), deduped_28_1 );
    deduped_24_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_22_1 := List( [ 0 .. Length( deduped_26_1 ) ], function ( i_2 )
            return Sum( deduped_26_1{[ 1 .. i_2 ]} );
        end );
    hoisted_20_1 := [ 1 .. Sum( deduped_26_1 ) ];
    hoisted_19_1 := [ 1 .. Sum( deduped_27_1 ) ];
    hoisted_9_1 := UnderlyingCategory( deduped_29_1 );
    deduped_11_1 := List( deduped_31_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_29_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_9_1, IndexOfObject, i_2 ) );
        end );
    hoisted_17_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( beta_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := deduped_11_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_29_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), deduped_30_1 );
    hoisted_16_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( beta_1 ) ), deduped_28_1 );
    deduped_13_1 := ZeroImmutable( deduped_36_1 );
    hoisted_18_1 := Concatenation( List( deduped_31_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
              deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
              deduped_3_2 := hoisted_16_1[deduped_4_2];
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_34_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_26_1[i_3], deduped_13_1 );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_26_1[i_3], deduped_13_1 );
                    end ) );
              return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_3_2 > 0 and deduped_26_1[deduped_4_2] = 0 then
                                return ListWithIdenticalEntries( deduped_3_2, deduped_37_1 );
                            else
                                return hoisted_17_1[deduped_4_2];
                            fi;
                            return;
                        end )(  ), function ( row_3 )
                        return Concatenation( hoisted_1_2, List( row_3, Coefficient ), hoisted_2_2 );
                    end ) );
          end ) );
    hoisted_12_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := deduped_11_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_29_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), deduped_30_1 );
    hoisted_15_1 := Concatenation( List( deduped_31_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2, deduped_3_2, deduped_4_2;
              deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( m_i_2 );
              deduped_3_2 := deduped_25_1[deduped_4_2];
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_34_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_27_1[i_3], deduped_13_1 );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_27_1[i_3], deduped_13_1 );
                    end ) );
              return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                            if deduped_3_2 > 0 and deduped_27_1[deduped_4_2] = 0 then
                                return ListWithIdenticalEntries( deduped_3_2, deduped_37_1 );
                            else
                                return hoisted_12_1[deduped_4_2];
                            fi;
                            return;
                        end )(  ), function ( row_3 )
                        return Concatenation( hoisted_1_2, List( row_3, Coefficient ), hoisted_2_2 );
                    end ) );
          end ) );
    deduped_3_1 := ListOfObjectsOfUnderlyingCategory( ModelingCategory( deduped_35_1 ) );
    hoisted_6_1 := Concatenation( List( deduped_31_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_26_1[i_2], deduped_3_1[i_2] );
          end ) );
    hoisted_4_1 := Concatenation( List( deduped_31_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_25_1[i_2], deduped_3_1[i_2] );
          end ) );
    hoisted_21_1 := List( [ 1 .. Sum( deduped_25_1 ) ], function ( i_2 )
            local hoisted_1_2, hoisted_2_2;
            hoisted_2_2 := hoisted_4_1[i_2];
            hoisted_1_2 := hoisted_15_1[i_2];
            return List( hoisted_20_1, function ( j_3 )
                    return CreateCapCategoryMorphismWithAttributes( deduped_29_1, hoisted_2_2, hoisted_6_1[j_3], Coefficient, Sum( List( hoisted_19_1, function ( k_4 )
                                return hoisted_1_2[k_4] * hoisted_18_1[k_4][j_3];
                            end ) ) );
                end );
        end );
    deduped_2_1 := List( [ 0 .. Length( deduped_25_1 ) ], function ( i_2 )
            return Sum( deduped_25_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_32_1, deduped_33_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_25_1, List( deduped_31_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_22_1[obj_idx_2] + 1 .. deduped_22_1[deduped_2_2] ];
                  return List( [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_21_1[nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_26_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                        return List( row_3, Coefficient );
                    end ), deduped_25_1[deduped_2_2], deduped_26_1[deduped_2_2], deduped_36_1 );
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_24_1, CreateCapCategoryObjectWithAttributes( deduped_24_1, RankOfObject, NumberRows( deduped_1_2 ) ), CreateCapCategoryObjectWithAttributes( deduped_24_1, RankOfObject, NumberColumns( deduped_1_2 ) ), UnderlyingMatrix, deduped_1_2 ), deduped_2_2 );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.PreCompose :=
        
########
function ( cat_1, alpha_1, beta_1 )
    local deduped_2_1, deduped_3_1, hoisted_4_1, hoisted_6_1, hoisted_9_1, deduped_11_1, hoisted_12_1, deduped_13_1, hoisted_16_1, hoisted_17_1, hoisted_18_1, hoisted_19_1, hoisted_20_1, hoisted_21_1, hoisted_22_1, deduped_23_1, deduped_24_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1, deduped_30_1, deduped_31_1, deduped_32_1, deduped_33_1, deduped_34_1, deduped_35_1, deduped_36_1, deduped_37_1, deduped_38_1;
    deduped_38_1 := [  ];
    deduped_37_1 := UnderlyingRing( cat_1 );
    deduped_36_1 := ModelingCategory( cat_1 );
    deduped_35_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_34_1 := Range( beta_1 );
    deduped_33_1 := Source( alpha_1 );
    deduped_32_1 := [ 1 .. deduped_35_1 ];
    deduped_31_1 := ListWithIdenticalEntries( deduped_35_1, deduped_38_1 );
    deduped_30_1 := UnderlyingCategory( deduped_36_1 );
    deduped_29_1 := ListWithIdenticalEntries( deduped_35_1, 0 );
    deduped_28_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( alpha_1 ) ), deduped_29_1 );
    deduped_27_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_34_1 ), deduped_29_1 );
    deduped_26_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( deduped_33_1 ), deduped_29_1 );
    deduped_24_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_23_1 := List( [ 0 .. Length( deduped_27_1 ) ], function ( i_2 )
            return Sum( deduped_27_1{[ 1 .. i_2 ]} );
        end );
    hoisted_21_1 := [ 1 .. Sum( deduped_27_1 ) ];
    hoisted_20_1 := [ 1 .. Sum( deduped_28_1 ) ];
    hoisted_9_1 := UnderlyingCategory( deduped_30_1 );
    deduped_11_1 := List( deduped_32_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_30_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_9_1, IndexOfObject, i_2 ) );
        end );
    hoisted_18_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( beta_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := deduped_11_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_30_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), deduped_31_1 );
    hoisted_17_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( beta_1 ) ), deduped_29_1 );
    deduped_13_1 := ZeroImmutable( deduped_37_1 );
    hoisted_19_1 := Concatenation( List( deduped_32_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2;
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_35_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_27_1[i_3], deduped_13_1 );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_27_1[i_3], deduped_13_1 );
                    end ) );
              return List( deduped_32_1, function ( i_3 )
                        local deduped_1_3;
                        deduped_1_3 := hoisted_17_1[i_3];
                        return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                    if deduped_1_3 > 0 and deduped_27_1[i_3] = 0 then
                                        return ListWithIdenticalEntries( deduped_1_3, deduped_38_1 );
                                    else
                                        return hoisted_18_1[i_3];
                                    fi;
                                    return;
                                end )(  ), function ( row_4 )
                                return Concatenation( hoisted_1_2, List( row_4, Coefficient ), hoisted_2_2 );
                            end );
                    end )[m_i_2];
          end ) );
    hoisted_12_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( alpha_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := deduped_11_1[deduped_2_2];
              return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_2[1] ) ), function ( row_3 )
                        return List( row_3, function ( c_4 )
                                return CreateCapCategoryMorphismWithAttributes( deduped_30_1, deduped_1_2, deduped_1_2, Coefficient, c_4 );
                            end );
                    end ), deduped_2_2 );
          end ), deduped_31_1 );
    hoisted_16_1 := Concatenation( List( deduped_32_1, function ( m_i_2 )
              local hoisted_1_2, hoisted_2_2;
              hoisted_2_2 := Concatenation( List( [ m_i_2 + 1 .. deduped_35_1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_28_1[i_3], deduped_13_1 );
                    end ) );
              hoisted_1_2 := Concatenation( List( [ 1 .. m_i_2 - 1 ], function ( i_3 )
                        return ListWithIdenticalEntries( deduped_28_1[i_3], deduped_13_1 );
                    end ) );
              return List( deduped_32_1, function ( i_3 )
                        local deduped_1_3;
                        deduped_1_3 := deduped_26_1[i_3];
                        return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                    if deduped_1_3 > 0 and deduped_28_1[i_3] = 0 then
                                        return ListWithIdenticalEntries( deduped_1_3, deduped_38_1 );
                                    else
                                        return hoisted_12_1[i_3];
                                    fi;
                                    return;
                                end )(  ), function ( row_4 )
                                return Concatenation( hoisted_1_2, List( row_4, Coefficient ), hoisted_2_2 );
                            end );
                    end )[m_i_2];
          end ) );
    deduped_3_1 := ListOfObjectsOfUnderlyingCategory( ModelingCategory( deduped_36_1 ) );
    hoisted_6_1 := Concatenation( List( deduped_32_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_27_1[i_2], deduped_3_1[i_2] );
          end ) );
    hoisted_4_1 := Concatenation( List( deduped_32_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_26_1[i_2], deduped_3_1[i_2] );
          end ) );
    hoisted_22_1 := List( [ 1 .. Sum( deduped_26_1 ) ], function ( i_2 )
            local hoisted_1_2, hoisted_2_2;
            hoisted_2_2 := hoisted_4_1[i_2];
            hoisted_1_2 := hoisted_16_1[i_2];
            return List( hoisted_21_1, function ( j_3 )
                    return CreateCapCategoryMorphismWithAttributes( deduped_30_1, hoisted_2_2, hoisted_6_1[j_3], Coefficient, Sum( List( hoisted_20_1, function ( k_4 )
                                return hoisted_1_2[k_4] * hoisted_19_1[k_4][j_3];
                            end ) ) );
                end );
        end );
    deduped_2_1 := List( [ 0 .. Length( deduped_26_1 ) ], function ( i_2 )
            return Sum( deduped_26_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_33_1, deduped_34_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_26_1, List( deduped_32_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_23_1[obj_idx_2] + 1 .. deduped_23_1[deduped_2_2] ];
                  return List( [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_22_1[nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_27_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2, deduped_3_2;
              deduped_3_2 := pair_2[2];
              deduped_2_2 := deduped_27_1[deduped_3_2];
              deduped_1_2 := deduped_26_1[deduped_3_2];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_24_1, CreateCapCategoryObjectWithAttributes( deduped_24_1, RankOfObject, deduped_1_2 ), CreateCapCategoryObjectWithAttributes( deduped_24_1, RankOfObject, deduped_2_2 ), UnderlyingMatrix, HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                            return List( row_3, Coefficient );
                        end ), deduped_1_2, deduped_2_2, deduped_37_1 ) ), deduped_3_2 );
          end ) );
end
########
        
    ;
    
    ##
    AddSumOfMorphisms( cat,
        
########
function ( cat_1, source_1, list_of_morphisms_1, range_1 )
    local deduped_2_1, deduped_3_1, hoisted_4_1, hoisted_6_1, hoisted_9_1, hoisted_11_1, hoisted_12_1, deduped_13_1, hoisted_16_1, hoisted_17_1, deduped_18_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1;
    deduped_29_1 := [  ];
    deduped_28_1 := UnderlyingRing( cat_1 );
    deduped_27_1 := ModelingCategory( cat_1 );
    deduped_26_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_25_1 := [ 1 .. deduped_26_1 ];
    deduped_24_1 := UnderlyingCategory( deduped_27_1 );
    deduped_23_1 := ListWithIdenticalEntries( deduped_26_1, 0 );
    deduped_22_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( range_1 ), deduped_23_1 );
    deduped_21_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( source_1 ), deduped_23_1 );
    deduped_20_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_18_1 := List( [ 0 .. Length( deduped_22_1 ) ], function ( i_2 )
            return Sum( deduped_22_1{[ 1 .. i_2 ]} );
        end );
    hoisted_16_1 := [ 1 .. Sum( deduped_22_1 ) ];
    deduped_13_1 := ZeroImmutable( deduped_28_1 );
    hoisted_12_1 := ListWithIdenticalEntries( deduped_26_1, deduped_29_1 );
    hoisted_9_1 := UnderlyingCategory( deduped_24_1 );
    hoisted_11_1 := List( deduped_25_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_24_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_9_1, IndexOfObject, i_2 ) );
        end );
    deduped_3_1 := ListOfObjectsOfUnderlyingCategory( ModelingCategory( deduped_27_1 ) );
    hoisted_6_1 := Concatenation( List( deduped_25_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_22_1[i_2], deduped_3_1[i_2] );
          end ) );
    hoisted_4_1 := Concatenation( List( deduped_25_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_21_1[i_2], deduped_3_1[i_2] );
          end ) );
    hoisted_17_1 := List( [ 1 .. Sum( deduped_21_1 ) ], function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := hoisted_4_1[i_2];
            return List( hoisted_16_1, function ( j_3 )
                    return CreateCapCategoryMorphismWithAttributes( deduped_24_1, hoisted_1_2, hoisted_6_1[j_3], Coefficient, Sum( List( list_of_morphisms_1, function ( x_4 )
                                local hoisted_1_4, deduped_2_4, hoisted_3_4;
                                hoisted_3_4 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( x_4 ), function ( pair_5 )
                                          local deduped_1_5, deduped_2_5;
                                          deduped_2_5 := pair_5[2];
                                          deduped_1_5 := hoisted_11_1[deduped_2_5];
                                          return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_5[1] ) ), function ( row_6 )
                                                    return List( row_6, function ( c_7 )
                                                            return CreateCapCategoryMorphismWithAttributes( deduped_24_1, deduped_1_5, deduped_1_5, Coefficient, c_7 );
                                                        end );
                                                end ), deduped_2_5 );
                                      end ), hoisted_12_1 );
                                deduped_2_4 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( x_4 ) ), deduped_23_1 );
                                hoisted_1_4 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( x_4 ) ), deduped_23_1 );
                                return Concatenation( List( deduped_25_1, function ( m_i_5 )
                                              local hoisted_1_5, hoisted_2_5, deduped_3_5, deduped_4_5;
                                              deduped_4_5 := CAP_JIT_INCOMPLETE_LOGIC( m_i_5 );
                                              deduped_3_5 := hoisted_1_4[deduped_4_5];
                                              hoisted_2_5 := Concatenation( List( [ m_i_5 + 1 .. deduped_26_1 ], function ( i_6 )
                                                        return ListWithIdenticalEntries( deduped_2_4[i_6], deduped_13_1 );
                                                    end ) );
                                              hoisted_1_5 := Concatenation( List( [ 1 .. m_i_5 - 1 ], function ( i_6 )
                                                        return ListWithIdenticalEntries( deduped_2_4[i_6], deduped_13_1 );
                                                    end ) );
                                              return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                                            if deduped_3_5 > 0 and deduped_2_4[deduped_4_5] = 0 then
                                                                return ListWithIdenticalEntries( deduped_3_5, deduped_29_1 );
                                                            else
                                                                return hoisted_3_4[deduped_4_5];
                                                            fi;
                                                            return;
                                                        end )(  ), function ( row_6 )
                                                        return Concatenation( hoisted_1_5, List( row_6, Coefficient ), hoisted_2_5 );
                                                    end ) );
                                          end ) )[i_2][j_3];
                            end ) ) );
                end );
        end );
    deduped_2_1 := List( [ 0 .. Length( deduped_21_1 ) ], function ( i_2 )
            return Sum( deduped_21_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, source_1, range_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_21_1, List( deduped_25_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_18_1[obj_idx_2] + 1 .. deduped_18_1[deduped_2_2] ];
                  return List( [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_17_1[nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_22_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                        return List( row_3, Coefficient );
                    end ), deduped_21_1[deduped_2_2], deduped_22_1[deduped_2_2], deduped_28_1 );
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_20_1, CreateCapCategoryObjectWithAttributes( deduped_20_1, RankOfObject, NumberRows( deduped_1_2 ) ), CreateCapCategoryObjectWithAttributes( deduped_20_1, RankOfObject, NumberColumns( deduped_1_2 ) ), UnderlyingMatrix, deduped_1_2 ), deduped_2_2 );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.SumOfMorphisms :=
        
########
function ( cat_1, source_1, list_of_morphisms_1, range_1 )
    local deduped_2_1, deduped_3_1, hoisted_4_1, hoisted_6_1, hoisted_9_1, hoisted_11_1, hoisted_12_1, deduped_13_1, hoisted_16_1, hoisted_17_1, deduped_18_1, deduped_19_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1;
    deduped_29_1 := [  ];
    deduped_28_1 := UnderlyingRing( cat_1 );
    deduped_27_1 := ModelingCategory( cat_1 );
    deduped_26_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_25_1 := [ 1 .. deduped_26_1 ];
    deduped_24_1 := UnderlyingCategory( deduped_27_1 );
    deduped_23_1 := ListWithIdenticalEntries( deduped_26_1, 0 );
    deduped_22_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( range_1 ), deduped_23_1 );
    deduped_21_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( source_1 ), deduped_23_1 );
    deduped_19_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_18_1 := List( [ 0 .. Length( deduped_22_1 ) ], function ( i_2 )
            return Sum( deduped_22_1{[ 1 .. i_2 ]} );
        end );
    hoisted_16_1 := [ 1 .. Sum( deduped_22_1 ) ];
    deduped_13_1 := ZeroImmutable( deduped_28_1 );
    hoisted_12_1 := ListWithIdenticalEntries( deduped_26_1, deduped_29_1 );
    hoisted_9_1 := UnderlyingCategory( deduped_24_1 );
    hoisted_11_1 := List( deduped_25_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_24_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_9_1, IndexOfObject, i_2 ) );
        end );
    deduped_3_1 := ListOfObjectsOfUnderlyingCategory( ModelingCategory( deduped_27_1 ) );
    hoisted_6_1 := Concatenation( List( deduped_25_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_22_1[i_2], deduped_3_1[i_2] );
          end ) );
    hoisted_4_1 := Concatenation( List( deduped_25_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_21_1[i_2], deduped_3_1[i_2] );
          end ) );
    hoisted_17_1 := List( [ 1 .. Sum( deduped_21_1 ) ], function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := hoisted_4_1[i_2];
            return List( hoisted_16_1, function ( j_3 )
                    return CreateCapCategoryMorphismWithAttributes( deduped_24_1, hoisted_1_2, hoisted_6_1[j_3], Coefficient, Sum( List( list_of_morphisms_1, function ( x_4 )
                                local hoisted_1_4, deduped_2_4, hoisted_3_4;
                                hoisted_3_4 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( x_4 ), function ( pair_5 )
                                          local deduped_1_5, deduped_2_5;
                                          deduped_2_5 := pair_5[2];
                                          deduped_1_5 := hoisted_11_1[deduped_2_5];
                                          return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_5[1] ) ), function ( row_6 )
                                                    return List( row_6, function ( c_7 )
                                                            return CreateCapCategoryMorphismWithAttributes( deduped_24_1, deduped_1_5, deduped_1_5, Coefficient, c_7 );
                                                        end );
                                                end ), deduped_2_5 );
                                      end ), hoisted_12_1 );
                                deduped_2_4 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( x_4 ) ), deduped_23_1 );
                                hoisted_1_4 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( x_4 ) ), deduped_23_1 );
                                return Concatenation( List( deduped_25_1, function ( m_i_5 )
                                              local hoisted_1_5, hoisted_2_5;
                                              hoisted_2_5 := Concatenation( List( [ m_i_5 + 1 .. deduped_26_1 ], function ( i_6 )
                                                        return ListWithIdenticalEntries( deduped_2_4[i_6], deduped_13_1 );
                                                    end ) );
                                              hoisted_1_5 := Concatenation( List( [ 1 .. m_i_5 - 1 ], function ( i_6 )
                                                        return ListWithIdenticalEntries( deduped_2_4[i_6], deduped_13_1 );
                                                    end ) );
                                              return List( deduped_25_1, function ( i_6 )
                                                        local deduped_1_6;
                                                        deduped_1_6 := hoisted_1_4[i_6];
                                                        return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                                                    if deduped_1_6 > 0 and deduped_2_4[i_6] = 0 then
                                                                        return ListWithIdenticalEntries( deduped_1_6, deduped_29_1 );
                                                                    else
                                                                        return hoisted_3_4[i_6];
                                                                    fi;
                                                                    return;
                                                                end )(  ), function ( row_7 )
                                                                return Concatenation( hoisted_1_5, List( row_7, Coefficient ), hoisted_2_5 );
                                                            end );
                                                    end )[m_i_5];
                                          end ) )[i_2][j_3];
                            end ) ) );
                end );
        end );
    deduped_2_1 := List( [ 0 .. Length( deduped_21_1 ) ], function ( i_2 )
            return Sum( deduped_21_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, source_1, range_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_21_1, List( deduped_25_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_18_1[obj_idx_2] + 1 .. deduped_18_1[deduped_2_2] ];
                  return List( [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_17_1[nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_22_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2, deduped_3_2;
              deduped_3_2 := pair_2[2];
              deduped_2_2 := deduped_22_1[deduped_3_2];
              deduped_1_2 := deduped_21_1[deduped_3_2];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_19_1, CreateCapCategoryObjectWithAttributes( deduped_19_1, RankOfObject, deduped_1_2 ), CreateCapCategoryObjectWithAttributes( deduped_19_1, RankOfObject, deduped_2_2 ), UnderlyingMatrix, HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                            return List( row_3, Coefficient );
                        end ), deduped_1_2, deduped_2_2, deduped_28_1 ) ), deduped_3_2 );
          end ) );
end
########
        
    ;
    
    ##
    AddUniversalMorphismFromDirectSumWithGivenDirectSum( cat,
        
########
function ( cat_1, objects_1, T_1, tau_1, P_1 )
    local deduped_2_1, hoisted_5_1, deduped_7_1, hoisted_8_1, deduped_9_1, hoisted_12_1, deduped_14_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1;
    deduped_24_1 := [  ];
    deduped_23_1 := UnderlyingRing( cat_1 );
    deduped_22_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_21_1 := [ 1 .. deduped_22_1 ];
    deduped_20_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
    deduped_19_1 := ListWithIdenticalEntries( deduped_22_1, 0 );
    deduped_18_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( T_1 ), deduped_19_1 );
    deduped_17_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( P_1 ), deduped_19_1 );
    deduped_16_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_14_1 := List( [ 0 .. Length( deduped_18_1 ) ], function ( i_2 )
            return Sum( deduped_18_1{[ 1 .. i_2 ]} );
        end );
    deduped_9_1 := ZeroImmutable( deduped_23_1 );
    hoisted_8_1 := ListWithIdenticalEntries( deduped_22_1, deduped_24_1 );
    hoisted_5_1 := UnderlyingCategory( deduped_20_1 );
    deduped_7_1 := List( deduped_21_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_20_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_5_1, IndexOfObject, i_2 ) );
        end );
    hoisted_12_1 := UnionOfRowsListList( Sum( deduped_18_1 ), List( tau_1, function ( x_2 )
              local hoisted_1_2, deduped_2_2, hoisted_3_2;
              hoisted_3_2 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( x_2 ), function ( pair_3 )
                        local deduped_1_3, deduped_2_3;
                        deduped_2_3 := pair_3[2];
                        deduped_1_3 := deduped_7_1[deduped_2_3];
                        return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_3[1] ) ), function ( row_4 )
                                  return List( row_4, function ( c_5 )
                                          return CreateCapCategoryMorphismWithAttributes( deduped_20_1, deduped_1_3, deduped_1_3, Coefficient, c_5 );
                                      end );
                              end ), deduped_2_3 );
                    end ), hoisted_8_1 );
              deduped_2_2 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( x_2 ) ), deduped_19_1 );
              hoisted_1_2 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( x_2 ) ), deduped_19_1 );
              return Concatenation( List( deduped_21_1, function ( m_i_3 )
                        local deduped_1_3, hoisted_2_3, hoisted_3_3, deduped_4_3, deduped_5_3;
                        deduped_5_3 := CAP_JIT_INCOMPLETE_LOGIC( m_i_3 );
                        deduped_4_3 := hoisted_1_2[deduped_5_3];
                        deduped_1_3 := deduped_7_1[m_i_3];
                        hoisted_3_3 := Concatenation( List( [ m_i_3 + 1 .. deduped_22_1 ], function ( i_4 )
                                  return ListWithIdenticalEntries( deduped_2_2[i_4], CreateCapCategoryMorphismWithAttributes( deduped_20_1, deduped_1_3, deduped_7_1[i_4], Coefficient, deduped_9_1 ) );
                              end ) );
                        hoisted_2_3 := Concatenation( List( [ 1 .. m_i_3 - 1 ], function ( i_4 )
                                  return ListWithIdenticalEntries( deduped_2_2[i_4], CreateCapCategoryMorphismWithAttributes( deduped_20_1, deduped_1_3, deduped_7_1[i_4], Coefficient, deduped_9_1 ) );
                              end ) );
                        return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                      if deduped_4_3 > 0 and deduped_2_2[deduped_5_3] = 0 then
                                          return ListWithIdenticalEntries( deduped_4_3, deduped_24_1 );
                                      else
                                          return hoisted_3_2[deduped_5_3];
                                      fi;
                                      return;
                                  end )(  ), function ( row_4 )
                                  return Concatenation( hoisted_2_3, row_4, hoisted_3_3 );
                              end ) );
                    end ) );
          end ) );
    deduped_2_1 := List( [ 0 .. Length( deduped_17_1 ) ], function ( i_2 )
            return Sum( deduped_17_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, P_1, T_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_17_1, List( deduped_21_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_14_1[obj_idx_2] + 1 .. deduped_14_1[deduped_2_2] ];
                  return List( [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_12_1[nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_18_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                        return List( row_3, Coefficient );
                    end ), deduped_17_1[deduped_2_2], deduped_18_1[deduped_2_2], deduped_23_1 );
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_16_1, CreateCapCategoryObjectWithAttributes( deduped_16_1, RankOfObject, NumberRows( deduped_1_2 ) ), CreateCapCategoryObjectWithAttributes( deduped_16_1, RankOfObject, NumberColumns( deduped_1_2 ) ), UnderlyingMatrix, deduped_1_2 ), deduped_2_2 );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.UniversalMorphismFromDirectSumWithGivenDirectSum :=
        
########
function ( cat_1, objects_1, T_1, tau_1, P_1 )
    local deduped_2_1, hoisted_5_1, deduped_7_1, hoisted_8_1, deduped_9_1, hoisted_12_1, deduped_14_1, deduped_15_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1;
    deduped_24_1 := [  ];
    deduped_23_1 := UnderlyingRing( cat_1 );
    deduped_22_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_21_1 := [ 1 .. deduped_22_1 ];
    deduped_20_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
    deduped_19_1 := ListWithIdenticalEntries( deduped_22_1, 0 );
    deduped_18_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( T_1 ), deduped_19_1 );
    deduped_17_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( P_1 ), deduped_19_1 );
    deduped_15_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_14_1 := List( [ 0 .. Length( deduped_18_1 ) ], function ( i_2 )
            return Sum( deduped_18_1{[ 1 .. i_2 ]} );
        end );
    deduped_9_1 := ZeroImmutable( deduped_23_1 );
    hoisted_8_1 := ListWithIdenticalEntries( deduped_22_1, deduped_24_1 );
    hoisted_5_1 := UnderlyingCategory( deduped_20_1 );
    deduped_7_1 := List( deduped_21_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_20_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_5_1, IndexOfObject, i_2 ) );
        end );
    hoisted_12_1 := UnionOfRowsListList( Sum( deduped_18_1 ), List( tau_1, function ( x_2 )
              local hoisted_1_2, deduped_2_2, hoisted_3_2;
              hoisted_3_2 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( x_2 ), function ( pair_3 )
                        local deduped_1_3, deduped_2_3;
                        deduped_2_3 := pair_3[2];
                        deduped_1_3 := deduped_7_1[deduped_2_3];
                        return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_3[1] ) ), function ( row_4 )
                                  return List( row_4, function ( c_5 )
                                          return CreateCapCategoryMorphismWithAttributes( deduped_20_1, deduped_1_3, deduped_1_3, Coefficient, c_5 );
                                      end );
                              end ), deduped_2_3 );
                    end ), hoisted_8_1 );
              deduped_2_2 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( x_2 ) ), deduped_19_1 );
              hoisted_1_2 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( x_2 ) ), deduped_19_1 );
              return Concatenation( List( deduped_21_1, function ( m_i_3 )
                        local deduped_1_3, hoisted_2_3, hoisted_3_3;
                        deduped_1_3 := deduped_7_1[m_i_3];
                        hoisted_3_3 := Concatenation( List( [ m_i_3 + 1 .. deduped_22_1 ], function ( i_4 )
                                  return ListWithIdenticalEntries( deduped_2_2[i_4], CreateCapCategoryMorphismWithAttributes( deduped_20_1, deduped_1_3, deduped_7_1[i_4], Coefficient, deduped_9_1 ) );
                              end ) );
                        hoisted_2_3 := Concatenation( List( [ 1 .. m_i_3 - 1 ], function ( i_4 )
                                  return ListWithIdenticalEntries( deduped_2_2[i_4], CreateCapCategoryMorphismWithAttributes( deduped_20_1, deduped_1_3, deduped_7_1[i_4], Coefficient, deduped_9_1 ) );
                              end ) );
                        return List( deduped_21_1, function ( i_4 )
                                  local deduped_1_4;
                                  deduped_1_4 := hoisted_1_2[i_4];
                                  return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                              if deduped_1_4 > 0 and deduped_2_2[i_4] = 0 then
                                                  return ListWithIdenticalEntries( deduped_1_4, deduped_24_1 );
                                              else
                                                  return hoisted_3_2[i_4];
                                              fi;
                                              return;
                                          end )(  ), function ( row_5 )
                                          return Concatenation( hoisted_2_3, row_5, hoisted_3_3 );
                                      end );
                              end )[m_i_3];
                    end ) );
          end ) );
    deduped_2_1 := List( [ 0 .. Length( deduped_17_1 ) ], function ( i_2 )
            return Sum( deduped_17_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, P_1, T_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_17_1, List( deduped_21_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_14_1[obj_idx_2] + 1 .. deduped_14_1[deduped_2_2] ];
                  return List( [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_12_1[nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_18_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2, deduped_3_2;
              deduped_3_2 := pair_2[2];
              deduped_2_2 := deduped_18_1[deduped_3_2];
              deduped_1_2 := deduped_17_1[deduped_3_2];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_15_1, CreateCapCategoryObjectWithAttributes( deduped_15_1, RankOfObject, deduped_1_2 ), CreateCapCategoryObjectWithAttributes( deduped_15_1, RankOfObject, deduped_2_2 ), UnderlyingMatrix, HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                            return List( row_3, Coefficient );
                        end ), deduped_1_2, deduped_2_2, deduped_23_1 ) ), deduped_3_2 );
          end ) );
end
########
        
    ;
    
    ##
    AddUniversalMorphismIntoDirectSumWithGivenDirectSum( cat,
        
########
function ( cat_1, objects_1, T_1, tau_1, P_1 )
    local deduped_2_1, hoisted_5_1, deduped_7_1, hoisted_8_1, deduped_9_1, hoisted_12_1, deduped_14_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1;
    deduped_24_1 := [  ];
    deduped_23_1 := UnderlyingRing( cat_1 );
    deduped_22_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_21_1 := [ 1 .. deduped_22_1 ];
    deduped_20_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
    deduped_19_1 := ListWithIdenticalEntries( deduped_22_1, 0 );
    deduped_18_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( P_1 ), deduped_19_1 );
    deduped_17_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( T_1 ), deduped_19_1 );
    deduped_16_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_14_1 := List( [ 0 .. Length( deduped_18_1 ) ], function ( i_2 )
            return Sum( deduped_18_1{[ 1 .. i_2 ]} );
        end );
    deduped_9_1 := ZeroImmutable( deduped_23_1 );
    hoisted_8_1 := ListWithIdenticalEntries( deduped_22_1, deduped_24_1 );
    hoisted_5_1 := UnderlyingCategory( deduped_20_1 );
    deduped_7_1 := List( deduped_21_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_20_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_5_1, IndexOfObject, i_2 ) );
        end );
    hoisted_12_1 := UnionOfColumnsListList( Sum( deduped_17_1 ), List( tau_1, function ( x_2 )
              local hoisted_1_2, deduped_2_2, hoisted_3_2;
              hoisted_3_2 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( x_2 ), function ( pair_3 )
                        local deduped_1_3, deduped_2_3;
                        deduped_2_3 := pair_3[2];
                        deduped_1_3 := deduped_7_1[deduped_2_3];
                        return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_3[1] ) ), function ( row_4 )
                                  return List( row_4, function ( c_5 )
                                          return CreateCapCategoryMorphismWithAttributes( deduped_20_1, deduped_1_3, deduped_1_3, Coefficient, c_5 );
                                      end );
                              end ), deduped_2_3 );
                    end ), hoisted_8_1 );
              deduped_2_2 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( x_2 ) ), deduped_19_1 );
              hoisted_1_2 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( x_2 ) ), deduped_19_1 );
              return Concatenation( List( deduped_21_1, function ( m_i_3 )
                        local deduped_1_3, hoisted_2_3, hoisted_3_3, deduped_4_3, deduped_5_3;
                        deduped_5_3 := CAP_JIT_INCOMPLETE_LOGIC( m_i_3 );
                        deduped_4_3 := hoisted_1_2[deduped_5_3];
                        deduped_1_3 := deduped_7_1[m_i_3];
                        hoisted_3_3 := Concatenation( List( [ m_i_3 + 1 .. deduped_22_1 ], function ( i_4 )
                                  return ListWithIdenticalEntries( deduped_2_2[i_4], CreateCapCategoryMorphismWithAttributes( deduped_20_1, deduped_1_3, deduped_7_1[i_4], Coefficient, deduped_9_1 ) );
                              end ) );
                        hoisted_2_3 := Concatenation( List( [ 1 .. m_i_3 - 1 ], function ( i_4 )
                                  return ListWithIdenticalEntries( deduped_2_2[i_4], CreateCapCategoryMorphismWithAttributes( deduped_20_1, deduped_1_3, deduped_7_1[i_4], Coefficient, deduped_9_1 ) );
                              end ) );
                        return CAP_JIT_INCOMPLETE_LOGIC( List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                      if deduped_4_3 > 0 and deduped_2_2[deduped_5_3] = 0 then
                                          return ListWithIdenticalEntries( deduped_4_3, deduped_24_1 );
                                      else
                                          return hoisted_3_2[deduped_5_3];
                                      fi;
                                      return;
                                  end )(  ), function ( row_4 )
                                  return Concatenation( hoisted_2_3, row_4, hoisted_3_3 );
                              end ) );
                    end ) );
          end ) );
    deduped_2_1 := List( [ 0 .. Length( deduped_17_1 ) ], function ( i_2 )
            return Sum( deduped_17_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, T_1, P_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_17_1, List( deduped_21_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_14_1[obj_idx_2] + 1 .. deduped_14_1[deduped_2_2] ];
                  return List( [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_12_1[nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_18_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              deduped_1_2 := HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                        return List( row_3, Coefficient );
                    end ), deduped_17_1[deduped_2_2], deduped_18_1[deduped_2_2], deduped_23_1 );
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_16_1, CreateCapCategoryObjectWithAttributes( deduped_16_1, RankOfObject, NumberRows( deduped_1_2 ) ), CreateCapCategoryObjectWithAttributes( deduped_16_1, RankOfObject, NumberColumns( deduped_1_2 ) ), UnderlyingMatrix, deduped_1_2 ), deduped_2_2 );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.UniversalMorphismIntoDirectSumWithGivenDirectSum :=
        
########
function ( cat_1, objects_1, T_1, tau_1, P_1 )
    local deduped_2_1, hoisted_5_1, deduped_7_1, hoisted_8_1, deduped_9_1, hoisted_12_1, deduped_14_1, deduped_15_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1;
    deduped_24_1 := [  ];
    deduped_23_1 := UnderlyingRing( cat_1 );
    deduped_22_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_21_1 := [ 1 .. deduped_22_1 ];
    deduped_20_1 := UnderlyingCategory( ModelingCategory( cat_1 ) );
    deduped_19_1 := ListWithIdenticalEntries( deduped_22_1, 0 );
    deduped_18_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( P_1 ), deduped_19_1 );
    deduped_17_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( T_1 ), deduped_19_1 );
    deduped_15_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_14_1 := List( [ 0 .. Length( deduped_18_1 ) ], function ( i_2 )
            return Sum( deduped_18_1{[ 1 .. i_2 ]} );
        end );
    deduped_9_1 := ZeroImmutable( deduped_23_1 );
    hoisted_8_1 := ListWithIdenticalEntries( deduped_22_1, deduped_24_1 );
    hoisted_5_1 := UnderlyingCategory( deduped_20_1 );
    deduped_7_1 := List( deduped_21_1, function ( i_2 )
            return CreateCapCategoryObjectWithAttributes( deduped_20_1, UnderlyingOriginalObject, CreateCapCategoryObjectWithAttributes( hoisted_5_1, IndexOfObject, i_2 ) );
        end );
    hoisted_12_1 := UnionOfColumnsListList( Sum( deduped_17_1 ), List( tau_1, function ( x_2 )
              local hoisted_1_2, deduped_2_2, hoisted_3_2;
              hoisted_3_2 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList( cat_1, List( ListOfPairsOfMorphismAndIndex( x_2 ), function ( pair_3 )
                        local deduped_1_3, deduped_2_3;
                        deduped_2_3 := pair_3[2];
                        deduped_1_3 := deduped_7_1[deduped_2_3];
                        return NTuple( 2, List( EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( pair_3[1] ) ), function ( row_4 )
                                  return List( row_4, function ( c_5 )
                                          return CreateCapCategoryMorphismWithAttributes( deduped_20_1, deduped_1_3, deduped_1_3, Coefficient, c_5 );
                                      end );
                              end ), deduped_2_3 );
                    end ), hoisted_8_1 );
              deduped_2_2 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Range( x_2 ) ), deduped_19_1 );
              hoisted_1_2 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( Source( x_2 ) ), deduped_19_1 );
              return Concatenation( List( deduped_21_1, function ( m_i_3 )
                        local deduped_1_3, hoisted_2_3, hoisted_3_3;
                        deduped_1_3 := deduped_7_1[m_i_3];
                        hoisted_3_3 := Concatenation( List( [ m_i_3 + 1 .. deduped_22_1 ], function ( i_4 )
                                  return ListWithIdenticalEntries( deduped_2_2[i_4], CreateCapCategoryMorphismWithAttributes( deduped_20_1, deduped_1_3, deduped_7_1[i_4], Coefficient, deduped_9_1 ) );
                              end ) );
                        hoisted_2_3 := Concatenation( List( [ 1 .. m_i_3 - 1 ], function ( i_4 )
                                  return ListWithIdenticalEntries( deduped_2_2[i_4], CreateCapCategoryMorphismWithAttributes( deduped_20_1, deduped_1_3, deduped_7_1[i_4], Coefficient, deduped_9_1 ) );
                              end ) );
                        return List( deduped_21_1, function ( i_4 )
                                  local deduped_1_4;
                                  deduped_1_4 := hoisted_1_2[i_4];
                                  return List( CAP_JIT_EXPR_CASE_WRAPPER( function (  )
                                              if deduped_1_4 > 0 and deduped_2_2[i_4] = 0 then
                                                  return ListWithIdenticalEntries( deduped_1_4, deduped_24_1 );
                                              else
                                                  return hoisted_3_2[i_4];
                                              fi;
                                              return;
                                          end )(  ), function ( row_5 )
                                          return Concatenation( hoisted_2_3, row_5, hoisted_3_3 );
                                      end );
                              end )[m_i_3];
                    end ) );
          end ) );
    deduped_2_1 := List( [ 0 .. Length( deduped_17_1 ) ], function ( i_2 )
            return Sum( deduped_17_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, T_1, P_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_17_1, List( deduped_21_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_14_1[obj_idx_2] + 1 .. deduped_14_1[deduped_2_2] ];
                  return List( [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_12_1[nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_18_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2, deduped_3_2;
              deduped_3_2 := pair_2[2];
              deduped_2_2 := deduped_18_1[deduped_3_2];
              deduped_1_2 := deduped_17_1[deduped_3_2];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_15_1, CreateCapCategoryObjectWithAttributes( deduped_15_1, RankOfObject, deduped_1_2 ), CreateCapCategoryObjectWithAttributes( deduped_15_1, RankOfObject, deduped_2_2 ), UnderlyingMatrix, HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                            return List( row_3, Coefficient );
                        end ), deduped_1_2, deduped_2_2, deduped_23_1 ) ), deduped_3_2 );
          end ) );
end
########
        
    ;
    
    ##
    AddZeroMorphism( cat,
        
########
function ( cat_1, a_1, b_1 )
    local deduped_2_1, deduped_3_1, hoisted_4_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, hoisted_9_1, hoisted_10_1, deduped_11_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1;
    deduped_20_1 := UnderlyingRing( cat_1 );
    deduped_19_1 := ModelingCategory( cat_1 );
    deduped_18_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_17_1 := [ 1 .. deduped_18_1 ];
    deduped_16_1 := ListWithIdenticalEntries( deduped_18_1, 0 );
    deduped_15_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( b_1 ), deduped_16_1 );
    deduped_14_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( a_1 ), deduped_16_1 );
    deduped_13_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_11_1 := List( [ 0 .. Length( deduped_15_1 ) ], function ( i_2 )
            return Sum( deduped_15_1{[ 1 .. i_2 ]} );
        end );
    hoisted_9_1 := [ 1 .. Sum( deduped_15_1 ) ];
    hoisted_8_1 := ZeroImmutable( deduped_20_1 );
    hoisted_7_1 := UnderlyingCategory( deduped_19_1 );
    deduped_3_1 := ListOfObjectsOfUnderlyingCategory( ModelingCategory( deduped_19_1 ) );
    hoisted_6_1 := Concatenation( List( deduped_17_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_15_1[i_2], deduped_3_1[i_2] );
          end ) );
    hoisted_4_1 := Concatenation( List( deduped_17_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_14_1[i_2], deduped_3_1[i_2] );
          end ) );
    hoisted_10_1 := List( [ 1 .. Sum( deduped_14_1 ) ], function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := hoisted_4_1[i_2];
            return List( hoisted_9_1, function ( j_3 )
                    return CreateCapCategoryMorphismWithAttributes( hoisted_7_1, hoisted_1_2, hoisted_6_1[j_3], Coefficient, hoisted_8_1 );
                end );
        end );
    deduped_2_1 := List( [ 0 .. Length( deduped_14_1 ) ], function ( i_2 )
            return Sum( deduped_14_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, a_1, b_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_14_1, List( deduped_17_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_11_1[obj_idx_2] + 1 .. deduped_11_1[deduped_2_2] ];
                  return List( [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_10_1[nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_15_1 ), function ( pair_2 )
              local morphism_attr_1_2, deduped_2_2;
              deduped_2_2 := pair_2[2];
              morphism_attr_1_2 := HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                        return List( row_3, Coefficient );
                    end ), deduped_14_1[deduped_2_2], deduped_15_1[deduped_2_2], deduped_20_1 );
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_13_1, CreateCapCategoryObjectWithAttributes( deduped_13_1, RankOfObject, NumberRows( morphism_attr_1_2 ) ), CreateCapCategoryObjectWithAttributes( deduped_13_1, RankOfObject, NumberColumns( morphism_attr_1_2 ) ), UnderlyingMatrix, morphism_attr_1_2 ), deduped_2_2 );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.ZeroMorphism :=
        
########
function ( cat_1, a_1, b_1 )
    local deduped_2_1, deduped_3_1, hoisted_4_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, hoisted_9_1, hoisted_10_1, deduped_11_1, deduped_12_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1;
    deduped_20_1 := UnderlyingRing( cat_1 );
    deduped_19_1 := ModelingCategory( cat_1 );
    deduped_18_1 := NrOfSummandsOfCoproduct( cat_1 );
    deduped_17_1 := [ 1 .. deduped_18_1 ];
    deduped_16_1 := ListWithIdenticalEntries( deduped_18_1, 0 );
    deduped_15_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( b_1 ), deduped_16_1 );
    deduped_14_1 := COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList( cat_1, ListOfPairsOfObjectAndIndex( a_1 ), deduped_16_1 );
    deduped_12_1 := UnderlyingCategoryOfRows( cat_1 );
    deduped_11_1 := List( [ 0 .. Length( deduped_15_1 ) ], function ( i_2 )
            return Sum( deduped_15_1{[ 1 .. i_2 ]} );
        end );
    hoisted_9_1 := [ 1 .. Sum( deduped_15_1 ) ];
    hoisted_8_1 := ZeroImmutable( deduped_20_1 );
    hoisted_7_1 := UnderlyingCategory( deduped_19_1 );
    deduped_3_1 := ListOfObjectsOfUnderlyingCategory( ModelingCategory( deduped_19_1 ) );
    hoisted_6_1 := Concatenation( List( deduped_17_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_15_1[i_2], deduped_3_1[i_2] );
          end ) );
    hoisted_4_1 := Concatenation( List( deduped_17_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_14_1[i_2], deduped_3_1[i_2] );
          end ) );
    hoisted_10_1 := List( [ 1 .. Sum( deduped_14_1 ) ], function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := hoisted_4_1[i_2];
            return List( hoisted_9_1, function ( j_3 )
                    return CreateCapCategoryMorphismWithAttributes( hoisted_7_1, hoisted_1_2, hoisted_6_1[j_3], Coefficient, hoisted_8_1 );
                end );
        end );
    deduped_2_1 := List( [ 0 .. Length( deduped_14_1 ) ], function ( i_2 )
            return Sum( deduped_14_1{[ 1 .. i_2 ]} );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, a_1, b_1, ListOfPairsOfMorphismAndIndex, List( COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList( cat_1, deduped_14_1, List( deduped_17_1, function ( obj_idx_2 )
                  local hoisted_1_2, deduped_2_2;
                  deduped_2_2 := obj_idx_2 + 1;
                  hoisted_1_2 := [ deduped_11_1[obj_idx_2] + 1 .. deduped_11_1[deduped_2_2] ];
                  return List( [ deduped_2_1[obj_idx_2] + 1 .. deduped_2_1[deduped_2_2] ], function ( nr_rows_3 )
                          return hoisted_10_1[nr_rows_3]{hoisted_1_2};
                      end );
              end ), deduped_15_1 ), function ( pair_2 )
              local deduped_1_2, deduped_2_2, deduped_3_2;
              deduped_3_2 := pair_2[2];
              deduped_2_2 := deduped_15_1[deduped_3_2];
              deduped_1_2 := deduped_14_1[deduped_3_2];
              return NTuple( 2, CreateCapCategoryMorphismWithAttributes( deduped_12_1, CreateCapCategoryObjectWithAttributes( deduped_12_1, RankOfObject, deduped_1_2 ), CreateCapCategoryObjectWithAttributes( deduped_12_1, RankOfObject, deduped_2_2 ), UnderlyingMatrix, HomalgMatrixListList( List( pair_2[1], function ( row_3 )
                            return List( row_3, Coefficient );
                        end ), deduped_1_2, deduped_2_2, deduped_20_1 ) ), deduped_3_2 );
          end ) );
end
########
        
    ;
    
    ##
    AddZeroObject( cat,
        
########
function ( cat_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, ListOfPairsOfObjectAndIndex, COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseObjectListToSparseList( cat_1, ListWithIdenticalEntries( NrOfSummandsOfCoproduct( cat_1 ), 0 ) ) );
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
