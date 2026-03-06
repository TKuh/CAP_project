# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Implementations
#
BindGlobal( "ADD_FUNCTIONS_FOR_SkeletalCategoryOfGroupRepresentations_S4_Q_precompiled", function ( cat )
    
    ##
    AddRightDistributivityExpanding( cat,
        
########
function ( cat_1, L_1, a_1 )
    local deduped_2_1, deduped_4_1, deduped_6_1, hoisted_7_1, hoisted_8_1, deduped_9_1, hoisted_13_1, deduped_14_1, deduped_15_1, hoisted_16_1, deduped_17_1, hoisted_20_1, hoisted_22_1, deduped_23_1, hoisted_25_1, hoisted_26_1, hoisted_28_1, deduped_29_1, deduped_30_1, deduped_31_1, deduped_32_1, deduped_33_1, deduped_34_1, deduped_35_1, deduped_36_1, deduped_37_1, deduped_38_1, deduped_39_1, deduped_40_1, deduped_41_1, deduped_42_1, deduped_43_1, deduped_44_1;
    deduped_44_1 := BigInt( 0 );
    deduped_43_1 := UnderlyingIrreducibleCharacters( cat_1 );
    deduped_42_1 := TripleOfNrSupportListOfSupportListOfRanks( a_1 );
    deduped_41_1 := [ 1 .. Length( L_1 ) ];
    deduped_40_1 := NTuple( 2, deduped_44_1, CapJitTypedExpression( [  ], function (  )
              return rec(
                  filter := IsList,
                  element_type := rec(
                      filter := IsNTuple,
                      element_types := [ rec(
                              filter := IsInt ), rec(
                              filter := IsInt ) ] ) );
          end ) );
    deduped_39_1 := deduped_42_1[1];
    deduped_38_1 := [ 1 .. deduped_39_1 ];
    deduped_37_1 := Union( List( L_1, function ( x_2 )
              return TripleOfNrSupportListOfSupportListOfRanks( x_2 )[2];
          end ) );
    deduped_36_1 := Length( deduped_37_1 );
    deduped_35_1 := [ 1 .. deduped_36_1 ];
    deduped_4_1 := [ 1 .. IndexOfTrivialCharacterInListOfIrreducibleCharacters( cat_1 ) ];
    deduped_2_1 := deduped_42_1[2];
    deduped_34_1 := Union( List( deduped_35_1, function ( i_2 )
              local hoisted_1_2;
              hoisted_1_2 := deduped_37_1[i_2];
              return Union( List( deduped_38_1, function ( j_3 )
                        local hoisted_1_3;
                        hoisted_1_3 := deduped_2_1[j_3];
                        return Filtered( deduped_4_1, function ( k_4 )
                                return not CAP_JIT_INCOMPLETE_LOGIC( IsZero( SGREPS_ScalarProduct( deduped_43_1, CAP_JIT_INCOMPLETE_LOGIC( k_4 ), hoisted_1_2, hoisted_1_3 ) ) );
                            end );
                    end ) );
          end ) );
    deduped_33_1 := Union2( deduped_34_1, deduped_34_1 );
    deduped_32_1 := Length( deduped_34_1 );
    deduped_31_1 := Length( deduped_33_1 );
    hoisted_8_1 := deduped_42_1[3];
    deduped_9_1 := List( deduped_38_1, function ( n_2 )
            return hoisted_8_1[n_2];
        end );
    deduped_6_1 := [ 0 ];
    hoisted_7_1 := List( deduped_35_1, function ( n_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_37_1[CAP_JIT_INCOMPLETE_LOGIC( n_2 )];
            return CAP_JIT_INCOMPLETE_LOGIC( Sum( List( L_1, function ( x_3 )
                        local hoisted_1_3, deduped_2_3, deduped_3_3;
                        deduped_3_3 := TripleOfNrSupportListOfSupportListOfRanks( x_3 );
                        deduped_2_3 := deduped_3_3[2];
                        hoisted_1_3 := deduped_3_3[3];
                        return [ deduped_6_1, List( [ 1 .. deduped_3_3[1] ], function ( n_4 )
                                          return hoisted_1_3[n_4];
                                      end ){Positions( deduped_2_3, deduped_1_2 )} ][BooleanToInteger( deduped_1_2 in deduped_2_3 ) + 1][1];
                    end ) ) );
        end );
    deduped_30_1 := List( [ 1 .. deduped_32_1 ], function ( n_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_34_1[CAP_JIT_INCOMPLETE_LOGIC( n_2 )];
            return CAP_JIT_INCOMPLETE_LOGIC( Sum( List( deduped_35_1, function ( i_3 )
                        local deduped_1_3, hoisted_2_3, deduped_4_3;
                        deduped_1_3 := deduped_37_1[i_3];
                        deduped_4_3 := Union( List( deduped_38_1, function ( j_4 )
                                  local hoisted_1_4;
                                  hoisted_1_4 := deduped_2_1[j_4];
                                  return Filtered( deduped_4_1, function ( k_5 )
                                          return not CAP_JIT_INCOMPLETE_LOGIC( IsZero( SGREPS_ScalarProduct( deduped_43_1, CAP_JIT_INCOMPLETE_LOGIC( k_5 ), deduped_1_3, hoisted_1_4 ) ) );
                                      end );
                              end ) );
                        hoisted_2_3 := hoisted_7_1[i_3];
                        return [ deduped_6_1, List( [ 1 .. Length( deduped_4_3 ) ], function ( n_4 )
                                          local deduped_1_4;
                                          deduped_1_4 := deduped_4_3[CAP_JIT_INCOMPLETE_LOGIC( n_4 )];
                                          return CAP_JIT_INCOMPLETE_LOGIC( Sum( List( deduped_38_1, function ( j_5 )
                                                      local deduped_1_5, hoisted_3_5, deduped_4_5;
                                                      deduped_1_5 := deduped_2_1[j_5];
                                                      deduped_4_5 := Filtered( deduped_4_1, function ( k_6 )
                                                              return not CAP_JIT_INCOMPLETE_LOGIC( IsZero( SGREPS_ScalarProduct( deduped_43_1, CAP_JIT_INCOMPLETE_LOGIC( k_6 ), deduped_1_3, deduped_1_5 ) ) );
                                                          end );
                                                      hoisted_3_5 := hoisted_2_3 * deduped_9_1[j_5];
                                                      return [ deduped_6_1, List( [ 1 .. Length( deduped_4_5 ) ], function ( n_6 )
                                                                        return CAP_JIT_INCOMPLETE_LOGIC( CAP_JIT_INCOMPLETE_LOGIC( SGREPS_ScalarProduct( deduped_43_1, CAP_JIT_INCOMPLETE_LOGIC( deduped_4_5[CAP_JIT_INCOMPLETE_LOGIC( n_6 )] ), deduped_1_3, deduped_1_5 ) ) * hoisted_3_5 );
                                                                    end ){Positions( deduped_4_5, deduped_1_4 )} ][BooleanToInteger( deduped_1_4 in deduped_4_5 ) + 1][1];
                                                  end ) ) );
                                      end ){Positions( deduped_4_3, deduped_1_2 )} ][BooleanToInteger( deduped_1_2 in deduped_4_3 ) + 1][1];
                    end ) ) );
        end );
    deduped_29_1 := CreateCapCategoryObjectWithAttributes( cat_1, TripleOfNrSupportListOfSupportListOfRanks, NTuple( 3, deduped_32_1, deduped_34_1, deduped_30_1 ) );
    hoisted_28_1 := [ deduped_40_1 ];
    deduped_15_1 := [ deduped_44_1 ];
    hoisted_25_1 := NTuple( 3, deduped_36_1, deduped_37_1, List( deduped_35_1, function ( n_2 )
              local deduped_1_2;
              deduped_1_2 := deduped_37_1[CAP_JIT_INCOMPLETE_LOGIC( n_2 )];
              return CAP_JIT_INCOMPLETE_LOGIC( Sum( List( deduped_41_1, function ( i_3 )
                          local hoisted_1_3, deduped_2_3, deduped_3_3;
                          deduped_3_3 := TripleOfNrSupportListOfSupportListOfRanks( CAP_JIT_INCOMPLETE_LOGIC( L_1[i_3] ) );
                          deduped_2_3 := deduped_3_3[2];
                          hoisted_1_3 := deduped_3_3[3];
                          return CAP_JIT_INCOMPLETE_LOGIC( [ deduped_15_1, List( [ 1 .. deduped_3_3[1] ], function ( n_4 )
                                              return hoisted_1_3[n_4];
                                          end ){Positions( deduped_2_3, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_2_3 )][1] );
                      end ) ) );
          end ) );
    hoisted_26_1 := List( deduped_41_1, function ( i_2 )
            return hoisted_25_1;
        end );
    deduped_23_1 := List( deduped_38_1, function ( n_2 )
            return deduped_9_1[n_2];
        end );
    deduped_17_1 := BigInt( 1 );
    hoisted_22_1 := List( deduped_38_1, function ( n_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_9_1[CAP_JIT_INCOMPLETE_LOGIC( n_2 )];
            return CAP_JIT_INCOMPLETE_LOGIC( [ NTuple( 2, deduped_17_1, [ NTuple( 2, deduped_17_1, deduped_1_2 ) ] ), deduped_40_1 ][1 + BooleanToInteger( deduped_1_2 = 0 )] );
        end );
    hoisted_20_1 := List( deduped_41_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := [ 1 .. i_2 - 1 ];
            return NTuple( 3, deduped_36_1, deduped_37_1, List( deduped_35_1, function ( n_3 )
                      local deduped_1_3, deduped_2_3, deduped_3_3, deduped_4_3;
                      deduped_1_3 := deduped_37_1[CAP_JIT_INCOMPLETE_LOGIC( n_3 )];
                      deduped_4_3 := List( L_1, function ( object_4 )
                              local hoisted_1_4, deduped_2_4, deduped_3_4;
                              deduped_3_4 := TripleOfNrSupportListOfSupportListOfRanks( object_4 );
                              deduped_2_4 := deduped_3_4[2];
                              hoisted_1_4 := deduped_3_4[3];
                              return [ deduped_15_1, List( [ 1 .. deduped_3_4[1] ], function ( n_5 )
                                                return hoisted_1_4[n_5];
                                            end ){Positions( deduped_2_4, deduped_1_3 )} ][1 + BooleanToInteger( deduped_1_3 in deduped_2_4 )][1];
                          end );
                      deduped_3_3 := deduped_4_3[i_2];
                      deduped_2_3 := Sum( deduped_4_3{hoisted_1_2} );
                      return CAP_JIT_INCOMPLETE_LOGIC( [ NTuple( 2, deduped_17_1, [ NTuple( 2, deduped_2_3 + 1, deduped_2_3 + deduped_3_3 ) ] ), deduped_40_1 ][1 + BooleanToInteger( deduped_3_3 = 0 )] );
                  end ) );
        end );
    deduped_14_1 := [ 1 .. Length( deduped_43_1 ) ];
    hoisted_16_1 := List( deduped_41_1, function ( i_2 )
            local deduped_1_2, hoisted_2_2, hoisted_3_2, deduped_6_2, deduped_7_2, deduped_8_2, deduped_9_2;
            deduped_9_2 := CAP_JIT_INCOMPLETE_LOGIC( TripleOfNrSupportListOfSupportListOfRanks( CAP_JIT_INCOMPLETE_LOGIC( L_1[i_2] ) ) );
            deduped_8_2 := [ 1 .. deduped_9_2[1] ];
            deduped_1_2 := deduped_9_2[2];
            deduped_7_2 := Union( List( deduped_8_2, function ( i_3 )
                      local hoisted_1_3;
                      hoisted_1_3 := deduped_1_2[i_3];
                      return Union( List( deduped_38_1, function ( j_4 )
                                local hoisted_1_4, hoisted_2_4;
                                hoisted_1_4 := deduped_2_1[j_4];
                                hoisted_2_4 := List( deduped_4_1, function ( k_5 )
                                        return IsZero( SGREPS_ScalarProduct( deduped_43_1, k_5, hoisted_1_3, hoisted_1_4 ) );
                                    end );
                                return Filtered( deduped_14_1, function ( i_5 )
                                        return not hoisted_2_4[i_5];
                                    end );
                            end ) );
                  end ) );
            deduped_6_2 := Length( deduped_7_2 );
            hoisted_2_2 := deduped_9_2[3];
            hoisted_3_2 := List( deduped_8_2, function ( n_3 )
                    return hoisted_2_2[n_3];
                end );
            return NTuple( 3, deduped_6_2, deduped_7_2, List( [ 1 .. deduped_6_2 ], function ( n_3 )
                      local deduped_1_3;
                      deduped_1_3 := deduped_7_2[CAP_JIT_INCOMPLETE_LOGIC( n_3 )];
                      return CAP_JIT_INCOMPLETE_LOGIC( Sum( List( deduped_8_2, function ( i_4 )
                                  local deduped_1_4, hoisted_2_4, deduped_4_4, deduped_5_4;
                                  deduped_5_4 := CAP_JIT_INCOMPLETE_LOGIC( i_4 );
                                  deduped_1_4 := deduped_1_2[deduped_5_4];
                                  deduped_4_4 := Union( List( deduped_38_1, function ( j_5 )
                                            local hoisted_1_5, hoisted_2_5;
                                            hoisted_1_5 := deduped_2_1[j_5];
                                            hoisted_2_5 := List( deduped_4_1, function ( k_6 )
                                                    return IsZero( SGREPS_ScalarProduct( deduped_43_1, k_6, deduped_1_4, hoisted_1_5 ) );
                                                end );
                                            return Filtered( deduped_14_1, function ( i_6 )
                                                    return not hoisted_2_5[i_6];
                                                end );
                                        end ) );
                                  hoisted_2_4 := hoisted_3_2[deduped_5_4];
                                  return CAP_JIT_INCOMPLETE_LOGIC( [ deduped_15_1, List( [ 1 .. Length( deduped_4_4 ) ], function ( n_5 )
                                                      local deduped_1_5;
                                                      deduped_1_5 := deduped_4_4[CAP_JIT_INCOMPLETE_LOGIC( n_5 )];
                                                      return CAP_JIT_INCOMPLETE_LOGIC( Sum( List( deduped_38_1, function ( i_6 )
                                                                  local deduped_1_6, hoisted_2_6, hoisted_3_6, hoisted_4_6, deduped_5_6, deduped_6_6;
                                                                  deduped_6_6 := CAP_JIT_INCOMPLETE_LOGIC( i_6 );
                                                                  deduped_1_6 := deduped_2_1[deduped_6_6];
                                                                  hoisted_2_6 := List( deduped_4_1, function ( k_7 )
                                                                          return IsZero( SGREPS_ScalarProduct( deduped_43_1, k_7, deduped_1_4, deduped_1_6 ) );
                                                                      end );
                                                                  deduped_5_6 := Filtered( deduped_14_1, function ( i_7 )
                                                                          return not hoisted_2_6[i_7];
                                                                      end );
                                                                  hoisted_4_6 := hoisted_2_4 * deduped_9_1[deduped_6_6];
                                                                  hoisted_3_6 := List( deduped_4_1, function ( k_7 )
                                                                            return SGREPS_ScalarProduct( deduped_43_1, k_7, deduped_1_4, deduped_1_6 );
                                                                        end ){deduped_5_6};
                                                                  return CAP_JIT_INCOMPLETE_LOGIC( [ deduped_15_1, List( [ 1 .. Length( deduped_5_6 ) ], function ( n_7 )
                                                                                      return CAP_JIT_INCOMPLETE_LOGIC( hoisted_3_6[CAP_JIT_INCOMPLETE_LOGIC( n_7 )] * hoisted_4_6 );
                                                                                  end ){Positions( deduped_5_6, deduped_1_5 )} ][1 + BooleanToInteger( deduped_1_5 in deduped_5_6 )][1] );
                                                              end ) ) );
                                                  end ){Positions( deduped_4_4, deduped_1_3 )} ][1 + BooleanToInteger( deduped_1_3 in deduped_4_4 )][1] );
                              end ) ) );
                  end ) );
        end );
    hoisted_13_1 := UnderlyingSplittingField( cat_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_29_1, deduped_29_1, TripleOfNrSupportListOfSupportListOfMatrices, NTuple( 3, deduped_31_1, deduped_33_1, List( [ 1 .. deduped_31_1 ], function ( i_2 )
                local deduped_1_2, deduped_2_2, hoisted_3_2, deduped_4_2;
                deduped_1_2 := deduped_33_1[CAP_JIT_INCOMPLETE_LOGIC( i_2 )];
                deduped_2_2 := List( deduped_41_1, function ( i_3 )
                        local hoisted_2_3, hoisted_3_3, deduped_5_3, hoisted_6_3, hoisted_7_3, hoisted_8_3, hoisted_9_3, hoisted_12_3, deduped_13_3, deduped_14_3, deduped_15_3, deduped_16_3, deduped_17_3, deduped_18_3;
                        deduped_18_3 := hoisted_26_1[i_3];
                        deduped_17_3 := hoisted_20_1[i_3];
                        deduped_16_3 := [ 1 .. deduped_17_3[1] ];
                        deduped_15_3 := Union2( deduped_34_1, hoisted_16_1[i_3][2] );
                        deduped_14_3 := List( deduped_16_3, function ( i_4 )
                                return deduped_39_1;
                            end );
                        deduped_13_3 := deduped_14_3[1];
                        hoisted_12_3 := List( deduped_16_3, function ( i_4 )
                                return deduped_13_3;
                            end );
                        hoisted_9_3 := [ 1 .. deduped_13_3 ];
                        hoisted_6_3 := deduped_18_3[3];
                        hoisted_7_3 := List( [ 1 .. deduped_18_3[1] ], function ( n_4 )
                                return hoisted_6_3[n_4];
                            end );
                        hoisted_8_3 := List( deduped_16_3, function ( i_4 )
                                local hoisted_1_4;
                                hoisted_1_4 := CAP_JIT_INCOMPLETE_LOGIC( hoisted_7_3[CAP_JIT_INCOMPLETE_LOGIC( i_4 )] );
                                return List( deduped_38_1, function ( j_5 )
                                        return hoisted_1_4 * deduped_23_1[j_5];
                                    end );
                            end );
                        deduped_5_3 := deduped_17_3[2];
                        hoisted_2_3 := deduped_17_3[3];
                        hoisted_3_3 := List( deduped_16_3, function ( i_4 )
                                local deduped_1_4, hoisted_2_4, deduped_4_4, deduped_5_4;
                                deduped_5_4 := CAP_JIT_INCOMPLETE_LOGIC( hoisted_2_3[CAP_JIT_INCOMPLETE_LOGIC( i_4 )] );
                                deduped_4_4 := [ 1 .. deduped_5_4[1] ];
                                deduped_1_4 := deduped_5_4[2];
                                hoisted_2_4 := Sum( List( deduped_4_4, function ( i_5 )
                                          local deduped_1_5;
                                          deduped_1_5 := deduped_1_4[i_5];
                                          return deduped_1_5[2] - deduped_1_5[1] + deduped_17_1;
                                      end ) );
                                return List( deduped_38_1, function ( j_5 )
                                        local hoisted_1_5, hoisted_2_5, hoisted_3_5, deduped_4_5, deduped_5_5;
                                        deduped_5_5 := hoisted_22_1[j_5];
                                        deduped_4_5 := deduped_5_5[1];
                                        hoisted_3_5 := [ 1 .. deduped_4_5 ];
                                        hoisted_2_5 := deduped_23_1[j_5];
                                        hoisted_1_5 := deduped_5_5[2];
                                        return NTuple( 2, hoisted_2_4 * deduped_4_5, Concatenation( List( deduped_4_4, function ( i_6 )
                                                    local deduped_1_6;
                                                    deduped_1_6 := deduped_1_4[i_6];
                                                    return Concatenation( List( [ deduped_1_6[1] .. deduped_1_6[2] ], function ( j_7 )
                                                              local deduped_1_7;
                                                              deduped_1_7 := hoisted_2_5 * (j_7 - 1);
                                                              return List( hoisted_3_5, function ( k_8 )
                                                                      local deduped_1_8;
                                                                      deduped_1_8 := hoisted_1_5[k_8];
                                                                      return NTuple( 2, deduped_1_8[1] + deduped_1_7, deduped_1_8[2] + deduped_1_7 );
                                                                  end );
                                                          end ) );
                                                end ) ) );
                                    end );
                            end );
                        return [ hoisted_28_1, List( [ 1 .. Length( deduped_15_3 ) ], function ( n_4 )
                                          local deduped_1_4, deduped_2_4, deduped_3_4, hoisted_4_4;
                                          deduped_1_4 := deduped_15_3[CAP_JIT_INCOMPLETE_LOGIC( n_4 )];
                                          deduped_2_4 := List( deduped_16_3, function ( i_5 )
                                                  local hoisted_1_5, hoisted_2_5, hoisted_3_5, deduped_4_5;
                                                  deduped_4_5 := CAP_JIT_INCOMPLETE_LOGIC( i_5 );
                                                  hoisted_2_5 := deduped_5_3[deduped_4_5];
                                                  hoisted_1_5 := hoisted_8_3[deduped_4_5];
                                                  hoisted_3_5 := CAP_JIT_INCOMPLETE_LOGIC( List( deduped_38_1, function ( j_6 )
                                                            return hoisted_1_5[j_6] * SGREPS_ScalarProduct( deduped_43_1, deduped_1_4, hoisted_2_5, deduped_2_1[j_6] );
                                                        end ) );
                                                  return List( hoisted_9_3, function ( j_6 )
                                                          return hoisted_3_5[j_6];
                                                      end );
                                              end );
                                          hoisted_4_4 := List( deduped_16_3, function ( i_5 )
                                                  local hoisted_1_5, deduped_2_5;
                                                  deduped_2_5 := CAP_JIT_INCOMPLETE_LOGIC( i_5 );
                                                  hoisted_1_5 := deduped_2_4[deduped_2_5];
                                                  return CAP_JIT_INCOMPLETE_LOGIC( Sum( List( [ 1 .. hoisted_12_3[deduped_2_5] ], function ( i_6 )
                                                              return hoisted_1_5[i_6];
                                                          end ) ) );
                                              end );
                                          deduped_3_4 := List( deduped_16_3, function ( i_5 )
                                                  local hoisted_1_5, hoisted_2_5, deduped_3_5, hoisted_4_5, deduped_5_5, deduped_6_5;
                                                  deduped_6_5 := CAP_JIT_INCOMPLETE_LOGIC( i_5 );
                                                  deduped_5_5 := [ 1 .. deduped_14_3[i_5] ];
                                                  hoisted_4_5 := deduped_2_4[i_5];
                                                  hoisted_2_5 := deduped_5_3[deduped_6_5];
                                                  hoisted_1_5 := hoisted_3_3[deduped_6_5];
                                                  deduped_3_5 := CAP_JIT_INCOMPLETE_LOGIC( List( deduped_38_1, function ( j_6 )
                                                            local deduped_1_6, hoisted_2_6, hoisted_4_6, deduped_5_6, deduped_6_6, deduped_7_6, deduped_8_6, deduped_9_6;
                                                            deduped_9_6 := hoisted_1_5[j_6];
                                                            deduped_8_6 := SGREPS_ScalarProduct( deduped_43_1, deduped_1_4, hoisted_2_5, deduped_2_1[j_6] );
                                                            deduped_7_6 := [ 1 .. deduped_9_6[1] ];
                                                            deduped_6_6 := [ NTuple( 2, deduped_17_1, [ NTuple( 2, deduped_17_1, deduped_8_6 ) ] ), deduped_40_1 ][1 + BooleanToInteger( deduped_8_6 = 0 )];
                                                            deduped_5_6 := deduped_6_6[1];
                                                            hoisted_4_6 := [ 1 .. deduped_5_6 ];
                                                            hoisted_2_6 := deduped_6_6[2];
                                                            deduped_1_6 := deduped_9_6[2];
                                                            return NTuple( 2, Sum( List( deduped_7_6, function ( i_7 )
                                                                          local deduped_1_7;
                                                                          deduped_1_7 := deduped_1_6[i_7];
                                                                          return deduped_1_7[2] - deduped_1_7[1] + deduped_17_1;
                                                                      end ) ) * deduped_5_6, Concatenation( List( deduped_7_6, function ( i_7 )
                                                                        local deduped_1_7;
                                                                        deduped_1_7 := deduped_1_6[i_7];
                                                                        return Concatenation( List( [ deduped_1_7[1] .. deduped_1_7[2] ], function ( j_8 )
                                                                                  local deduped_1_8;
                                                                                  deduped_1_8 := deduped_8_6 * (j_8 - 1);
                                                                                  return List( hoisted_4_6, function ( k_9 )
                                                                                          local deduped_1_9;
                                                                                          deduped_1_9 := hoisted_2_6[k_9];
                                                                                          return NTuple( 2, deduped_1_9[1] + deduped_1_8, deduped_1_9[2] + deduped_1_8 );
                                                                                      end );
                                                                              end ) );
                                                                    end ) ) );
                                                        end ) );
                                                  return NTuple( 2, Sum( List( deduped_5_5, function ( i_6 )
                                                              return deduped_3_5[i_6][1];
                                                          end ) ), Concatenation( List( deduped_5_5, function ( i_6 )
                                                              local deduped_1_6;
                                                              deduped_1_6 := Sum( List( [ 1 .. i_6 - 1 ], function ( j_7 )
                                                                        return hoisted_4_5[j_7];
                                                                    end ) );
                                                              return List( deduped_3_5[i_6][2], function ( col_7 )
                                                                      return NTuple( 2, col_7[1] + deduped_1_6, col_7[2] + deduped_1_6 );
                                                                  end );
                                                          end ) ) );
                                              end );
                                          return CAP_JIT_INCOMPLETE_LOGIC( NTuple( 2, Sum( List( deduped_16_3, function ( i_5 )
                                                        return deduped_3_4[i_5][1];
                                                    end ) ), Concatenation( List( deduped_16_3, function ( i_5 )
                                                        local deduped_1_5;
                                                        deduped_1_5 := Sum( List( [ 1 .. i_5 - 1 ], function ( j_6 )
                                                                  return hoisted_4_4[j_6];
                                                              end ) );
                                                        return List( deduped_3_4[i_5][2], function ( col_6 )
                                                                return NTuple( 2, col_6[1] + deduped_1_5, col_6[2] + deduped_1_5 );
                                                            end );
                                                    end ) ) ) );
                                      end ){Positions( deduped_15_3, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_15_3 )][1];
                    end );
                deduped_4_2 := CAP_JIT_INCOMPLETE_LOGIC( NTuple( 2, Sum( List( deduped_41_1, function ( i_3 )
                              return deduped_2_2[i_3][1];
                          end ) ), Concatenation( List( deduped_41_1, function ( i_3 )
                              return deduped_2_2[i_3][2];
                          end ) ) ) );
                hoisted_3_2 := deduped_4_2[2];
                return CertainColumns( HomalgIdentityMatrix( deduped_30_1[i_2], hoisted_13_1 ), Concatenation( List( [ 1 .. deduped_4_2[1] ], function ( j_3 )
                            local deduped_1_3;
                            deduped_1_3 := hoisted_3_2[j_3];
                            return [ deduped_1_3[1] .. deduped_1_3[2] ];
                        end ) ) );
            end ) ) );
end
########
        
    , 301 : IsPrecompiledDerivation := true );
    
    ##
    cat!.cached_precompiled_functions.RightDistributivityExpanding :=
        
########
function ( cat_1, L_1, a_1 )
    local deduped_2_1, deduped_4_1, deduped_6_1, hoisted_7_1, hoisted_8_1, hoisted_9_1, hoisted_10_1, deduped_11_1, hoisted_14_1, hoisted_16_1, hoisted_17_1, deduped_18_1, deduped_19_1, hoisted_20_1, deduped_21_1, hoisted_24_1, hoisted_26_1, hoisted_27_1, hoisted_28_1, deduped_29_1, hoisted_31_1, hoisted_32_1, hoisted_33_1, hoisted_35_1, hoisted_36_1, hoisted_37_1, deduped_38_1, deduped_39_1, deduped_40_1, deduped_41_1, deduped_42_1, deduped_43_1, deduped_44_1, deduped_45_1, deduped_46_1, deduped_47_1, deduped_48_1, deduped_49_1, deduped_50_1, deduped_51_1, deduped_52_1, deduped_53_1, deduped_54_1, deduped_55_1;
    deduped_55_1 := BigInt( 0 );
    deduped_54_1 := UnderlyingIrreducibleCharacters( cat_1 );
    deduped_53_1 := TripleOfNrSupportListOfSupportListOfRanks( a_1 );
    deduped_52_1 := [ 1 .. Length( L_1 ) ];
    deduped_51_1 := NTuple( 2, deduped_55_1, CapJitTypedExpression( [  ], function (  )
              return rec(
                  filter := IsList,
                  element_type := rec(
                      filter := IsNTuple,
                      element_types := [ rec(
                              filter := IsInt ), rec(
                              filter := IsInt ) ] ) );
          end ) );
    deduped_50_1 := deduped_53_1[1];
    deduped_49_1 := [ 1 .. deduped_50_1 ];
    deduped_48_1 := Union( List( L_1, function ( x_2 )
              return TripleOfNrSupportListOfSupportListOfRanks( x_2 )[2];
          end ) );
    deduped_47_1 := Length( deduped_48_1 );
    deduped_46_1 := [ 1 .. deduped_47_1 ];
    deduped_4_1 := [ 1 .. IndexOfTrivialCharacterInListOfIrreducibleCharacters( cat_1 ) ];
    deduped_2_1 := deduped_53_1[2];
    deduped_45_1 := Union( List( deduped_46_1, function ( i_2 )
              local hoisted_1_2;
              hoisted_1_2 := deduped_48_1[i_2];
              return Union( List( deduped_49_1, function ( j_3 )
                        local hoisted_1_3, hoisted_2_3;
                        hoisted_1_3 := deduped_2_1[j_3];
                        hoisted_2_3 := List( deduped_4_1, function ( k_4 )
                                return IsZero( SGREPS_ScalarProduct( deduped_54_1, k_4, hoisted_1_2, hoisted_1_3 ) );
                            end );
                        return Filtered( deduped_4_1, function ( k_4 )
                                return not hoisted_2_3[k_4];
                            end );
                    end ) );
          end ) );
    deduped_44_1 := Union2( deduped_45_1, deduped_45_1 );
    deduped_43_1 := Length( deduped_45_1 );
    deduped_42_1 := [ 1 .. deduped_43_1 ];
    deduped_41_1 := Length( deduped_44_1 );
    deduped_40_1 := [ 1 .. deduped_41_1 ];
    hoisted_10_1 := deduped_53_1[3];
    deduped_11_1 := List( deduped_49_1, function ( n_2 )
            return hoisted_10_1[n_2];
        end );
    deduped_6_1 := [ 0 ];
    hoisted_7_1 := List( deduped_46_1, function ( n_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_48_1[n_2];
            return Sum( List( L_1, function ( x_3 )
                      local hoisted_1_3, deduped_2_3, deduped_3_3;
                      deduped_3_3 := TripleOfNrSupportListOfSupportListOfRanks( x_3 );
                      deduped_2_3 := deduped_3_3[2];
                      hoisted_1_3 := deduped_3_3[3];
                      return [ deduped_6_1, List( [ 1 .. deduped_3_3[1] ], function ( n_4 )
                                        return hoisted_1_3[n_4];
                                    end ){Positions( deduped_2_3, deduped_1_2 )} ][BooleanToInteger( deduped_1_2 in deduped_2_3 ) + 1][1];
                  end ) );
        end );
    hoisted_8_1 := List( deduped_46_1, function ( n_2 )
            return hoisted_7_1[n_2];
        end );
    hoisted_9_1 := List( deduped_46_1, function ( n_2 )
            return hoisted_8_1[n_2];
        end );
    hoisted_14_1 := List( deduped_42_1, function ( n_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_45_1[n_2];
            return Sum( List( deduped_46_1, function ( i_3 )
                      local deduped_1_3, hoisted_2_3, hoisted_4_3, hoisted_5_3, deduped_6_3, deduped_7_3;
                      deduped_1_3 := deduped_48_1[i_3];
                      deduped_7_3 := Union( List( deduped_49_1, function ( j_4 )
                                local hoisted_1_4, hoisted_2_4;
                                hoisted_1_4 := deduped_2_1[j_4];
                                hoisted_2_4 := List( deduped_4_1, function ( k_5 )
                                        return IsZero( SGREPS_ScalarProduct( deduped_54_1, k_5, deduped_1_3, hoisted_1_4 ) );
                                    end );
                                return Filtered( deduped_4_1, function ( k_5 )
                                        return not hoisted_2_4[k_5];
                                    end );
                            end ) );
                      deduped_6_3 := [ 1 .. Length( deduped_7_3 ) ];
                      hoisted_2_3 := hoisted_9_1[i_3];
                      hoisted_4_3 := List( deduped_6_3, function ( n_4 )
                              local deduped_1_4;
                              deduped_1_4 := deduped_7_3[n_4];
                              return Sum( List( deduped_49_1, function ( j_5 )
                                        local deduped_1_5, hoisted_2_5, hoisted_3_5, hoisted_4_5, hoisted_5_5, hoisted_6_5, hoisted_7_5, deduped_8_5, deduped_9_5;
                                        deduped_1_5 := deduped_2_1[j_5];
                                        hoisted_2_5 := List( deduped_4_1, function ( k_6 )
                                                return IsZero( SGREPS_ScalarProduct( deduped_54_1, k_6, deduped_1_3, deduped_1_5 ) );
                                            end );
                                        deduped_9_5 := Filtered( deduped_4_1, function ( k_6 )
                                                return not hoisted_2_5[k_6];
                                            end );
                                        deduped_8_5 := [ 1 .. Length( deduped_9_5 ) ];
                                        hoisted_5_5 := hoisted_2_3 * deduped_11_1[j_5];
                                        hoisted_3_5 := List( deduped_4_1, function ( k_6 )
                                                return SGREPS_ScalarProduct( deduped_54_1, k_6, deduped_1_3, deduped_1_5 );
                                            end );
                                        hoisted_4_5 := List( deduped_9_5, function ( k_6 )
                                                return hoisted_3_5[k_6];
                                            end );
                                        hoisted_6_5 := List( deduped_8_5, function ( n_6 )
                                                return hoisted_4_5[n_6] * hoisted_5_5;
                                            end );
                                        hoisted_7_5 := List( deduped_8_5, function ( n_6 )
                                                return hoisted_6_5[n_6];
                                            end );
                                        return [ deduped_6_1, List( deduped_8_5, function ( n_6 )
                                                          return hoisted_7_5[n_6];
                                                      end ){Positions( deduped_9_5, deduped_1_4 )} ][BooleanToInteger( deduped_1_4 in deduped_9_5 ) + 1][1];
                                    end ) );
                          end );
                      hoisted_5_3 := List( deduped_6_3, function ( n_4 )
                              return hoisted_4_3[n_4];
                          end );
                      return [ deduped_6_1, List( deduped_6_3, function ( n_4 )
                                        return hoisted_5_3[n_4];
                                    end ){Positions( deduped_7_3, deduped_1_2 )} ][BooleanToInteger( deduped_1_2 in deduped_7_3 ) + 1][1];
                  end ) );
        end );
    deduped_39_1 := List( deduped_42_1, function ( n_2 )
            return hoisted_14_1[n_2];
        end );
    deduped_38_1 := CreateCapCategoryObjectWithAttributes( cat_1, TripleOfNrSupportListOfSupportListOfRanks, NTuple( 3, deduped_43_1, deduped_45_1, deduped_39_1 ) );
    hoisted_35_1 := [ deduped_51_1 ];
    deduped_19_1 := [ deduped_55_1 ];
    hoisted_31_1 := List( deduped_46_1, function ( n_2 )
            local deduped_1_2, hoisted_2_2;
            deduped_1_2 := deduped_48_1[n_2];
            hoisted_2_2 := List( L_1, function ( object_3 )
                    local hoisted_1_3, deduped_2_3, deduped_3_3;
                    deduped_3_3 := TripleOfNrSupportListOfSupportListOfRanks( object_3 );
                    deduped_2_3 := deduped_3_3[2];
                    hoisted_1_3 := deduped_3_3[3];
                    return [ deduped_19_1, List( [ 1 .. deduped_3_3[1] ], function ( n_4 )
                                      return hoisted_1_3[n_4];
                                  end ){Positions( deduped_2_3, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_2_3 )][1];
                end );
            return Sum( List( deduped_52_1, function ( i_3 )
                      return hoisted_2_2[i_3];
                  end ) );
        end );
    hoisted_32_1 := NTuple( 3, deduped_47_1, deduped_48_1, List( deduped_46_1, function ( n_2 )
              return hoisted_31_1[n_2];
          end ) );
    hoisted_33_1 := List( deduped_52_1, function ( i_2 )
            return hoisted_32_1;
        end );
    deduped_29_1 := List( deduped_49_1, function ( n_2 )
            return deduped_11_1[n_2];
        end );
    deduped_21_1 := BigInt( 1 );
    hoisted_26_1 := List( deduped_49_1, function ( n_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_11_1[n_2];
            return [ NTuple( 2, deduped_21_1, [ NTuple( 2, deduped_21_1, deduped_1_2 ) ] ), deduped_51_1 ][1 + BooleanToInteger( deduped_1_2 = 0 )];
        end );
    hoisted_27_1 := List( deduped_49_1, function ( n_2 )
            return hoisted_26_1[n_2];
        end );
    hoisted_28_1 := List( deduped_49_1, function ( n_2 )
            return hoisted_27_1[n_2];
        end );
    hoisted_24_1 := List( deduped_52_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2;
            hoisted_1_2 := [ 1 .. i_2 - 1 ];
            hoisted_2_2 := List( deduped_46_1, function ( i_3 )
                    local deduped_1_3, deduped_2_3, deduped_3_3, deduped_4_3;
                    deduped_1_3 := deduped_48_1[i_3];
                    deduped_4_3 := List( L_1, function ( object_4 )
                            local hoisted_1_4, deduped_2_4, deduped_3_4;
                            deduped_3_4 := TripleOfNrSupportListOfSupportListOfRanks( object_4 );
                            deduped_2_4 := deduped_3_4[2];
                            hoisted_1_4 := deduped_3_4[3];
                            return [ deduped_19_1, List( [ 1 .. deduped_3_4[1] ], function ( n_5 )
                                              return hoisted_1_4[n_5];
                                          end ){Positions( deduped_2_4, deduped_1_3 )} ][1 + BooleanToInteger( deduped_1_3 in deduped_2_4 )][1];
                        end );
                    deduped_3_3 := deduped_4_3[i_2];
                    deduped_2_3 := Sum( deduped_4_3{hoisted_1_2} );
                    return [ NTuple( 2, deduped_21_1, [ NTuple( 2, deduped_2_3 + 1, deduped_2_3 + deduped_3_3 ) ] ), deduped_51_1 ][1 + BooleanToInteger( deduped_3_3 = 0 )];
                end );
            return NTuple( 3, deduped_47_1, deduped_48_1, List( deduped_46_1, function ( n_3 )
                      return hoisted_2_2[n_3];
                  end ) );
        end );
    deduped_18_1 := [ 1 .. Length( deduped_54_1 ) ];
    hoisted_17_1 := List( L_1, TripleOfNrSupportListOfSupportListOfRanks );
    hoisted_20_1 := List( deduped_52_1, function ( i_2 )
            local deduped_1_2, hoisted_2_2, hoisted_3_2, hoisted_6_2, deduped_7_2, deduped_8_2, deduped_9_2, deduped_10_2, deduped_11_2;
            deduped_11_2 := hoisted_17_1[i_2];
            deduped_10_2 := [ 1 .. deduped_11_2[1] ];
            deduped_1_2 := deduped_11_2[2];
            deduped_9_2 := Union( List( deduped_10_2, function ( i_3 )
                      local hoisted_1_3;
                      hoisted_1_3 := deduped_1_2[i_3];
                      return Union( List( deduped_49_1, function ( j_4 )
                                local hoisted_1_4, hoisted_2_4;
                                hoisted_1_4 := deduped_2_1[j_4];
                                hoisted_2_4 := List( deduped_4_1, function ( k_5 )
                                        return IsZero( SGREPS_ScalarProduct( deduped_54_1, k_5, hoisted_1_3, hoisted_1_4 ) );
                                    end );
                                return Filtered( deduped_18_1, function ( i_5 )
                                        return not hoisted_2_4[i_5];
                                    end );
                            end ) );
                  end ) );
            deduped_8_2 := Length( deduped_9_2 );
            deduped_7_2 := [ 1 .. deduped_8_2 ];
            hoisted_2_2 := deduped_11_2[3];
            hoisted_3_2 := List( deduped_10_2, function ( n_3 )
                    return hoisted_2_2[n_3];
                end );
            hoisted_6_2 := List( deduped_7_2, function ( n_3 )
                    local deduped_1_3, hoisted_2_3;
                    deduped_1_3 := deduped_9_2[n_3];
                    hoisted_2_3 := List( deduped_10_2, function ( i_4 )
                            local deduped_1_4, hoisted_2_4, hoisted_4_4, hoisted_5_4, deduped_6_4, deduped_7_4;
                            deduped_1_4 := deduped_1_2[i_4];
                            deduped_7_4 := Union( List( deduped_49_1, function ( j_5 )
                                      local hoisted_1_5, hoisted_2_5;
                                      hoisted_1_5 := deduped_2_1[j_5];
                                      hoisted_2_5 := List( deduped_4_1, function ( k_6 )
                                              return IsZero( SGREPS_ScalarProduct( deduped_54_1, k_6, deduped_1_4, hoisted_1_5 ) );
                                          end );
                                      return Filtered( deduped_18_1, function ( i_6 )
                                              return not hoisted_2_5[i_6];
                                          end );
                                  end ) );
                            deduped_6_4 := [ 1 .. Length( deduped_7_4 ) ];
                            hoisted_2_4 := hoisted_3_2[i_4];
                            hoisted_4_4 := List( deduped_6_4, function ( n_5 )
                                    local deduped_1_5, hoisted_2_5;
                                    deduped_1_5 := deduped_7_4[n_5];
                                    hoisted_2_5 := List( deduped_49_1, function ( j_6 )
                                            local deduped_1_6, hoisted_2_6, hoisted_3_6, hoisted_4_6, hoisted_5_6, hoisted_6_6, deduped_7_6, deduped_8_6;
                                            deduped_1_6 := deduped_2_1[j_6];
                                            hoisted_2_6 := List( deduped_4_1, function ( k_7 )
                                                    return IsZero( SGREPS_ScalarProduct( deduped_54_1, k_7, deduped_1_4, deduped_1_6 ) );
                                                end );
                                            deduped_8_6 := Filtered( deduped_18_1, function ( i_7 )
                                                    return not hoisted_2_6[i_7];
                                                end );
                                            deduped_7_6 := [ 1 .. Length( deduped_8_6 ) ];
                                            hoisted_4_6 := hoisted_2_4 * deduped_11_1[j_6];
                                            hoisted_3_6 := List( deduped_4_1, function ( k_7 )
                                                      return SGREPS_ScalarProduct( deduped_54_1, k_7, deduped_1_4, deduped_1_6 );
                                                  end ){deduped_8_6};
                                            hoisted_5_6 := List( deduped_7_6, function ( n_7 )
                                                    return hoisted_3_6[n_7] * hoisted_4_6;
                                                end );
                                            hoisted_6_6 := List( deduped_7_6, function ( n_7 )
                                                    return hoisted_5_6[n_7];
                                                end );
                                            return [ deduped_19_1, List( deduped_7_6, function ( n_7 )
                                                              return hoisted_6_6[n_7];
                                                          end ){Positions( deduped_8_6, deduped_1_5 )} ][1 + BooleanToInteger( deduped_1_5 in deduped_8_6 )][1];
                                        end );
                                    return Sum( List( deduped_49_1, function ( i_6 )
                                              return hoisted_2_5[i_6];
                                          end ) );
                                end );
                            hoisted_5_4 := List( deduped_6_4, function ( n_5 )
                                    return hoisted_4_4[n_5];
                                end );
                            return [ deduped_19_1, List( deduped_6_4, function ( n_5 )
                                              return hoisted_5_4[n_5];
                                          end ){Positions( deduped_7_4, deduped_1_3 )} ][1 + BooleanToInteger( deduped_1_3 in deduped_7_4 )][1];
                        end );
                    return Sum( List( deduped_10_2, function ( i_4 )
                              return hoisted_2_3[i_4];
                          end ) );
                end );
            return NTuple( 3, deduped_8_2, deduped_9_2, List( deduped_7_2, function ( n_3 )
                      return hoisted_6_2[n_3];
                  end ) );
        end );
    hoisted_36_1 := List( deduped_40_1, function ( n_2 )
            local deduped_1_2, deduped_2_2;
            deduped_1_2 := deduped_44_1[n_2];
            deduped_2_2 := List( deduped_52_1, function ( i_3 )
                    local hoisted_2_3, hoisted_3_3, hoisted_4_3, deduped_6_3, hoisted_8_3, hoisted_9_3, hoisted_10_3, hoisted_11_3, hoisted_12_3, hoisted_14_3, hoisted_15_3, hoisted_16_3, deduped_17_3, deduped_18_3, deduped_19_3, deduped_20_3, deduped_21_3, deduped_22_3, deduped_23_3;
                    deduped_23_3 := hoisted_33_1[i_3];
                    deduped_22_3 := hoisted_24_1[i_3];
                    deduped_21_3 := [ 1 .. deduped_22_3[1] ];
                    deduped_20_3 := Union2( deduped_45_1, hoisted_20_1[i_3][2] );
                    deduped_19_3 := List( deduped_21_3, function ( i_4 )
                            return deduped_50_1;
                        end );
                    deduped_18_3 := [ 1 .. Length( deduped_20_3 ) ];
                    deduped_17_3 := deduped_19_3[1];
                    hoisted_14_3 := List( deduped_21_3, function ( i_4 )
                            return deduped_17_3;
                        end );
                    hoisted_12_3 := [ 1 .. deduped_17_3 ];
                    hoisted_8_3 := deduped_23_3[3];
                    hoisted_9_3 := List( [ 1 .. deduped_23_3[1] ], function ( n_4 )
                            return hoisted_8_3[n_4];
                        end );
                    hoisted_10_3 := List( deduped_21_3, function ( n_4 )
                            return hoisted_9_3[n_4];
                        end );
                    hoisted_11_3 := List( deduped_21_3, function ( i_4 )
                            local hoisted_1_4;
                            hoisted_1_4 := hoisted_10_3[i_4];
                            return List( deduped_49_1, function ( j_5 )
                                    return hoisted_1_4 * deduped_29_1[j_5];
                                end );
                        end );
                    deduped_6_3 := deduped_22_3[2];
                    hoisted_2_3 := deduped_22_3[3];
                    hoisted_3_3 := List( deduped_21_3, function ( n_4 )
                            return hoisted_2_3[n_4];
                        end );
                    hoisted_4_3 := List( deduped_21_3, function ( i_4 )
                            local deduped_1_4, hoisted_2_4, deduped_4_4, deduped_5_4;
                            deduped_5_4 := hoisted_3_3[i_4];
                            deduped_4_4 := [ 1 .. deduped_5_4[1] ];
                            deduped_1_4 := deduped_5_4[2];
                            hoisted_2_4 := Sum( List( deduped_4_4, function ( i_5 )
                                      local deduped_1_5;
                                      deduped_1_5 := deduped_1_4[i_5];
                                      return deduped_1_5[2] - deduped_1_5[1] + deduped_21_1;
                                  end ) );
                            return List( deduped_49_1, function ( j_5 )
                                    local hoisted_1_5, hoisted_2_5, hoisted_3_5, deduped_4_5, deduped_5_5;
                                    deduped_5_5 := hoisted_28_1[j_5];
                                    deduped_4_5 := deduped_5_5[1];
                                    hoisted_3_5 := [ 1 .. deduped_4_5 ];
                                    hoisted_2_5 := deduped_29_1[j_5];
                                    hoisted_1_5 := deduped_5_5[2];
                                    return NTuple( 2, hoisted_2_4 * deduped_4_5, Concatenation( List( deduped_4_4, function ( i_6 )
                                                local deduped_1_6;
                                                deduped_1_6 := deduped_1_4[i_6];
                                                return Concatenation( List( [ deduped_1_6[1] .. deduped_1_6[2] ], function ( j_7 )
                                                          local deduped_1_7;
                                                          deduped_1_7 := hoisted_2_5 * (j_7 - 1);
                                                          return List( hoisted_3_5, function ( k_8 )
                                                                  local deduped_1_8;
                                                                  deduped_1_8 := hoisted_1_5[k_8];
                                                                  return NTuple( 2, deduped_1_8[1] + deduped_1_7, deduped_1_8[2] + deduped_1_7 );
                                                              end );
                                                      end ) );
                                            end ) ) );
                                end );
                        end );
                    hoisted_15_3 := List( deduped_18_3, function ( k_4 )
                            local deduped_1_4, hoisted_2_4, hoisted_3_4, deduped_4_4, deduped_5_4, hoisted_6_4, hoisted_7_4;
                            deduped_1_4 := deduped_20_3[k_4];
                            hoisted_3_4 := List( deduped_21_3, function ( i_5 )
                                    local hoisted_1_5, hoisted_2_5;
                                    hoisted_2_5 := deduped_6_3[i_5];
                                    hoisted_1_5 := hoisted_11_3[i_5];
                                    return List( deduped_49_1, function ( j_6 )
                                            return hoisted_1_5[j_6] * SGREPS_ScalarProduct( deduped_54_1, deduped_1_4, hoisted_2_5, deduped_2_1[j_6] );
                                        end );
                                end );
                            deduped_4_4 := List( deduped_21_3, function ( i_5 )
                                    local hoisted_1_5;
                                    hoisted_1_5 := hoisted_3_4[i_5];
                                    return List( hoisted_12_3, function ( j_6 )
                                            return hoisted_1_5[j_6];
                                        end );
                                end );
                            hoisted_6_4 := List( deduped_21_3, function ( i_5 )
                                    local hoisted_1_5;
                                    hoisted_1_5 := deduped_4_4[i_5];
                                    return Sum( List( [ 1 .. hoisted_14_3[i_5] ], function ( i_6 )
                                              return hoisted_1_5[i_6];
                                          end ) );
                                end );
                            hoisted_7_4 := List( deduped_21_3, function ( i_5 )
                                    return hoisted_6_4[i_5];
                                end );
                            hoisted_2_4 := List( deduped_21_3, function ( i_5 )
                                    local hoisted_1_5, hoisted_2_5;
                                    hoisted_2_5 := deduped_6_3[i_5];
                                    hoisted_1_5 := hoisted_4_3[i_5];
                                    return List( deduped_49_1, function ( j_6 )
                                            local deduped_1_6, hoisted_2_6, hoisted_4_6, deduped_5_6, deduped_6_6, deduped_7_6, deduped_8_6, deduped_9_6;
                                            deduped_9_6 := hoisted_1_5[j_6];
                                            deduped_8_6 := SGREPS_ScalarProduct( deduped_54_1, deduped_1_4, hoisted_2_5, deduped_2_1[j_6] );
                                            deduped_7_6 := [ 1 .. deduped_9_6[1] ];
                                            deduped_6_6 := [ NTuple( 2, deduped_21_1, [ NTuple( 2, deduped_21_1, deduped_8_6 ) ] ), deduped_51_1 ][1 + BooleanToInteger( deduped_8_6 = 0 )];
                                            deduped_5_6 := deduped_6_6[1];
                                            hoisted_4_6 := [ 1 .. deduped_5_6 ];
                                            hoisted_2_6 := deduped_6_6[2];
                                            deduped_1_6 := deduped_9_6[2];
                                            return NTuple( 2, Sum( List( deduped_7_6, function ( i_7 )
                                                          local deduped_1_7;
                                                          deduped_1_7 := deduped_1_6[i_7];
                                                          return deduped_1_7[2] - deduped_1_7[1] + deduped_21_1;
                                                      end ) ) * deduped_5_6, Concatenation( List( deduped_7_6, function ( i_7 )
                                                        local deduped_1_7;
                                                        deduped_1_7 := deduped_1_6[i_7];
                                                        return Concatenation( List( [ deduped_1_7[1] .. deduped_1_7[2] ], function ( j_8 )
                                                                  local deduped_1_8;
                                                                  deduped_1_8 := deduped_8_6 * (j_8 - 1);
                                                                  return List( hoisted_4_6, function ( k_9 )
                                                                          local deduped_1_9;
                                                                          deduped_1_9 := hoisted_2_6[k_9];
                                                                          return NTuple( 2, deduped_1_9[1] + deduped_1_8, deduped_1_9[2] + deduped_1_8 );
                                                                      end );
                                                              end ) );
                                                    end ) ) );
                                        end );
                                end );
                            deduped_5_4 := List( deduped_21_3, function ( i_5 )
                                    local deduped_1_5, hoisted_2_5, deduped_3_5;
                                    deduped_3_5 := [ 1 .. deduped_19_3[i_5] ];
                                    hoisted_2_5 := deduped_4_4[i_5];
                                    deduped_1_5 := hoisted_2_4[i_5];
                                    return NTuple( 2, Sum( List( deduped_3_5, function ( i_6 )
                                                return deduped_1_5[i_6][1];
                                            end ) ), Concatenation( List( deduped_3_5, function ( i_6 )
                                                local deduped_1_6;
                                                deduped_1_6 := Sum( List( [ 1 .. i_6 - 1 ], function ( j_7 )
                                                          return hoisted_2_5[j_7];
                                                      end ) );
                                                return List( deduped_1_5[i_6][2], function ( col_7 )
                                                        return NTuple( 2, col_7[1] + deduped_1_6, col_7[2] + deduped_1_6 );
                                                    end );
                                            end ) ) );
                                end );
                            return NTuple( 2, Sum( List( deduped_21_3, function ( i_5 )
                                        return deduped_5_4[i_5][1];
                                    end ) ), Concatenation( List( deduped_21_3, function ( i_5 )
                                        local deduped_1_5;
                                        deduped_1_5 := Sum( List( [ 1 .. i_5 - 1 ], function ( j_6 )
                                                  return hoisted_7_4[j_6];
                                              end ) );
                                        return List( deduped_5_4[i_5][2], function ( col_6 )
                                                return NTuple( 2, col_6[1] + deduped_1_5, col_6[2] + deduped_1_5 );
                                            end );
                                    end ) ) );
                        end );
                    hoisted_16_3 := List( deduped_18_3, function ( i_4 )
                            return hoisted_15_3[i_4];
                        end );
                    return [ hoisted_35_1, List( deduped_18_3, function ( n_4 )
                                      return hoisted_16_3[n_4];
                                  end ){Positions( deduped_20_3, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_20_3 )][1];
                end );
            return NTuple( 2, Sum( List( deduped_52_1, function ( i_3 )
                        return deduped_2_2[i_3][1];
                    end ) ), Concatenation( List( deduped_52_1, function ( i_3 )
                        return deduped_2_2[i_3][2];
                    end ) ) );
        end );
    hoisted_37_1 := List( deduped_40_1, function ( n_2 )
            return hoisted_36_1[n_2];
        end );
    hoisted_16_1 := UnderlyingSplittingField( cat_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_38_1, deduped_38_1, TripleOfNrSupportListOfSupportListOfMatrices, NTuple( 3, deduped_41_1, deduped_44_1, List( deduped_40_1, function ( i_2 )
                local hoisted_1_2, deduped_2_2;
                deduped_2_2 := hoisted_37_1[i_2];
                hoisted_1_2 := deduped_2_2[2];
                return CertainColumns( HomalgIdentityMatrix( deduped_39_1[i_2], hoisted_16_1 ), Concatenation( List( [ 1 .. deduped_2_2[1] ], function ( j_3 )
                            local deduped_1_3;
                            deduped_1_3 := hoisted_1_2[j_3];
                            return [ deduped_1_3[1] .. deduped_1_3[2] ];
                        end ) ) );
            end ) ) );
end
########
        
    ;
    
    if IsBound( cat!.precompiled_functions_added ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "precompiled functions have already been added before" );
        
    fi;
    
    cat!.precompiled_functions_added := true;
    
end );

BindGlobal( "SkeletalCategoryOfGroupRepresentations_S4_Q_precompiled", function ( group, homalg_field )
  local category_constructor, cat;
    
    category_constructor :=
        
        
        function ( group, homalg_field )
    return SkeletalCategoryOfGroupRepresentations( group, homalg_field : no_precompiled_code := true );
end;
        
        
    
    cat := category_constructor( group, homalg_field : FinalizeCategory := false, no_precompiled_code := true );
    
    ADD_FUNCTIONS_FOR_SkeletalCategoryOfGroupRepresentations_S4_Q_precompiled( cat );
    
    Finalize( cat );
    
    return cat;
    
end );
