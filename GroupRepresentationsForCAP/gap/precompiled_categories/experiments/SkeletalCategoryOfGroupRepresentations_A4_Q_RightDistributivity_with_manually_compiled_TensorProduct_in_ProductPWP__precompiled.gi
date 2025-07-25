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
    local deduped_2_1, deduped_3_1, deduped_4_1, deduped_6_1, hoisted_7_1, hoisted_8_1, deduped_9_1, hoisted_13_1, deduped_15_1, deduped_16_1, hoisted_18_1, deduped_19_1, deduped_20_1, hoisted_21_1, hoisted_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1, deduped_30_1, deduped_31_1, deduped_32_1, deduped_33_1, deduped_34_1;
    deduped_34_1 := BigInt( 0 );
    deduped_33_1 := TripleOfNrSupportListOfSupportListOfRanks( a_1 );
    deduped_32_1 := NTuple( 2, deduped_34_1, CapJitTypedExpression( [  ], function (  )
              return rec(
                  filter := IsList,
                  element_type := rec(
                      filter := IsNTuple,
                      element_types := [ rec(
                              filter := IsInt ), rec(
                              filter := IsInt ) ] ) );
          end ) );
    deduped_31_1 := deduped_33_1[1];
    deduped_30_1 := [ 1 .. deduped_31_1 ];
    deduped_29_1 := Union( List( L_1, function ( x_2 )
              return TripleOfNrSupportListOfSupportListOfRanks( x_2 )[2];
          end ) );
    deduped_28_1 := [ 1 .. Length( deduped_29_1 ) ];
    deduped_4_1 := [ 1 .. IndexOfTrivialCharacterInListOfIrreducibleCharacters( cat_1 ) ];
    deduped_3_1 := UnderlyingIrreducibleCharacters( cat_1 );
    deduped_2_1 := deduped_33_1[2];
    deduped_27_1 := Union( List( deduped_28_1, function ( i_2 )
              local hoisted_1_2;
              hoisted_1_2 := deduped_29_1[i_2];
              return Union( List( deduped_30_1, function ( j_3 )
                        local hoisted_1_3;
                        hoisted_1_3 := deduped_2_1[j_3];
                        return Filtered( deduped_4_1, function ( k_4 )
                                return not CAP_JIT_INCOMPLETE_LOGIC( IsZero( SGREPS_ScalarProduct( deduped_3_1, CAP_JIT_INCOMPLETE_LOGIC( k_4 ), hoisted_1_2, hoisted_1_3 ) ) );
                            end );
                    end ) );
          end ) );
    deduped_26_1 := Length( deduped_27_1 );
    deduped_25_1 := [ 1 .. deduped_26_1 ];
    hoisted_8_1 := deduped_33_1[3];
    deduped_9_1 := List( deduped_30_1, function ( n_2 )
            return hoisted_8_1[n_2];
        end );
    deduped_6_1 := [ 0 ];
    hoisted_7_1 := List( deduped_28_1, function ( n_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_29_1[CAP_JIT_INCOMPLETE_LOGIC( n_2 )];
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
    deduped_24_1 := List( deduped_25_1, function ( n_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_27_1[CAP_JIT_INCOMPLETE_LOGIC( n_2 )];
            return CAP_JIT_INCOMPLETE_LOGIC( Sum( List( deduped_28_1, function ( i_3 )
                        local deduped_1_3, hoisted_2_3, deduped_4_3;
                        deduped_1_3 := deduped_29_1[i_3];
                        deduped_4_3 := Union( List( deduped_30_1, function ( j_4 )
                                  local hoisted_1_4;
                                  hoisted_1_4 := deduped_2_1[j_4];
                                  return Filtered( deduped_4_1, function ( k_5 )
                                          return not CAP_JIT_INCOMPLETE_LOGIC( IsZero( SGREPS_ScalarProduct( deduped_3_1, CAP_JIT_INCOMPLETE_LOGIC( k_5 ), deduped_1_3, hoisted_1_4 ) ) );
                                      end );
                              end ) );
                        hoisted_2_3 := hoisted_7_1[i_3];
                        return [ deduped_6_1, List( [ 1 .. Length( deduped_4_3 ) ], function ( n_4 )
                                          local deduped_1_4;
                                          deduped_1_4 := deduped_4_3[CAP_JIT_INCOMPLETE_LOGIC( n_4 )];
                                          return CAP_JIT_INCOMPLETE_LOGIC( Sum( List( deduped_30_1, function ( j_5 )
                                                      local deduped_1_5, hoisted_3_5, deduped_4_5;
                                                      deduped_1_5 := deduped_2_1[j_5];
                                                      deduped_4_5 := Filtered( deduped_4_1, function ( k_6 )
                                                              return not CAP_JIT_INCOMPLETE_LOGIC( IsZero( SGREPS_ScalarProduct( deduped_3_1, CAP_JIT_INCOMPLETE_LOGIC( k_6 ), deduped_1_3, deduped_1_5 ) ) );
                                                          end );
                                                      hoisted_3_5 := hoisted_2_3 * deduped_9_1[j_5];
                                                      return [ deduped_6_1, List( [ 1 .. Length( deduped_4_5 ) ], function ( n_6 )
                                                                        return CAP_JIT_INCOMPLETE_LOGIC( CAP_JIT_INCOMPLETE_LOGIC( SGREPS_ScalarProduct( deduped_3_1, CAP_JIT_INCOMPLETE_LOGIC( deduped_4_5[CAP_JIT_INCOMPLETE_LOGIC( n_6 )] ), deduped_1_3, deduped_1_5 ) ) * hoisted_3_5 );
                                                                    end ){Positions( deduped_4_5, deduped_1_4 )} ][BooleanToInteger( deduped_1_4 in deduped_4_5 ) + 1][1];
                                                  end ) ) );
                                      end ){Positions( deduped_4_3, deduped_1_2 )} ][BooleanToInteger( deduped_1_2 in deduped_4_3 ) + 1][1];
                    end ) ) );
        end );
    deduped_23_1 := CreateCapCategoryObjectWithAttributes( cat_1, TripleOfNrSupportListOfSupportListOfRanks, NTuple( 3, deduped_26_1, deduped_27_1, deduped_24_1 ) );
    deduped_20_1 := [ 1 .. Length( L_1 ) ];
    deduped_15_1 := [ deduped_34_1 ];
    hoisted_21_1 := List( deduped_28_1, function ( n_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_29_1[n_2];
            return Sum( List( deduped_20_1, function ( i_3 )
                      local hoisted_1_3, deduped_2_3, deduped_3_3;
                      deduped_3_3 := TripleOfNrSupportListOfSupportListOfRanks( CAP_JIT_INCOMPLETE_LOGIC( L_1[i_3] ) );
                      deduped_2_3 := deduped_3_3[2];
                      hoisted_1_3 := deduped_3_3[3];
                      return CAP_JIT_INCOMPLETE_LOGIC( [ deduped_15_1, List( [ 1 .. deduped_3_3[1] ], function ( n_4 )
                                          return hoisted_1_3[n_4];
                                      end ){Positions( deduped_2_3, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_2_3 )][1] );
                  end ) );
        end );
    hoisted_22_1 := List( deduped_28_1, function ( i_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_29_1[i_2];
            return [ deduped_15_1, hoisted_21_1{Positions( deduped_29_1, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_29_1 )][1];
        end );
    deduped_19_1 := [ 1 .. Sum( List( deduped_28_1, function ( i_2 )
                  return deduped_31_1;
              end ) ) ];
    hoisted_18_1 := [ deduped_32_1 ];
    deduped_16_1 := BigInt( 1 );
    hoisted_13_1 := UnderlyingSplittingField( cat_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_23_1, deduped_23_1, TripleOfNrSupportListOfSupportListOfMatrices, NTuple( 3, deduped_26_1, deduped_27_1, List( deduped_25_1, function ( i_2 )
                local deduped_1_2, hoisted_2_2, deduped_3_2, hoisted_4_2, deduped_5_2;
                deduped_1_2 := deduped_27_1[CAP_JIT_INCOMPLETE_LOGIC( i_2 )];
                hoisted_2_2 := Concatenation( List( deduped_28_1, function ( i_3 )
                          local hoisted_2_3, deduped_3_3;
                          deduped_3_3 := deduped_29_1[i_3];
                          hoisted_2_3 := [ deduped_15_1, hoisted_22_1{Positions( deduped_29_1, deduped_3_3 )} ][1 + BooleanToInteger( deduped_3_3 in deduped_29_1 )][1];
                          return List( deduped_30_1, function ( j_4 )
                                  return hoisted_2_3 * (deduped_9_1[j_4] * SGREPS_ScalarProduct( deduped_3_1, deduped_1_2, deduped_3_3, deduped_2_1[j_4] ));
                              end );
                      end ) );
                deduped_3_2 := List( deduped_20_1, function ( l_3 )
                        local hoisted_1_3, hoisted_2_3, deduped_3_3;
                        hoisted_1_3 := [ 1 .. l_3 - 1 ];
                        hoisted_2_3 := List( deduped_28_1, function ( i_4 )
                                local deduped_1_4, deduped_2_4, deduped_3_4, deduped_4_4;
                                deduped_1_4 := deduped_29_1[i_4];
                                deduped_4_4 := List( L_1, function ( object_5 )
                                        local hoisted_1_5, deduped_2_5, deduped_3_5;
                                        deduped_3_5 := TripleOfNrSupportListOfSupportListOfRanks( object_5 );
                                        deduped_2_5 := deduped_3_5[2];
                                        hoisted_1_5 := deduped_3_5[3];
                                        return [ deduped_15_1, List( [ 1 .. deduped_3_5[1] ], function ( n_6 )
                                                          return hoisted_1_5[n_6];
                                                      end ){Positions( deduped_2_5, deduped_1_4 )} ][1 + BooleanToInteger( deduped_1_4 in deduped_2_5 )][1];
                                    end );
                                deduped_3_4 := deduped_4_4[l_3];
                                deduped_2_4 := Sum( deduped_4_4{hoisted_1_3} );
                                return [ NTuple( 2, deduped_16_1, [ NTuple( 2, deduped_2_4 + 1, deduped_2_4 + deduped_3_4 ) ] ), deduped_32_1 ][1 + BooleanToInteger( deduped_3_4 = 0 )];
                            end );
                        deduped_3_3 := Concatenation( List( deduped_28_1, function ( i_4 )
                                  local deduped_1_4, hoisted_3_4, deduped_5_4, deduped_6_4, deduped_7_4;
                                  deduped_7_4 := deduped_29_1[i_4];
                                  deduped_6_4 := [ hoisted_18_1, hoisted_2_3{Positions( deduped_29_1, deduped_7_4 )} ][1 + BooleanToInteger( deduped_7_4 in deduped_29_1 )][1];
                                  deduped_5_4 := [ 1 .. deduped_6_4[1] ];
                                  deduped_1_4 := deduped_6_4[2];
                                  hoisted_3_4 := Sum( List( deduped_5_4, function ( i_5 )
                                            local deduped_1_5;
                                            deduped_1_5 := deduped_1_4[i_5];
                                            return deduped_1_5[2] - deduped_1_5[1] + deduped_16_1;
                                        end ) );
                                  return List( deduped_30_1, function ( j_5 )
                                          local hoisted_1_5, hoisted_3_5, deduped_4_5, deduped_5_5, deduped_6_5;
                                          deduped_6_5 := deduped_9_1[j_5] * SGREPS_ScalarProduct( deduped_3_1, deduped_1_2, deduped_7_4, deduped_2_1[j_5] );
                                          deduped_5_5 := [ NTuple( 2, deduped_16_1, [ NTuple( 2, deduped_16_1, deduped_6_5 ) ] ), deduped_32_1 ][1 + BooleanToInteger( deduped_6_5 = 0 )];
                                          deduped_4_5 := deduped_5_5[1];
                                          hoisted_3_5 := [ 1 .. deduped_4_5 ];
                                          hoisted_1_5 := deduped_5_5[2];
                                          return NTuple( 2, hoisted_3_4 * deduped_4_5, Concatenation( List( deduped_5_4, function ( i_6 )
                                                      local deduped_1_6;
                                                      deduped_1_6 := deduped_1_4[i_6];
                                                      return Concatenation( List( [ deduped_1_6[1] .. deduped_1_6[2] ], function ( j_7 )
                                                                local deduped_1_7;
                                                                deduped_1_7 := deduped_6_5 * (j_7 - 1);
                                                                return List( hoisted_3_5, function ( k_8 )
                                                                        local deduped_1_8;
                                                                        deduped_1_8 := hoisted_1_5[k_8];
                                                                        return NTuple( 2, deduped_1_8[1] + deduped_1_7, deduped_1_8[2] + deduped_1_7 );
                                                                    end );
                                                            end ) );
                                                  end ) ) );
                                      end );
                              end ) );
                        return NTuple( 2, Sum( List( deduped_19_1, function ( i_4 )
                                    return deduped_3_3[i_4][1];
                                end ) ), Concatenation( List( deduped_19_1, function ( i_4 )
                                    local deduped_1_4;
                                    deduped_1_4 := Sum( List( [ 1 .. i_4 - 1 ], function ( j_5 )
                                              return hoisted_2_2[j_5];
                                          end ) );
                                    return List( deduped_3_3[i_4][2], function ( col_5 )
                                            return NTuple( 2, col_5[1] + deduped_1_4, col_5[2] + deduped_1_4 );
                                        end );
                                end ) ) );
                    end );
                deduped_5_2 := CAP_JIT_INCOMPLETE_LOGIC( NTuple( 2, Sum( List( deduped_20_1, function ( i_3 )
                              return deduped_3_2[i_3][1];
                          end ) ), Concatenation( List( deduped_20_1, function ( i_3 )
                              return deduped_3_2[i_3][2];
                          end ) ) ) );
                hoisted_4_2 := deduped_5_2[2];
                return CertainColumns( HomalgIdentityMatrix( deduped_24_1[i_2], hoisted_13_1 ), Concatenation( List( [ 1 .. deduped_5_2[1] ], function ( j_3 )
                            local deduped_1_3;
                            deduped_1_3 := hoisted_4_2[j_3];
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
    local deduped_2_1, deduped_3_1, deduped_4_1, deduped_6_1, hoisted_7_1, hoisted_8_1, hoisted_9_1, hoisted_10_1, deduped_11_1, hoisted_14_1, hoisted_16_1, deduped_18_1, deduped_19_1, hoisted_21_1, deduped_22_1, deduped_23_1, hoisted_24_1, hoisted_25_1, hoisted_26_1, deduped_27_1, deduped_28_1, deduped_29_1, deduped_30_1, deduped_31_1, deduped_32_1, deduped_33_1, deduped_34_1, deduped_35_1, deduped_36_1, deduped_37_1, deduped_38_1;
    deduped_38_1 := BigInt( 0 );
    deduped_37_1 := TripleOfNrSupportListOfSupportListOfRanks( a_1 );
    deduped_36_1 := NTuple( 2, deduped_38_1, CapJitTypedExpression( [  ], function (  )
              return rec(
                  filter := IsList,
                  element_type := rec(
                      filter := IsNTuple,
                      element_types := [ rec(
                              filter := IsInt ), rec(
                              filter := IsInt ) ] ) );
          end ) );
    deduped_35_1 := deduped_37_1[1];
    deduped_34_1 := [ 1 .. deduped_35_1 ];
    deduped_33_1 := Union( List( L_1, function ( x_2 )
              return TripleOfNrSupportListOfSupportListOfRanks( x_2 )[2];
          end ) );
    deduped_32_1 := [ 1 .. Length( deduped_33_1 ) ];
    deduped_4_1 := [ 1 .. IndexOfTrivialCharacterInListOfIrreducibleCharacters( cat_1 ) ];
    deduped_3_1 := UnderlyingIrreducibleCharacters( cat_1 );
    deduped_2_1 := deduped_37_1[2];
    deduped_31_1 := Union( List( deduped_32_1, function ( i_2 )
              local hoisted_1_2;
              hoisted_1_2 := deduped_33_1[i_2];
              return Union( List( deduped_34_1, function ( j_3 )
                        local hoisted_1_3, hoisted_2_3;
                        hoisted_1_3 := deduped_2_1[j_3];
                        hoisted_2_3 := List( deduped_4_1, function ( k_4 )
                                return IsZero( SGREPS_ScalarProduct( deduped_3_1, k_4, hoisted_1_2, hoisted_1_3 ) );
                            end );
                        return Filtered( deduped_4_1, function ( k_4 )
                                return not hoisted_2_3[k_4];
                            end );
                    end ) );
          end ) );
    deduped_30_1 := Length( deduped_31_1 );
    deduped_29_1 := [ 1 .. deduped_30_1 ];
    hoisted_10_1 := deduped_37_1[3];
    deduped_11_1 := List( deduped_34_1, function ( n_2 )
            return hoisted_10_1[n_2];
        end );
    deduped_6_1 := [ 0 ];
    hoisted_7_1 := List( deduped_32_1, function ( n_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_33_1[n_2];
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
    hoisted_8_1 := List( deduped_32_1, function ( n_2 )
            return hoisted_7_1[n_2];
        end );
    hoisted_9_1 := List( deduped_32_1, function ( n_2 )
            return hoisted_8_1[n_2];
        end );
    hoisted_14_1 := List( deduped_29_1, function ( n_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_31_1[n_2];
            return Sum( List( deduped_32_1, function ( i_3 )
                      local deduped_1_3, hoisted_2_3, hoisted_4_3, hoisted_5_3, deduped_6_3, deduped_7_3;
                      deduped_1_3 := deduped_33_1[i_3];
                      deduped_7_3 := Union( List( deduped_34_1, function ( j_4 )
                                local hoisted_1_4, hoisted_2_4;
                                hoisted_1_4 := deduped_2_1[j_4];
                                hoisted_2_4 := List( deduped_4_1, function ( k_5 )
                                        return IsZero( SGREPS_ScalarProduct( deduped_3_1, k_5, deduped_1_3, hoisted_1_4 ) );
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
                              return Sum( List( deduped_34_1, function ( j_5 )
                                        local deduped_1_5, hoisted_2_5, hoisted_3_5, hoisted_4_5, hoisted_5_5, hoisted_6_5, hoisted_7_5, deduped_8_5, deduped_9_5;
                                        deduped_1_5 := deduped_2_1[j_5];
                                        hoisted_2_5 := List( deduped_4_1, function ( k_6 )
                                                return IsZero( SGREPS_ScalarProduct( deduped_3_1, k_6, deduped_1_3, deduped_1_5 ) );
                                            end );
                                        deduped_9_5 := Filtered( deduped_4_1, function ( k_6 )
                                                return not hoisted_2_5[k_6];
                                            end );
                                        deduped_8_5 := [ 1 .. Length( deduped_9_5 ) ];
                                        hoisted_5_5 := hoisted_2_3 * deduped_11_1[j_5];
                                        hoisted_3_5 := List( deduped_4_1, function ( k_6 )
                                                return SGREPS_ScalarProduct( deduped_3_1, k_6, deduped_1_3, deduped_1_5 );
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
    deduped_28_1 := List( deduped_29_1, function ( n_2 )
            return hoisted_14_1[n_2];
        end );
    deduped_27_1 := CreateCapCategoryObjectWithAttributes( cat_1, TripleOfNrSupportListOfSupportListOfRanks, NTuple( 3, deduped_30_1, deduped_31_1, deduped_28_1 ) );
    deduped_23_1 := [ 1 .. Length( L_1 ) ];
    deduped_18_1 := [ deduped_38_1 ];
    hoisted_24_1 := List( deduped_32_1, function ( n_2 )
            local deduped_1_2, hoisted_2_2;
            deduped_1_2 := deduped_33_1[n_2];
            hoisted_2_2 := List( L_1, function ( object_3 )
                    local hoisted_1_3, deduped_2_3, deduped_3_3;
                    deduped_3_3 := TripleOfNrSupportListOfSupportListOfRanks( object_3 );
                    deduped_2_3 := deduped_3_3[2];
                    hoisted_1_3 := deduped_3_3[3];
                    return [ deduped_18_1, List( [ 1 .. deduped_3_3[1] ], function ( n_4 )
                                      return hoisted_1_3[n_4];
                                  end ){Positions( deduped_2_3, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_2_3 )][1];
                end );
            return Sum( List( deduped_23_1, function ( i_3 )
                      return hoisted_2_2[i_3];
                  end ) );
        end );
    hoisted_25_1 := List( deduped_32_1, function ( i_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_33_1[i_2];
            return [ deduped_18_1, hoisted_24_1{Positions( deduped_33_1, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_33_1 )][1];
        end );
    deduped_22_1 := [ 1 .. Sum( List( deduped_32_1, function ( i_2 )
                  return deduped_35_1;
              end ) ) ];
    hoisted_21_1 := [ deduped_36_1 ];
    deduped_19_1 := BigInt( 1 );
    hoisted_26_1 := List( deduped_29_1, function ( k_2 )
            local deduped_1_2, hoisted_2_2, deduped_3_2;
            deduped_1_2 := deduped_31_1[k_2];
            hoisted_2_2 := Concatenation( List( deduped_32_1, function ( i_3 )
                      local hoisted_2_3, deduped_3_3;
                      deduped_3_3 := deduped_33_1[i_3];
                      hoisted_2_3 := [ deduped_18_1, hoisted_25_1{Positions( deduped_33_1, deduped_3_3 )} ][1 + BooleanToInteger( deduped_3_3 in deduped_33_1 )][1];
                      return List( deduped_34_1, function ( j_4 )
                              return hoisted_2_3 * (deduped_11_1[j_4] * SGREPS_ScalarProduct( deduped_3_1, deduped_1_2, deduped_3_3, deduped_2_1[j_4] ));
                          end );
                  end ) );
            deduped_3_2 := List( deduped_23_1, function ( l_3 )
                    local hoisted_1_3, hoisted_2_3, deduped_3_3;
                    hoisted_1_3 := [ 1 .. l_3 - 1 ];
                    hoisted_2_3 := List( deduped_32_1, function ( i_4 )
                            local deduped_1_4, deduped_2_4, deduped_3_4, deduped_4_4;
                            deduped_1_4 := deduped_33_1[i_4];
                            deduped_4_4 := List( L_1, function ( object_5 )
                                    local hoisted_1_5, deduped_2_5, deduped_3_5;
                                    deduped_3_5 := TripleOfNrSupportListOfSupportListOfRanks( object_5 );
                                    deduped_2_5 := deduped_3_5[2];
                                    hoisted_1_5 := deduped_3_5[3];
                                    return [ deduped_18_1, List( [ 1 .. deduped_3_5[1] ], function ( n_6 )
                                                      return hoisted_1_5[n_6];
                                                  end ){Positions( deduped_2_5, deduped_1_4 )} ][1 + BooleanToInteger( deduped_1_4 in deduped_2_5 )][1];
                                end );
                            deduped_3_4 := deduped_4_4[l_3];
                            deduped_2_4 := Sum( deduped_4_4{hoisted_1_3} );
                            return [ NTuple( 2, deduped_19_1, [ NTuple( 2, deduped_2_4 + 1, deduped_2_4 + deduped_3_4 ) ] ), deduped_36_1 ][1 + BooleanToInteger( deduped_3_4 = 0 )];
                        end );
                    deduped_3_3 := Concatenation( List( deduped_32_1, function ( i_4 )
                              local deduped_1_4, hoisted_3_4, deduped_5_4, deduped_6_4, deduped_7_4;
                              deduped_7_4 := deduped_33_1[i_4];
                              deduped_6_4 := [ hoisted_21_1, hoisted_2_3{Positions( deduped_33_1, deduped_7_4 )} ][1 + BooleanToInteger( deduped_7_4 in deduped_33_1 )][1];
                              deduped_5_4 := [ 1 .. deduped_6_4[1] ];
                              deduped_1_4 := deduped_6_4[2];
                              hoisted_3_4 := Sum( List( deduped_5_4, function ( i_5 )
                                        local deduped_1_5;
                                        deduped_1_5 := deduped_1_4[i_5];
                                        return deduped_1_5[2] - deduped_1_5[1] + deduped_19_1;
                                    end ) );
                              return List( deduped_34_1, function ( j_5 )
                                      local hoisted_1_5, hoisted_3_5, deduped_4_5, deduped_5_5, deduped_6_5;
                                      deduped_6_5 := deduped_11_1[j_5] * SGREPS_ScalarProduct( deduped_3_1, deduped_1_2, deduped_7_4, deduped_2_1[j_5] );
                                      deduped_5_5 := [ NTuple( 2, deduped_19_1, [ NTuple( 2, deduped_19_1, deduped_6_5 ) ] ), deduped_36_1 ][1 + BooleanToInteger( deduped_6_5 = 0 )];
                                      deduped_4_5 := deduped_5_5[1];
                                      hoisted_3_5 := [ 1 .. deduped_4_5 ];
                                      hoisted_1_5 := deduped_5_5[2];
                                      return NTuple( 2, hoisted_3_4 * deduped_4_5, Concatenation( List( deduped_5_4, function ( i_6 )
                                                  local deduped_1_6;
                                                  deduped_1_6 := deduped_1_4[i_6];
                                                  return Concatenation( List( [ deduped_1_6[1] .. deduped_1_6[2] ], function ( j_7 )
                                                            local deduped_1_7;
                                                            deduped_1_7 := deduped_6_5 * (j_7 - 1);
                                                            return List( hoisted_3_5, function ( k_8 )
                                                                    local deduped_1_8;
                                                                    deduped_1_8 := hoisted_1_5[k_8];
                                                                    return NTuple( 2, deduped_1_8[1] + deduped_1_7, deduped_1_8[2] + deduped_1_7 );
                                                                end );
                                                        end ) );
                                              end ) ) );
                                  end );
                          end ) );
                    return NTuple( 2, Sum( List( deduped_22_1, function ( i_4 )
                                return deduped_3_3[i_4][1];
                            end ) ), Concatenation( List( deduped_22_1, function ( i_4 )
                                local deduped_1_4;
                                deduped_1_4 := Sum( List( [ 1 .. i_4 - 1 ], function ( j_5 )
                                          return hoisted_2_2[j_5];
                                      end ) );
                                return List( deduped_3_3[i_4][2], function ( col_5 )
                                        return NTuple( 2, col_5[1] + deduped_1_4, col_5[2] + deduped_1_4 );
                                    end );
                            end ) ) );
                end );
            return NTuple( 2, Sum( List( deduped_23_1, function ( i_3 )
                        return deduped_3_2[i_3][1];
                    end ) ), Concatenation( List( deduped_23_1, function ( i_3 )
                        return deduped_3_2[i_3][2];
                    end ) ) );
        end );
    hoisted_16_1 := UnderlyingSplittingField( cat_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_27_1, deduped_27_1, TripleOfNrSupportListOfSupportListOfMatrices, NTuple( 3, deduped_30_1, deduped_31_1, List( deduped_29_1, function ( i_2 )
                local hoisted_1_2, deduped_2_2;
                deduped_2_2 := hoisted_26_1[i_2];
                hoisted_1_2 := deduped_2_2[2];
                return CertainColumns( HomalgIdentityMatrix( deduped_28_1[i_2], hoisted_16_1 ), Concatenation( List( [ 1 .. deduped_2_2[1] ], function ( j_3 )
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
