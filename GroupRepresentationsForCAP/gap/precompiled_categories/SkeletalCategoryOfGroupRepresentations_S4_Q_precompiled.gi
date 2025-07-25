# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Implementations
#
BindGlobal( "ADD_FUNCTIONS_FOR_SkeletalCategoryOfGroupRepresentations_S4_Q_precompiled", function ( cat )
    
    ##
    AddRightDistributivityExpandingWithGivenObjects( cat,
        
########
function ( cat_1, s_1, L_1, a_1, r_1 )
    local hoisted_1_1, hoisted_2_1, deduped_5_1, deduped_6_1, hoisted_9_1, hoisted_10_1, deduped_11_1, deduped_13_1, deduped_14_1, deduped_16_1, deduped_17_1, hoisted_18_1, hoisted_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1;
    deduped_29_1 := BigInt( 0 );
    deduped_28_1 := TripleOfNrSupportListOfSupportListOfRanks( a_1 );
    deduped_27_1 := TripleOfNrSupportListOfSupportListOfRanks( r_1 );
    deduped_26_1 := NTuple( 2, deduped_29_1, CapJitTypedExpression( [  ], function (  )
              return rec(
                  filter := IsList,
                  element_type := rec(
                      filter := IsNTuple,
                      element_types := [ rec(
                              filter := IsInt ), rec(
                              filter := IsInt ) ] ) );
          end ) );
    deduped_25_1 := deduped_28_1[1];
    deduped_24_1 := deduped_27_1[2];
    deduped_23_1 := deduped_27_1[1];
    deduped_22_1 := [ 1 .. deduped_25_1 ];
    deduped_21_1 := Union( List( L_1, function ( object_2 )
              return TripleOfNrSupportListOfSupportListOfRanks( object_2 )[2];
          end ) );
    deduped_20_1 := [ 1 .. Length( deduped_21_1 ) ];
    deduped_17_1 := [ 1 .. Length( L_1 ) ];
    deduped_5_1 := [ deduped_29_1 ];
    hoisted_18_1 := List( deduped_20_1, function ( n_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_21_1[n_2];
            return Sum( List( deduped_17_1, function ( i_3 )
                      local hoisted_1_3, deduped_2_3, deduped_3_3;
                      deduped_3_3 := TripleOfNrSupportListOfSupportListOfRanks( CAP_JIT_INCOMPLETE_LOGIC( L_1[i_3] ) );
                      deduped_2_3 := deduped_3_3[2];
                      hoisted_1_3 := deduped_3_3[3];
                      return CAP_JIT_INCOMPLETE_LOGIC( [ deduped_5_1, List( [ 1 .. deduped_3_3[1] ], function ( n_4 )
                                          return hoisted_1_3[n_4];
                                      end ){Positions( deduped_2_3, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_2_3 )][1] );
                  end ) );
        end );
    hoisted_19_1 := List( deduped_20_1, function ( i_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_21_1[i_2];
            return [ deduped_5_1, hoisted_18_1{Positions( deduped_21_1, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_21_1 )][1];
        end );
    deduped_16_1 := [ 1 .. Sum( List( deduped_20_1, function ( i_2 )
                  return deduped_25_1;
              end ) ) ];
    deduped_14_1 := UnderlyingIrreducibleCharacters( cat_1 );
    deduped_13_1 := deduped_28_1[2];
    hoisted_10_1 := deduped_28_1[3];
    deduped_11_1 := List( deduped_22_1, function ( n_2 )
            return hoisted_10_1[n_2];
        end );
    hoisted_9_1 := [ deduped_26_1 ];
    deduped_6_1 := BigInt( 1 );
    hoisted_2_1 := UnderlyingSplittingField( cat_1 );
    hoisted_1_1 := TripleOfNrSupportListOfSupportListOfRanks( s_1 )[3];
    return CreateCapCategoryMorphismWithAttributes( cat_1, s_1, r_1, TripleOfNrSupportListOfSupportListOfMatrices, NTuple( 3, deduped_23_1, deduped_24_1, List( [ 1 .. deduped_23_1 ], function ( i_2 )
                local deduped_1_2, hoisted_2_2, deduped_3_2, hoisted_4_2, deduped_5_2;
                deduped_1_2 := deduped_24_1[CAP_JIT_INCOMPLETE_LOGIC( i_2 )];
                hoisted_2_2 := Concatenation( List( deduped_20_1, function ( i_3 )
                          local hoisted_2_3, deduped_3_3;
                          deduped_3_3 := deduped_21_1[i_3];
                          hoisted_2_3 := [ deduped_5_1, hoisted_19_1{Positions( deduped_21_1, deduped_3_3 )} ][1 + BooleanToInteger( deduped_3_3 in deduped_21_1 )][1];
                          return List( deduped_22_1, function ( j_4 )
                                  return hoisted_2_3 * (deduped_11_1[j_4] * SGREPS_ScalarProduct( deduped_14_1, deduped_1_2, deduped_3_3, deduped_13_1[j_4] ));
                              end );
                      end ) );
                deduped_3_2 := List( deduped_17_1, function ( l_3 )
                        local hoisted_1_3, hoisted_2_3, deduped_3_3;
                        hoisted_1_3 := [ 1 .. l_3 - 1 ];
                        hoisted_2_3 := List( deduped_20_1, function ( i_4 )
                                local deduped_1_4, deduped_2_4, deduped_3_4, deduped_4_4;
                                deduped_1_4 := deduped_21_1[i_4];
                                deduped_4_4 := List( L_1, function ( object_5 )
                                        local hoisted_1_5, deduped_2_5, deduped_3_5;
                                        deduped_3_5 := TripleOfNrSupportListOfSupportListOfRanks( object_5 );
                                        deduped_2_5 := deduped_3_5[2];
                                        hoisted_1_5 := deduped_3_5[3];
                                        return [ deduped_5_1, List( [ 1 .. deduped_3_5[1] ], function ( n_6 )
                                                          return hoisted_1_5[n_6];
                                                      end ){Positions( deduped_2_5, deduped_1_4 )} ][1 + BooleanToInteger( deduped_1_4 in deduped_2_5 )][1];
                                    end );
                                deduped_3_4 := deduped_4_4[l_3];
                                deduped_2_4 := Sum( deduped_4_4{hoisted_1_3} );
                                return [ NTuple( 2, deduped_6_1, [ NTuple( 2, deduped_2_4 + 1, deduped_2_4 + deduped_3_4 ) ] ), deduped_26_1 ][1 + BooleanToInteger( deduped_3_4 = 0 )];
                            end );
                        deduped_3_3 := Concatenation( List( deduped_20_1, function ( i_4 )
                                  local deduped_1_4, hoisted_3_4, deduped_5_4, deduped_6_4, deduped_7_4;
                                  deduped_7_4 := deduped_21_1[i_4];
                                  deduped_6_4 := [ hoisted_9_1, hoisted_2_3{Positions( deduped_21_1, deduped_7_4 )} ][1 + BooleanToInteger( deduped_7_4 in deduped_21_1 )][1];
                                  deduped_5_4 := [ 1 .. deduped_6_4[1] ];
                                  deduped_1_4 := deduped_6_4[2];
                                  hoisted_3_4 := Sum( List( deduped_5_4, function ( i_5 )
                                            local deduped_1_5;
                                            deduped_1_5 := deduped_1_4[i_5];
                                            return deduped_1_5[2] - deduped_1_5[1] + deduped_6_1;
                                        end ) );
                                  return List( deduped_22_1, function ( j_5 )
                                          local hoisted_1_5, hoisted_3_5, deduped_4_5, deduped_5_5, deduped_6_5;
                                          deduped_6_5 := deduped_11_1[j_5] * SGREPS_ScalarProduct( deduped_14_1, deduped_1_2, deduped_7_4, deduped_13_1[j_5] );
                                          deduped_5_5 := [ NTuple( 2, deduped_6_1, [ NTuple( 2, deduped_6_1, deduped_6_5 ) ] ), deduped_26_1 ][1 + BooleanToInteger( deduped_6_5 = 0 )];
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
                        return NTuple( 2, Sum( List( deduped_16_1, function ( i_4 )
                                    return deduped_3_3[i_4][1];
                                end ) ), Concatenation( List( deduped_16_1, function ( i_4 )
                                    local deduped_1_4;
                                    deduped_1_4 := Sum( List( [ 1 .. i_4 - 1 ], function ( j_5 )
                                              return hoisted_2_2[j_5];
                                          end ) );
                                    return List( deduped_3_3[i_4][2], function ( col_5 )
                                            return NTuple( 2, col_5[1] + deduped_1_4, col_5[2] + deduped_1_4 );
                                        end );
                                end ) ) );
                    end );
                deduped_5_2 := CAP_JIT_INCOMPLETE_LOGIC( NTuple( 2, Sum( List( deduped_17_1, function ( i_3 )
                              return deduped_3_2[i_3][1];
                          end ) ), Concatenation( List( deduped_17_1, function ( i_3 )
                              return deduped_3_2[i_3][2];
                          end ) ) ) );
                hoisted_4_2 := deduped_5_2[2];
                return CertainColumns( HomalgIdentityMatrix( hoisted_1_1[i_2], hoisted_2_1 ), Concatenation( List( [ 1 .. deduped_5_2[1] ], function ( j_3 )
                            local deduped_1_3;
                            deduped_1_3 := hoisted_4_2[j_3];
                            return [ deduped_1_3[1] .. deduped_1_3[2] ];
                        end ) ) );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.RightDistributivityExpandingWithGivenObjects :=
        
########
function ( cat_1, s_1, L_1, a_1, r_1 )
    local hoisted_1_1, hoisted_2_1, deduped_5_1, deduped_6_1, hoisted_9_1, hoisted_10_1, deduped_11_1, deduped_13_1, deduped_14_1, deduped_16_1, deduped_17_1, hoisted_18_1, hoisted_19_1, hoisted_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1, deduped_28_1, deduped_29_1, deduped_30_1, deduped_31_1;
    deduped_31_1 := BigInt( 0 );
    deduped_30_1 := TripleOfNrSupportListOfSupportListOfRanks( a_1 );
    deduped_29_1 := TripleOfNrSupportListOfSupportListOfRanks( r_1 );
    deduped_28_1 := NTuple( 2, deduped_31_1, CapJitTypedExpression( [  ], function (  )
              return rec(
                  filter := IsList,
                  element_type := rec(
                      filter := IsNTuple,
                      element_types := [ rec(
                              filter := IsInt ), rec(
                              filter := IsInt ) ] ) );
          end ) );
    deduped_27_1 := deduped_30_1[1];
    deduped_26_1 := deduped_29_1[2];
    deduped_25_1 := deduped_29_1[1];
    deduped_24_1 := [ 1 .. deduped_27_1 ];
    deduped_23_1 := [ 1 .. deduped_25_1 ];
    deduped_22_1 := Union( List( L_1, function ( object_2 )
              return TripleOfNrSupportListOfSupportListOfRanks( object_2 )[2];
          end ) );
    deduped_21_1 := [ 1 .. Length( deduped_22_1 ) ];
    deduped_17_1 := [ 1 .. Length( L_1 ) ];
    deduped_5_1 := [ deduped_31_1 ];
    hoisted_18_1 := List( deduped_21_1, function ( n_2 )
            local deduped_1_2, hoisted_2_2;
            deduped_1_2 := deduped_22_1[n_2];
            hoisted_2_2 := List( L_1, function ( object_3 )
                    local hoisted_1_3, deduped_2_3, deduped_3_3;
                    deduped_3_3 := TripleOfNrSupportListOfSupportListOfRanks( object_3 );
                    deduped_2_3 := deduped_3_3[2];
                    hoisted_1_3 := deduped_3_3[3];
                    return [ deduped_5_1, List( [ 1 .. deduped_3_3[1] ], function ( n_4 )
                                      return hoisted_1_3[n_4];
                                  end ){Positions( deduped_2_3, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_2_3 )][1];
                end );
            return Sum( List( deduped_17_1, function ( i_3 )
                      return hoisted_2_2[i_3];
                  end ) );
        end );
    hoisted_19_1 := List( deduped_21_1, function ( i_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_22_1[i_2];
            return [ deduped_5_1, hoisted_18_1{Positions( deduped_22_1, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_22_1 )][1];
        end );
    deduped_16_1 := [ 1 .. Sum( List( deduped_21_1, function ( i_2 )
                  return deduped_27_1;
              end ) ) ];
    deduped_14_1 := UnderlyingIrreducibleCharacters( cat_1 );
    deduped_13_1 := deduped_30_1[2];
    hoisted_10_1 := deduped_30_1[3];
    deduped_11_1 := List( deduped_24_1, function ( n_2 )
            return hoisted_10_1[n_2];
        end );
    hoisted_9_1 := [ deduped_28_1 ];
    deduped_6_1 := BigInt( 1 );
    hoisted_20_1 := List( deduped_23_1, function ( k_2 )
            local deduped_1_2, hoisted_2_2, deduped_3_2;
            deduped_1_2 := deduped_26_1[k_2];
            hoisted_2_2 := Concatenation( List( deduped_21_1, function ( i_3 )
                      local hoisted_2_3, deduped_3_3;
                      deduped_3_3 := deduped_22_1[i_3];
                      hoisted_2_3 := [ deduped_5_1, hoisted_19_1{Positions( deduped_22_1, deduped_3_3 )} ][1 + BooleanToInteger( deduped_3_3 in deduped_22_1 )][1];
                      return List( deduped_24_1, function ( j_4 )
                              return hoisted_2_3 * (deduped_11_1[j_4] * SGREPS_ScalarProduct( deduped_14_1, deduped_1_2, deduped_3_3, deduped_13_1[j_4] ));
                          end );
                  end ) );
            deduped_3_2 := List( deduped_17_1, function ( l_3 )
                    local hoisted_1_3, hoisted_2_3, deduped_3_3;
                    hoisted_1_3 := [ 1 .. l_3 - 1 ];
                    hoisted_2_3 := List( deduped_21_1, function ( i_4 )
                            local deduped_1_4, deduped_2_4, deduped_3_4, deduped_4_4;
                            deduped_1_4 := deduped_22_1[i_4];
                            deduped_4_4 := List( L_1, function ( object_5 )
                                    local hoisted_1_5, deduped_2_5, deduped_3_5;
                                    deduped_3_5 := TripleOfNrSupportListOfSupportListOfRanks( object_5 );
                                    deduped_2_5 := deduped_3_5[2];
                                    hoisted_1_5 := deduped_3_5[3];
                                    return [ deduped_5_1, List( [ 1 .. deduped_3_5[1] ], function ( n_6 )
                                                      return hoisted_1_5[n_6];
                                                  end ){Positions( deduped_2_5, deduped_1_4 )} ][1 + BooleanToInteger( deduped_1_4 in deduped_2_5 )][1];
                                end );
                            deduped_3_4 := deduped_4_4[l_3];
                            deduped_2_4 := Sum( deduped_4_4{hoisted_1_3} );
                            return [ NTuple( 2, deduped_6_1, [ NTuple( 2, deduped_2_4 + 1, deduped_2_4 + deduped_3_4 ) ] ), deduped_28_1 ][1 + BooleanToInteger( deduped_3_4 = 0 )];
                        end );
                    deduped_3_3 := Concatenation( List( deduped_21_1, function ( i_4 )
                              local deduped_1_4, hoisted_3_4, deduped_5_4, deduped_6_4, deduped_7_4;
                              deduped_7_4 := deduped_22_1[i_4];
                              deduped_6_4 := [ hoisted_9_1, hoisted_2_3{Positions( deduped_22_1, deduped_7_4 )} ][1 + BooleanToInteger( deduped_7_4 in deduped_22_1 )][1];
                              deduped_5_4 := [ 1 .. deduped_6_4[1] ];
                              deduped_1_4 := deduped_6_4[2];
                              hoisted_3_4 := Sum( List( deduped_5_4, function ( i_5 )
                                        local deduped_1_5;
                                        deduped_1_5 := deduped_1_4[i_5];
                                        return deduped_1_5[2] - deduped_1_5[1] + deduped_6_1;
                                    end ) );
                              return List( deduped_24_1, function ( j_5 )
                                      local hoisted_1_5, hoisted_3_5, deduped_4_5, deduped_5_5, deduped_6_5;
                                      deduped_6_5 := deduped_11_1[j_5] * SGREPS_ScalarProduct( deduped_14_1, deduped_1_2, deduped_7_4, deduped_13_1[j_5] );
                                      deduped_5_5 := [ NTuple( 2, deduped_6_1, [ NTuple( 2, deduped_6_1, deduped_6_5 ) ] ), deduped_28_1 ][1 + BooleanToInteger( deduped_6_5 = 0 )];
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
                    return NTuple( 2, Sum( List( deduped_16_1, function ( i_4 )
                                return deduped_3_3[i_4][1];
                            end ) ), Concatenation( List( deduped_16_1, function ( i_4 )
                                local deduped_1_4;
                                deduped_1_4 := Sum( List( [ 1 .. i_4 - 1 ], function ( j_5 )
                                          return hoisted_2_2[j_5];
                                      end ) );
                                return List( deduped_3_3[i_4][2], function ( col_5 )
                                        return NTuple( 2, col_5[1] + deduped_1_4, col_5[2] + deduped_1_4 );
                                    end );
                            end ) ) );
                end );
            return NTuple( 2, Sum( List( deduped_17_1, function ( i_3 )
                        return deduped_3_2[i_3][1];
                    end ) ), Concatenation( List( deduped_17_1, function ( i_3 )
                        return deduped_3_2[i_3][2];
                    end ) ) );
        end );
    hoisted_2_1 := UnderlyingSplittingField( cat_1 );
    hoisted_1_1 := TripleOfNrSupportListOfSupportListOfRanks( s_1 )[3];
    return CreateCapCategoryMorphismWithAttributes( cat_1, s_1, r_1, TripleOfNrSupportListOfSupportListOfMatrices, NTuple( 3, deduped_25_1, deduped_26_1, List( deduped_23_1, function ( i_2 )
                local hoisted_1_2, deduped_2_2;
                deduped_2_2 := hoisted_20_1[i_2];
                hoisted_1_2 := deduped_2_2[2];
                return CertainColumns( HomalgIdentityMatrix( hoisted_1_1[i_2], hoisted_2_1 ), Concatenation( List( [ 1 .. deduped_2_2[1] ], function ( j_3 )
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
    return SkeletalCategoryOfGroupRepresentations( group, homalg_field : no_precompiled_code := true,
        product_ins_mat_no_precompiled_code := false,
        ins_mat_no_precompiled_code := false );
end;
        
        
    
    cat := category_constructor( group, homalg_field : FinalizeCategory := false, no_precompiled_code := true );
    
    ADD_FUNCTIONS_FOR_SkeletalCategoryOfGroupRepresentations_S4_Q_precompiled( cat );
    
    Finalize( cat );
    
    return cat;
    
end );
