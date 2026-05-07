# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Implementations
#
BindGlobal( "ADD_FUNCTIONS_FOR_Subcategory_SkeletalCategoryOfGroupRepresentations_S4_SparseProduct_KroneckerComonoids_precompiled", function ( cat )
    
    ##
    AddRightDistributivityExpandingWithGivenObjects( cat,
        
########
function ( cat_1, s_1, L_1, a_1, r_1 )
    local deduped_3_1, deduped_4_1, hoisted_7_1, hoisted_8_1, deduped_9_1, deduped_11_1, deduped_12_1, deduped_14_1, deduped_15_1, hoisted_16_1, hoisted_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1;
    deduped_27_1 := BigInt( 0 );
    deduped_26_1 := TripleOfNrSupportListOfSupportListOfNumberElements( a_1 );
    deduped_25_1 := TripleOfNrSupportListOfSupportListOfNumberElements( r_1 );
    deduped_24_1 := NTuple( 2, deduped_27_1, CapJitTypedExpression( [  ], function (  )
              return rec(
                  filter := IsList,
                  element_type := rec(
                      filter := IsNTuple,
                      element_types := [ rec(
                              filter := IsInt ), rec(
                              filter := IsInt ) ] ) );
          end ) );
    deduped_23_1 := deduped_26_1[1];
    deduped_22_1 := deduped_25_1[2];
    deduped_21_1 := deduped_25_1[1];
    deduped_20_1 := [ 1 .. deduped_23_1 ];
    deduped_19_1 := Union( List( L_1, function ( object_2 )
              return TripleOfNrSupportListOfSupportListOfNumberElements( object_2 )[2];
          end ) );
    deduped_18_1 := [ 1 .. Length( deduped_19_1 ) ];
    deduped_15_1 := [ 1 .. Length( L_1 ) ];
    deduped_3_1 := [ deduped_27_1 ];
    hoisted_16_1 := List( deduped_18_1, function ( n_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_19_1[n_2];
            return Sum( List( deduped_15_1, function ( i_3 )
                      local hoisted_1_3, deduped_2_3, deduped_3_3;
                      deduped_3_3 := TripleOfNrSupportListOfSupportListOfNumberElements( CAP_JIT_INCOMPLETE_LOGIC( L_1[i_3] ) );
                      deduped_2_3 := deduped_3_3[2];
                      hoisted_1_3 := deduped_3_3[3];
                      return CAP_JIT_INCOMPLETE_LOGIC( [ deduped_3_1, List( [ 1 .. deduped_3_3[1] ], function ( n_4 )
                                          return hoisted_1_3[n_4];
                                      end ){Positions( deduped_2_3, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_2_3 )][1] );
                  end ) );
        end );
    hoisted_17_1 := List( deduped_18_1, function ( i_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_19_1[i_2];
            return [ deduped_3_1, hoisted_16_1{Positions( deduped_19_1, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_19_1 )][1];
        end );
    deduped_14_1 := [ 1 .. Sum( List( deduped_18_1, function ( i_2 )
                  return deduped_23_1;
              end ) ) ];
    deduped_12_1 := UnderlyingIrreducibleCharacters( cat_1 );
    deduped_11_1 := deduped_26_1[2];
    hoisted_8_1 := deduped_26_1[3];
    deduped_9_1 := List( deduped_20_1, function ( n_2 )
            return hoisted_8_1[n_2];
        end );
    hoisted_7_1 := [ deduped_24_1 ];
    deduped_4_1 := BigInt( 1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, s_1, r_1, TripleOfNrSupportListOfSupportListOfNrBlockColumnsAndListOfBlockColumns, NTuple( 3, deduped_21_1, deduped_22_1, List( [ 1 .. deduped_21_1 ], function ( k_2 )
                local deduped_1_2, hoisted_2_2, deduped_3_2;
                deduped_1_2 := deduped_22_1[k_2];
                hoisted_2_2 := Concatenation( List( deduped_18_1, function ( i_3 )
                          local hoisted_2_3, deduped_3_3;
                          deduped_3_3 := deduped_19_1[i_3];
                          hoisted_2_3 := [ deduped_3_1, hoisted_17_1{Positions( deduped_19_1, deduped_3_3 )} ][1 + BooleanToInteger( deduped_3_3 in deduped_19_1 )][1];
                          return List( deduped_20_1, function ( j_4 )
                                  return hoisted_2_3 * (deduped_9_1[j_4] * SGREPS_ScalarProduct( deduped_12_1, deduped_1_2, deduped_3_3, deduped_11_1[j_4] ));
                              end );
                      end ) );
                deduped_3_2 := List( deduped_15_1, function ( l_3 )
                        local hoisted_1_3, hoisted_2_3, deduped_3_3;
                        hoisted_1_3 := [ 1 .. l_3 - 1 ];
                        hoisted_2_3 := List( deduped_18_1, function ( i_4 )
                                local deduped_1_4, deduped_2_4, deduped_3_4, deduped_4_4;
                                deduped_1_4 := deduped_19_1[i_4];
                                deduped_4_4 := List( L_1, function ( object_5 )
                                        local hoisted_1_5, deduped_2_5, deduped_3_5;
                                        deduped_3_5 := TripleOfNrSupportListOfSupportListOfNumberElements( object_5 );
                                        deduped_2_5 := deduped_3_5[2];
                                        hoisted_1_5 := deduped_3_5[3];
                                        return [ deduped_3_1, List( [ 1 .. deduped_3_5[1] ], function ( n_6 )
                                                          return hoisted_1_5[n_6];
                                                      end ){Positions( deduped_2_5, deduped_1_4 )} ][1 + BooleanToInteger( deduped_1_4 in deduped_2_5 )][1];
                                    end );
                                deduped_3_4 := deduped_4_4[l_3];
                                deduped_2_4 := Sum( deduped_4_4{hoisted_1_3} );
                                return [ NTuple( 2, deduped_4_1, [ NTuple( 2, deduped_2_4 + 1, deduped_2_4 + deduped_3_4 ) ] ), deduped_24_1 ][1 + BooleanToInteger( deduped_3_4 = 0 )];
                            end );
                        deduped_3_3 := Concatenation( List( deduped_18_1, function ( i_4 )
                                  local deduped_1_4, hoisted_3_4, deduped_5_4, deduped_6_4, deduped_7_4;
                                  deduped_7_4 := deduped_19_1[i_4];
                                  deduped_6_4 := [ hoisted_7_1, hoisted_2_3{Positions( deduped_19_1, deduped_7_4 )} ][1 + BooleanToInteger( deduped_7_4 in deduped_19_1 )][1];
                                  deduped_5_4 := [ 1 .. deduped_6_4[1] ];
                                  deduped_1_4 := deduped_6_4[2];
                                  hoisted_3_4 := Sum( List( deduped_5_4, function ( i_5 )
                                            local deduped_1_5;
                                            deduped_1_5 := deduped_1_4[i_5];
                                            return deduped_1_5[2] - deduped_1_5[1] + deduped_4_1;
                                        end ) );
                                  return List( deduped_20_1, function ( j_5 )
                                          local hoisted_1_5, hoisted_3_5, deduped_4_5, deduped_5_5, deduped_6_5;
                                          deduped_6_5 := deduped_9_1[j_5] * SGREPS_ScalarProduct( deduped_12_1, deduped_1_2, deduped_7_4, deduped_11_1[j_5] );
                                          deduped_5_5 := [ NTuple( 2, deduped_4_1, [ NTuple( 2, deduped_4_1, deduped_6_5 ) ] ), deduped_24_1 ][1 + BooleanToInteger( deduped_6_5 = 0 )];
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
                        return NTuple( 2, Sum( List( deduped_14_1, function ( i_4 )
                                    return deduped_3_3[i_4][1];
                                end ) ), Concatenation( List( deduped_14_1, function ( i_4 )
                                    local deduped_1_4;
                                    deduped_1_4 := Sum( List( [ 1 .. i_4 - 1 ], function ( j_5 )
                                              return hoisted_2_2[j_5];
                                          end ) );
                                    return List( deduped_3_3[i_4][2], function ( col_5 )
                                            return NTuple( 2, col_5[1] + deduped_1_4, col_5[2] + deduped_1_4 );
                                        end );
                                end ) ) );
                    end );
                return NTuple( 2, Sum( List( deduped_15_1, function ( i_3 )
                            return deduped_3_2[i_3][1];
                        end ) ), Concatenation( List( deduped_15_1, function ( i_3 )
                            return deduped_3_2[i_3][2];
                        end ) ) );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.RightDistributivityExpandingWithGivenObjects :=
        
########
function ( cat_1, s_1, L_1, a_1, r_1 )
    local deduped_3_1, deduped_4_1, hoisted_7_1, hoisted_8_1, deduped_9_1, deduped_11_1, deduped_12_1, deduped_14_1, deduped_15_1, hoisted_16_1, hoisted_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1, deduped_26_1, deduped_27_1;
    deduped_27_1 := BigInt( 0 );
    deduped_26_1 := TripleOfNrSupportListOfSupportListOfNumberElements( a_1 );
    deduped_25_1 := TripleOfNrSupportListOfSupportListOfNumberElements( r_1 );
    deduped_24_1 := NTuple( 2, deduped_27_1, CapJitTypedExpression( [  ], function (  )
              return rec(
                  filter := IsList,
                  element_type := rec(
                      filter := IsNTuple,
                      element_types := [ rec(
                              filter := IsInt ), rec(
                              filter := IsInt ) ] ) );
          end ) );
    deduped_23_1 := deduped_26_1[1];
    deduped_22_1 := deduped_25_1[2];
    deduped_21_1 := deduped_25_1[1];
    deduped_20_1 := [ 1 .. deduped_23_1 ];
    deduped_19_1 := Union( List( L_1, function ( object_2 )
              return TripleOfNrSupportListOfSupportListOfNumberElements( object_2 )[2];
          end ) );
    deduped_18_1 := [ 1 .. Length( deduped_19_1 ) ];
    deduped_15_1 := [ 1 .. Length( L_1 ) ];
    deduped_3_1 := [ deduped_27_1 ];
    hoisted_16_1 := List( deduped_18_1, function ( n_2 )
            local deduped_1_2, hoisted_2_2;
            deduped_1_2 := deduped_19_1[n_2];
            hoisted_2_2 := List( L_1, function ( object_3 )
                    local hoisted_1_3, deduped_2_3, deduped_3_3;
                    deduped_3_3 := TripleOfNrSupportListOfSupportListOfNumberElements( object_3 );
                    deduped_2_3 := deduped_3_3[2];
                    hoisted_1_3 := deduped_3_3[3];
                    return [ deduped_3_1, List( [ 1 .. deduped_3_3[1] ], function ( n_4 )
                                      return hoisted_1_3[n_4];
                                  end ){Positions( deduped_2_3, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_2_3 )][1];
                end );
            return Sum( List( deduped_15_1, function ( i_3 )
                      return hoisted_2_2[i_3];
                  end ) );
        end );
    hoisted_17_1 := List( deduped_18_1, function ( i_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_19_1[i_2];
            return [ deduped_3_1, hoisted_16_1{Positions( deduped_19_1, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_19_1 )][1];
        end );
    deduped_14_1 := [ 1 .. Sum( List( deduped_18_1, function ( i_2 )
                  return deduped_23_1;
              end ) ) ];
    deduped_12_1 := UnderlyingIrreducibleCharacters( cat_1 );
    deduped_11_1 := deduped_26_1[2];
    hoisted_8_1 := deduped_26_1[3];
    deduped_9_1 := List( deduped_20_1, function ( n_2 )
            return hoisted_8_1[n_2];
        end );
    hoisted_7_1 := [ deduped_24_1 ];
    deduped_4_1 := BigInt( 1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, s_1, r_1, TripleOfNrSupportListOfSupportListOfNrBlockColumnsAndListOfBlockColumns, NTuple( 3, deduped_21_1, deduped_22_1, List( [ 1 .. deduped_21_1 ], function ( k_2 )
                local deduped_1_2, hoisted_2_2, deduped_3_2;
                deduped_1_2 := deduped_22_1[k_2];
                hoisted_2_2 := Concatenation( List( deduped_18_1, function ( i_3 )
                          local hoisted_2_3, deduped_3_3;
                          deduped_3_3 := deduped_19_1[i_3];
                          hoisted_2_3 := [ deduped_3_1, hoisted_17_1{Positions( deduped_19_1, deduped_3_3 )} ][1 + BooleanToInteger( deduped_3_3 in deduped_19_1 )][1];
                          return List( deduped_20_1, function ( j_4 )
                                  return hoisted_2_3 * (deduped_9_1[j_4] * SGREPS_ScalarProduct( deduped_12_1, deduped_1_2, deduped_3_3, deduped_11_1[j_4] ));
                              end );
                      end ) );
                deduped_3_2 := List( deduped_15_1, function ( l_3 )
                        local hoisted_1_3, hoisted_2_3, deduped_3_3;
                        hoisted_1_3 := [ 1 .. l_3 - 1 ];
                        hoisted_2_3 := List( deduped_18_1, function ( i_4 )
                                local deduped_1_4, deduped_2_4, deduped_3_4, deduped_4_4;
                                deduped_1_4 := deduped_19_1[i_4];
                                deduped_4_4 := List( L_1, function ( object_5 )
                                        local hoisted_1_5, deduped_2_5, deduped_3_5;
                                        deduped_3_5 := TripleOfNrSupportListOfSupportListOfNumberElements( object_5 );
                                        deduped_2_5 := deduped_3_5[2];
                                        hoisted_1_5 := deduped_3_5[3];
                                        return [ deduped_3_1, List( [ 1 .. deduped_3_5[1] ], function ( n_6 )
                                                          return hoisted_1_5[n_6];
                                                      end ){Positions( deduped_2_5, deduped_1_4 )} ][1 + BooleanToInteger( deduped_1_4 in deduped_2_5 )][1];
                                    end );
                                deduped_3_4 := deduped_4_4[l_3];
                                deduped_2_4 := Sum( deduped_4_4{hoisted_1_3} );
                                return [ NTuple( 2, deduped_4_1, [ NTuple( 2, deduped_2_4 + 1, deduped_2_4 + deduped_3_4 ) ] ), deduped_24_1 ][1 + BooleanToInteger( deduped_3_4 = 0 )];
                            end );
                        deduped_3_3 := Concatenation( List( deduped_18_1, function ( i_4 )
                                  local deduped_1_4, hoisted_3_4, deduped_5_4, deduped_6_4, deduped_7_4;
                                  deduped_7_4 := deduped_19_1[i_4];
                                  deduped_6_4 := [ hoisted_7_1, hoisted_2_3{Positions( deduped_19_1, deduped_7_4 )} ][1 + BooleanToInteger( deduped_7_4 in deduped_19_1 )][1];
                                  deduped_5_4 := [ 1 .. deduped_6_4[1] ];
                                  deduped_1_4 := deduped_6_4[2];
                                  hoisted_3_4 := Sum( List( deduped_5_4, function ( i_5 )
                                            local deduped_1_5;
                                            deduped_1_5 := deduped_1_4[i_5];
                                            return deduped_1_5[2] - deduped_1_5[1] + deduped_4_1;
                                        end ) );
                                  return List( deduped_20_1, function ( j_5 )
                                          local hoisted_1_5, hoisted_3_5, deduped_4_5, deduped_5_5, deduped_6_5;
                                          deduped_6_5 := deduped_9_1[j_5] * SGREPS_ScalarProduct( deduped_12_1, deduped_1_2, deduped_7_4, deduped_11_1[j_5] );
                                          deduped_5_5 := [ NTuple( 2, deduped_4_1, [ NTuple( 2, deduped_4_1, deduped_6_5 ) ] ), deduped_24_1 ][1 + BooleanToInteger( deduped_6_5 = 0 )];
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
                        return NTuple( 2, Sum( List( deduped_14_1, function ( i_4 )
                                    return deduped_3_3[i_4][1];
                                end ) ), Concatenation( List( deduped_14_1, function ( i_4 )
                                    local deduped_1_4;
                                    deduped_1_4 := Sum( List( [ 1 .. i_4 - 1 ], function ( j_5 )
                                              return hoisted_2_2[j_5];
                                          end ) );
                                    return List( deduped_3_3[i_4][2], function ( col_5 )
                                            return NTuple( 2, col_5[1] + deduped_1_4, col_5[2] + deduped_1_4 );
                                        end );
                                end ) ) );
                    end );
                return NTuple( 2, Sum( List( deduped_15_1, function ( i_3 )
                            return deduped_3_2[i_3][1];
                        end ) ), Concatenation( List( deduped_15_1, function ( i_3 )
                            return deduped_3_2[i_3][2];
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

BindGlobal( "SparseProduct_KroneckerComonoids_In_SkeletalGroupRepresentations_S4_precompiled", function ( irreducible_characters )
  local category_constructor, cat;
    
    category_constructor :=
        
        
        function ( irreducible_characters )
    return SubcategoryOfSkeletalCategoryOfGroupRepresentationsOfSparseProductOfKroneckerComonoids( irreducible_characters : no_precompiled_code := true );
end;
        
        
    
    cat := category_constructor( irreducible_characters : FinalizeCategory := false, no_precompiled_code := true );
    
    ADD_FUNCTIONS_FOR_Subcategory_SkeletalCategoryOfGroupRepresentations_S4_SparseProduct_KroneckerComonoids_precompiled( cat );
    
    Finalize( cat );
    
    return cat;
    
end );
