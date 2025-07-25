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
    local hoisted_2_1, deduped_3_1, hoisted_4_1, deduped_5_1, hoisted_7_1, hoisted_8_1, deduped_9_1, hoisted_11_1, hoisted_12_1, hoisted_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1;
    deduped_19_1 := TripleOfNrSupportListOfSupportListOfRanks( a_1 );
    deduped_18_1 := TripleOfNrSupportListOfSupportListOfRanks( s_1 );
    deduped_17_1 := deduped_18_1[2];
    deduped_16_1 := deduped_18_1[1];
    deduped_15_1 := Union( List( L_1, function ( x_2 )
              return TripleOfNrSupportListOfSupportListOfRanks( x_2 )[2];
          end ) );
    deduped_14_1 := [ 1 .. Length( deduped_15_1 ) ];
    hoisted_13_1 := [ 1 .. Length( L_1 ) ];
    hoisted_11_1 := [ 0 ];
    hoisted_12_1 := List( deduped_14_1, function ( n_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_15_1[CAP_JIT_INCOMPLETE_LOGIC( n_2 )];
            return CAP_JIT_INCOMPLETE_LOGIC( Sum( List( L_1, function ( x_3 )
                        local hoisted_1_3, deduped_2_3, deduped_3_3;
                        deduped_3_3 := TripleOfNrSupportListOfSupportListOfRanks( x_3 );
                        deduped_2_3 := deduped_3_3[2];
                        hoisted_1_3 := deduped_3_3[3];
                        return [ hoisted_11_1, List( [ 1 .. deduped_3_3[1] ], function ( n_4 )
                                          return hoisted_1_3[n_4];
                                      end ){Positions( deduped_2_3, deduped_1_2 )} ][BooleanToInteger( deduped_1_2 in deduped_2_3 ) + 1][1];
                    end ) ) );
        end );
    deduped_9_1 := [ 1 .. deduped_19_1[1] ];
    hoisted_8_1 := deduped_19_1[2];
    hoisted_7_1 := deduped_19_1[3];
    deduped_5_1 := List( L_1, TripleOfNrSupportListOfSupportListOfRanks );
    hoisted_4_1 := UnderlyingSplittingField( cat_1 );
    deduped_3_1 := [ BigInt( 0 ) ];
    hoisted_2_1 := deduped_18_1[3];
    return CreateCapCategoryMorphismWithAttributes( cat_1, s_1, r_1, TripleOfNrSupportListOfSupportListOfMatrices, NTuple( 3, deduped_16_1, deduped_17_1, List( [ 1 .. deduped_16_1 ], function ( i_2 )
                local hoisted_1_2, deduped_2_2, deduped_3_2, deduped_4_2;
                deduped_4_2 := deduped_17_1[i_2];
                hoisted_1_2 := deduped_17_1[CAP_JIT_INCOMPLETE_LOGIC( i_2 )];
                deduped_2_2 := List( deduped_14_1, function ( i_3 )
                        local hoisted_1_3;
                        hoisted_1_3 := deduped_15_1[i_3];
                        return List( deduped_9_1, function ( j_4 )
                                return hoisted_7_1[j_4] * SGREPS_ScalarProduct( cat_1, hoisted_1_2, hoisted_1_3, hoisted_8_1[j_4] );
                            end );
                    end );
                deduped_3_2 := List( deduped_14_1, function ( i_3 )
                        local hoisted_1_3, hoisted_2_3, deduped_3_3;
                        deduped_3_3 := deduped_15_1[i_3];
                        hoisted_2_3 := [ deduped_3_1, hoisted_12_1{Positions( deduped_15_1, deduped_3_3 )} ][1 + BooleanToInteger( deduped_3_3 in deduped_15_1 )][1];
                        hoisted_1_3 := deduped_2_2[i_3];
                        return List( deduped_9_1, function ( j_4 )
                                return hoisted_2_3 * hoisted_1_3[j_4];
                            end );
                    end );
                return CertainColumns( HomalgIdentityMatrix( [ deduped_3_1, hoisted_2_1{Positions( deduped_17_1, deduped_4_2 )} ][1 + BooleanToInteger( deduped_4_2 in deduped_17_1 )][1], hoisted_4_1 ), CAP_JIT_INCOMPLETE_LOGIC( Concatenation( List( hoisted_13_1, function ( l_3 )
                              local deduped_1_3, hoisted_2_3, hoisted_3_3, deduped_4_3;
                              deduped_4_3 := deduped_5_1[l_3];
                              hoisted_3_3 := [ 1 .. l_3 - 1 ];
                              hoisted_2_3 := deduped_4_3[3];
                              deduped_1_3 := deduped_4_3[2];
                              return Concatenation( List( deduped_14_1, function ( i_4 )
                                        local hoisted_1_4, hoisted_2_4, hoisted_3_4, hoisted_4_4, hoisted_6_4, deduped_7_4;
                                        deduped_7_4 := deduped_15_1[i_4];
                                        hoisted_6_4 := Sum( List( hoisted_3_3, function ( m_5 )
                                                  local deduped_1_5, deduped_2_5;
                                                  deduped_2_5 := deduped_5_1[m_5];
                                                  deduped_1_5 := deduped_2_5[2];
                                                  return [ deduped_3_1, deduped_2_5[3]{Positions( deduped_1_5, deduped_7_4 )} ][1 + BooleanToInteger( deduped_7_4 in deduped_1_5 )][1];
                                              end ) );
                                        hoisted_4_4 := Sum( Concatenation( deduped_3_2{[ 1 .. i_4 - 1 ]} ) );
                                        hoisted_3_4 := deduped_3_2[i_4];
                                        hoisted_2_4 := [ deduped_3_1, hoisted_2_3{Positions( deduped_1_3, deduped_7_4 )} ][1 + BooleanToInteger( deduped_7_4 in deduped_1_3 )][1];
                                        hoisted_1_4 := deduped_2_2[i_4];
                                        return Concatenation( List( deduped_9_1, function ( j_5 )
                                                  local hoisted_1_5, deduped_2_5;
                                                  deduped_2_5 := hoisted_1_4[j_5];
                                                  hoisted_1_5 := hoisted_4_4 + Sum( hoisted_3_4{[ 1 .. j_5 - 1 ]} ) + hoisted_6_4 * deduped_2_5;
                                                  return List( [ 1 .. hoisted_2_4 * deduped_2_5 ], function ( m_6 )
                                                          return hoisted_1_5 + m_6;
                                                      end );
                                              end ) );
                                    end ) );
                          end ) ) ) );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.RightDistributivityExpandingWithGivenObjects :=
        
########
function ( cat_1, s_1, L_1, a_1, r_1 )
    local hoisted_2_1, deduped_3_1, hoisted_4_1, deduped_5_1, hoisted_7_1, hoisted_8_1, deduped_9_1, hoisted_11_1, hoisted_12_1, hoisted_13_1, hoisted_14_1, hoisted_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1;
    deduped_22_1 := TripleOfNrSupportListOfSupportListOfRanks( a_1 );
    deduped_21_1 := TripleOfNrSupportListOfSupportListOfRanks( s_1 );
    deduped_20_1 := deduped_21_1[2];
    deduped_19_1 := deduped_21_1[1];
    deduped_18_1 := [ 1 .. deduped_19_1 ];
    deduped_17_1 := Union( List( L_1, function ( x_2 )
              return TripleOfNrSupportListOfSupportListOfRanks( x_2 )[2];
          end ) );
    deduped_16_1 := [ 1 .. Length( deduped_17_1 ) ];
    hoisted_14_1 := [ 1 .. Length( L_1 ) ];
    hoisted_11_1 := [ 0 ];
    hoisted_12_1 := List( deduped_16_1, function ( n_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_17_1[n_2];
            return Sum( List( L_1, function ( x_3 )
                      local hoisted_1_3, deduped_2_3, deduped_3_3;
                      deduped_3_3 := TripleOfNrSupportListOfSupportListOfRanks( x_3 );
                      deduped_2_3 := deduped_3_3[2];
                      hoisted_1_3 := deduped_3_3[3];
                      return [ hoisted_11_1, List( [ 1 .. deduped_3_3[1] ], function ( n_4 )
                                        return hoisted_1_3[n_4];
                                    end ){Positions( deduped_2_3, deduped_1_2 )} ][BooleanToInteger( deduped_1_2 in deduped_2_3 ) + 1][1];
                  end ) );
        end );
    hoisted_13_1 := List( deduped_16_1, function ( n_2 )
            return hoisted_12_1[n_2];
        end );
    deduped_9_1 := [ 1 .. deduped_22_1[1] ];
    hoisted_8_1 := deduped_22_1[2];
    hoisted_7_1 := deduped_22_1[3];
    deduped_5_1 := List( L_1, TripleOfNrSupportListOfSupportListOfRanks );
    deduped_3_1 := [ BigInt( 0 ) ];
    hoisted_15_1 := List( deduped_18_1, function ( k_2 )
            local hoisted_1_2, deduped_2_2, deduped_3_2;
            hoisted_1_2 := deduped_20_1[k_2];
            deduped_2_2 := List( deduped_16_1, function ( i_3 )
                    local hoisted_1_3;
                    hoisted_1_3 := deduped_17_1[i_3];
                    return List( deduped_9_1, function ( j_4 )
                            return hoisted_7_1[j_4] * SGREPS_ScalarProduct( cat_1, hoisted_1_2, hoisted_1_3, hoisted_8_1[j_4] );
                        end );
                end );
            deduped_3_2 := List( deduped_16_1, function ( i_3 )
                    local hoisted_1_3, hoisted_2_3, deduped_3_3;
                    deduped_3_3 := deduped_17_1[i_3];
                    hoisted_2_3 := [ deduped_3_1, hoisted_13_1{Positions( deduped_17_1, deduped_3_3 )} ][1 + BooleanToInteger( deduped_3_3 in deduped_17_1 )][1];
                    hoisted_1_3 := deduped_2_2[i_3];
                    return List( deduped_9_1, function ( j_4 )
                            return hoisted_2_3 * hoisted_1_3[j_4];
                        end );
                end );
            return Concatenation( List( hoisted_14_1, function ( l_3 )
                      local deduped_1_3, hoisted_2_3, hoisted_3_3, deduped_4_3;
                      deduped_4_3 := deduped_5_1[l_3];
                      hoisted_3_3 := [ 1 .. l_3 - 1 ];
                      hoisted_2_3 := deduped_4_3[3];
                      deduped_1_3 := deduped_4_3[2];
                      return Concatenation( List( deduped_16_1, function ( i_4 )
                                local hoisted_1_4, hoisted_2_4, hoisted_3_4, hoisted_4_4, hoisted_6_4, deduped_7_4;
                                deduped_7_4 := deduped_17_1[i_4];
                                hoisted_6_4 := Sum( List( hoisted_3_3, function ( m_5 )
                                          local deduped_1_5, deduped_2_5;
                                          deduped_2_5 := deduped_5_1[m_5];
                                          deduped_1_5 := deduped_2_5[2];
                                          return [ deduped_3_1, deduped_2_5[3]{Positions( deduped_1_5, deduped_7_4 )} ][1 + BooleanToInteger( deduped_7_4 in deduped_1_5 )][1];
                                      end ) );
                                hoisted_4_4 := Sum( Concatenation( deduped_3_2{[ 1 .. i_4 - 1 ]} ) );
                                hoisted_3_4 := deduped_3_2[i_4];
                                hoisted_2_4 := [ deduped_3_1, hoisted_2_3{Positions( deduped_1_3, deduped_7_4 )} ][1 + BooleanToInteger( deduped_7_4 in deduped_1_3 )][1];
                                hoisted_1_4 := deduped_2_2[i_4];
                                return Concatenation( List( deduped_9_1, function ( j_5 )
                                          local hoisted_1_5, deduped_2_5;
                                          deduped_2_5 := hoisted_1_4[j_5];
                                          hoisted_1_5 := hoisted_4_4 + Sum( hoisted_3_4{[ 1 .. j_5 - 1 ]} ) + hoisted_6_4 * deduped_2_5;
                                          return List( [ 1 .. hoisted_2_4 * deduped_2_5 ], function ( m_6 )
                                                  return hoisted_1_5 + m_6;
                                              end );
                                      end ) );
                            end ) );
                  end ) );
        end );
    hoisted_4_1 := UnderlyingSplittingField( cat_1 );
    hoisted_2_1 := deduped_21_1[3];
    return CreateCapCategoryMorphismWithAttributes( cat_1, s_1, r_1, TripleOfNrSupportListOfSupportListOfMatrices, NTuple( 3, deduped_19_1, deduped_20_1, List( deduped_18_1, function ( i_2 )
                local deduped_1_2;
                deduped_1_2 := deduped_20_1[i_2];
                return CertainColumns( HomalgIdentityMatrix( [ deduped_3_1, hoisted_2_1{Positions( deduped_20_1, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_20_1 )][1], hoisted_4_1 ), hoisted_15_1[i_2] );
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
