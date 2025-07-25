# SPDX-License-Identifier: GPL-2.0-or-later
# AdditiveClosuresForCAP: Additive closures for pre-additive categories
#
# Implementations
#
BindGlobal( "ADD_FUNCTIONS_FOR_AdditiveClosureOfObjectFiniteDisconnectedCategory_LinearClosure_over_Field_DiscreteCategory_precompiled", function ( cat )
    
    ##
    AddIsEqualForObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    return NrSummandsAndMultiplicities( arg2_1 ) = NrSummandsAndMultiplicities( arg3_1 );
end
########
        
    , 100 );
    
    ##
    AddIdentityMorphism( cat,
        
########
function ( cat_1, a_1 )
    local hoisted_1_1, hoisted_3_1, hoisted_4_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, deduped_9_1, deduped_10_1;
    deduped_10_1 := UnderlyingCategory( cat_1 );
    deduped_9_1 := ListOfObjectsOfUnderlyingCategory( cat_1 );
    hoisted_8_1 := [  ];
    hoisted_7_1 := [  ];
    hoisted_6_1 := [ OneImmutable( CommutativeRingOfLinearCategory( deduped_10_1 ) ) ];
    hoisted_4_1 := UnderlyingCategory( deduped_10_1 );
    hoisted_3_1 := List( deduped_9_1, UnderlyingOriginalObject );
    hoisted_1_1 := NrSummandsAndMultiplicities( a_1 )[2];
    return CreateCapCategoryMorphismWithAttributes( cat_1, a_1, a_1, ListOfMatrices, List( [ 1 .. NumberOfObjectsOfUnderlyingCategory( cat_1 ) ], function ( n_2 )
              local deduped_2_2;
              deduped_2_2 := [ 1 .. hoisted_1_1[n_2] ];
              return List( deduped_2_2, function ( i_3 )
                      local hoisted_1_3, deduped_3_3, deduped_4_3;
                      deduped_4_3 := hoisted_3_1[i_3];
                      deduped_3_3 := deduped_9_1[i_3];
                      hoisted_1_3 := CreateCapCategoryMorphismWithAttributes( deduped_10_1, deduped_3_3, deduped_3_3, CoefficientsList, hoisted_6_1, SupportMorphisms, [ CreateCapCategoryMorphismWithAttributes( hoisted_4_1, deduped_4_3, deduped_4_3 ) ] );
                      return List( deduped_2_2, function ( j_4 )
                              if i_3 = j_4 then
                                  return hoisted_1_3;
                              else
                                  return CreateCapCategoryMorphismWithAttributes( deduped_10_1, deduped_3_3, deduped_9_1[j_4], CoefficientsList, hoisted_7_1, SupportMorphisms, hoisted_8_1 );
                              fi;
                              return;
                          end );
                  end );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddPreCompose( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    local hoisted_3_1, hoisted_4_1, deduped_5_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, hoisted_9_1, hoisted_10_1, hoisted_11_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1;
    deduped_17_1 := UnderlyingCategory( cat_1 );
    deduped_16_1 := ListOfMatrices( beta_1 );
    deduped_15_1 := ListOfMatrices( alpha_1 );
    deduped_14_1 := Target( beta_1 );
    deduped_13_1 := Source( alpha_1 );
    hoisted_11_1 := List( deduped_16_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_list_3 )
                    return List( logic_new_func_list_3, SupportMorphisms );
                end );
        end );
    hoisted_10_1 := List( deduped_15_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_list_3 )
                    return List( logic_new_func_list_3, SupportMorphisms );
                end );
        end );
    hoisted_9_1 := ZeroImmutable( CommutativeRingOfLinearCategory( deduped_17_1 ) );
    hoisted_8_1 := List( deduped_16_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_list_3 )
                    return List( logic_new_func_list_3, function ( logic_new_func_x_4 )
                            return Sum( CoefficientsList( logic_new_func_x_4 ) );
                        end );
                end );
        end );
    hoisted_7_1 := List( deduped_15_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_list_3 )
                    return List( logic_new_func_list_3, function ( logic_new_func_x_4 )
                            return Sum( CoefficientsList( logic_new_func_x_4 ) );
                        end );
                end );
        end );
    hoisted_6_1 := NrSummandsAndMultiplicities( Target( alpha_1 ) )[2];
    deduped_5_1 := ListOfObjectsOfUnderlyingCategory( cat_1 );
    hoisted_4_1 := NrSummandsAndMultiplicities( deduped_14_1 )[2];
    hoisted_3_1 := NrSummandsAndMultiplicities( deduped_13_1 )[2];
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_13_1, deduped_14_1, ListOfMatrices, List( [ 1 .. NumberOfObjectsOfUnderlyingCategory( cat_1 ) ], function ( n_2 )
              local hoisted_1_2, deduped_2_2, deduped_3_2, hoisted_4_2, hoisted_5_2, hoisted_6_2;
              hoisted_6_2 := [ 1 .. hoisted_4_1[n_2] ];
              hoisted_5_2 := hoisted_11_1[n_2];
              hoisted_4_2 := hoisted_10_1[n_2];
              deduped_3_2 := [ 1 .. hoisted_6_1[n_2] ];
              deduped_2_2 := hoisted_8_1[n_2];
              hoisted_1_2 := hoisted_7_1[n_2];
              return List( [ 1 .. hoisted_3_1[n_2] ], function ( i_3 )
                      local deduped_1_3, hoisted_2_3, hoisted_3_3;
                      hoisted_3_3 := deduped_5_1[i_3];
                      hoisted_2_3 := hoisted_4_2[i_3];
                      deduped_1_3 := hoisted_1_2[i_3];
                      return List( hoisted_6_2, function ( j_4 )
                              local deduped_1_4, deduped_2_4;
                              deduped_2_4 := Sum( Concatenation( List( deduped_3_2, function ( k_5 )
                                          local deduped_1_5;
                                          deduped_1_5 := deduped_1_3[k_5] * deduped_2_2[k_5][j_4];
                                          return [ deduped_1_5 ]{[ 1 .. BooleanToInteger( not IsZero( deduped_1_5 ) ) ]};
                                      end ) ), hoisted_9_1 );
                              deduped_1_4 := [ 1 .. BooleanToInteger( not IsZero( deduped_2_4 ) ) ];
                              return CreateCapCategoryMorphismWithAttributes( deduped_17_1, hoisted_3_3, deduped_5_1[j_4], CoefficientsList, [ deduped_2_4 ]{deduped_1_4}, SupportMorphisms, Concatenation( List( deduped_3_2, function ( k_5 )
                                            return Concatenation( hoisted_2_3[k_5], hoisted_5_2[k_5][j_4] ){[ 1 .. BooleanToInteger( not IsZero( deduped_1_3[k_5] * deduped_2_2[k_5][j_4] ) ) ]};
                                        end ) ){deduped_1_4} );
                          end );
                  end );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddZeroMorphism( cat,
        
########
function ( cat_1, a_1, b_1 )
    local hoisted_1_1, hoisted_2_1, deduped_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1;
    hoisted_6_1 := [  ];
    hoisted_5_1 := [  ];
    hoisted_4_1 := UnderlyingCategory( cat_1 );
    deduped_3_1 := ListOfObjectsOfUnderlyingCategory( cat_1 );
    hoisted_2_1 := NrSummandsAndMultiplicities( b_1 )[2];
    hoisted_1_1 := NrSummandsAndMultiplicities( a_1 )[2];
    return CreateCapCategoryMorphismWithAttributes( cat_1, a_1, b_1, ListOfMatrices, List( [ 1 .. NumberOfObjectsOfUnderlyingCategory( cat_1 ) ], function ( n_2 )
              local hoisted_1_2;
              hoisted_1_2 := [ 1 .. hoisted_2_1[n_2] ];
              return List( [ 1 .. hoisted_1_1[n_2] ], function ( i_3 )
                      local hoisted_1_3;
                      hoisted_1_3 := deduped_3_1[i_3];
                      return List( hoisted_1_2, function ( j_4 )
                              return CreateCapCategoryMorphismWithAttributes( hoisted_4_1, hoisted_1_3, deduped_3_1[j_4], CoefficientsList, hoisted_5_1, SupportMorphisms, hoisted_6_1 );
                          end );
                  end );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddIsZeroForMorphisms( cat,
        
########
function ( cat_1, arg2_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, deduped_5_1;
    deduped_5_1 := ListOfMatrices( arg2_1 );
    hoisted_4_1 := List( deduped_5_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_list_3 )
                    return List( logic_new_func_list_3, function ( logic_new_func_x_4 )
                            return IsEmpty( SupportMorphisms( logic_new_func_x_4 ) );
                        end );
                end );
        end );
    hoisted_3_1 := List( deduped_5_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_list_3 )
                    return List( logic_new_func_list_3, function ( logic_new_func_x_4 )
                            return IsEmpty( CoefficientsList( logic_new_func_x_4 ) );
                        end );
                end );
        end );
    hoisted_2_1 := NrSummandsAndMultiplicities( Target( arg2_1 ) )[2];
    hoisted_1_1 := NrSummandsAndMultiplicities( Source( arg2_1 ) )[2];
    return ForAll( [ 1 .. NumberOfObjectsOfUnderlyingCategory( cat_1 ) ], function ( n_2 )
            local hoisted_1_2, hoisted_2_2, hoisted_3_2;
            hoisted_3_2 := [ 1 .. hoisted_2_1[n_2] ];
            hoisted_2_2 := hoisted_4_1[n_2];
            hoisted_1_2 := hoisted_3_1[n_2];
            return ForAll( [ 1 .. hoisted_1_1[n_2] ], function ( i_3 )
                    local hoisted_1_3, hoisted_2_3;
                    hoisted_2_3 := hoisted_2_2[i_3];
                    hoisted_1_3 := hoisted_1_2[i_3];
                    return ForAll( hoisted_3_2, function ( j_4 )
                            return hoisted_1_3[j_4] and hoisted_2_3[j_4];
                        end );
                end );
        end );
end
########
        
    , 100 );
    
    ##
    AddAdditionForMorphisms( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    local hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, hoisted_9_1, hoisted_10_1, hoisted_11_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1;
    deduped_17_1 := UnderlyingCategory( cat_1 );
    deduped_16_1 := ListOfMatrices( beta_1 );
    deduped_15_1 := ListOfMatrices( alpha_1 );
    deduped_14_1 := Target( alpha_1 );
    deduped_13_1 := Source( alpha_1 );
    hoisted_11_1 := List( deduped_16_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_list_3 )
                    return List( logic_new_func_list_3, SupportMorphisms );
                end );
        end );
    hoisted_10_1 := List( deduped_15_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_list_3 )
                    return List( logic_new_func_list_3, SupportMorphisms );
                end );
        end );
    hoisted_9_1 := ZeroImmutable( CommutativeRingOfLinearCategory( deduped_17_1 ) );
    hoisted_8_1 := List( deduped_16_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_list_3 )
                    return List( logic_new_func_list_3, CoefficientsList );
                end );
        end );
    hoisted_7_1 := List( deduped_15_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_list_3 )
                    return List( logic_new_func_list_3, CoefficientsList );
                end );
        end );
    hoisted_6_1 := List( deduped_15_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_list_3 )
                    return List( logic_new_func_list_3, Target );
                end );
        end );
    hoisted_5_1 := List( deduped_15_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_list_3 )
                    return List( logic_new_func_list_3, Source );
                end );
        end );
    hoisted_4_1 := NrSummandsAndMultiplicities( deduped_14_1 )[2];
    hoisted_3_1 := NrSummandsAndMultiplicities( deduped_13_1 )[2];
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_13_1, deduped_14_1, ListOfMatrices, List( [ 1 .. NumberOfObjectsOfUnderlyingCategory( cat_1 ) ], function ( n_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, hoisted_4_2, hoisted_5_2, hoisted_6_2, hoisted_7_2;
              hoisted_7_2 := [ 1 .. hoisted_4_1[n_2] ];
              hoisted_6_2 := hoisted_11_1[n_2];
              hoisted_5_2 := hoisted_10_1[n_2];
              hoisted_4_2 := hoisted_8_1[n_2];
              hoisted_3_2 := hoisted_7_1[n_2];
              hoisted_2_2 := hoisted_6_1[n_2];
              hoisted_1_2 := hoisted_5_1[n_2];
              return List( [ 1 .. hoisted_3_1[n_2] ], function ( i_3 )
                      local hoisted_1_3, hoisted_2_3, hoisted_3_3, hoisted_4_3, hoisted_5_3, hoisted_6_3;
                      hoisted_6_3 := hoisted_6_2[i_3];
                      hoisted_5_3 := hoisted_5_2[i_3];
                      hoisted_4_3 := hoisted_4_2[i_3];
                      hoisted_3_3 := hoisted_3_2[i_3];
                      hoisted_2_3 := hoisted_2_2[i_3];
                      hoisted_1_3 := hoisted_1_2[i_3];
                      return List( hoisted_7_2, function ( j_4 )
                              local deduped_1_4, deduped_2_4;
                              deduped_2_4 := Sum( Concatenation( hoisted_3_3[j_4], hoisted_4_3[j_4] ), hoisted_9_1 );
                              deduped_1_4 := [ 1 .. BooleanToInteger( not IsZero( deduped_2_4 ) ) ];
                              return CreateCapCategoryMorphismWithAttributes( deduped_17_1, hoisted_1_3[j_4], hoisted_2_3[j_4], CoefficientsList, [ deduped_2_4 ]{deduped_1_4}, SupportMorphisms, Concatenation( hoisted_5_3[j_4], hoisted_6_3[j_4] ){deduped_1_4} );
                          end );
                  end );
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

BindGlobal( "AdditiveClosureOfObjectFiniteDisconnectedCategory_LinearClosure_over_Field_DiscreteCategory_precompiled", function ( homalg_ring )
  local category_constructor, cat;
    
    category_constructor :=
        
        
        function ( homalg_ring )
    return AdditiveClosureOfObjectFiniteDisconnectedCategory( LinearClosure( homalg_ring, FiniteSkeletalDiscreteCategory( 3 : FinalizeCategory := true ) : FinalizeCategory := true ) );
end;
        
        
    
    cat := category_constructor( homalg_ring : FinalizeCategory := false, no_precompiled_code := true );
    
    ADD_FUNCTIONS_FOR_AdditiveClosureOfObjectFiniteDisconnectedCategory_LinearClosure_over_Field_DiscreteCategory_precompiled( cat );
    
    Finalize( cat );
    
    return cat;
    
end );
