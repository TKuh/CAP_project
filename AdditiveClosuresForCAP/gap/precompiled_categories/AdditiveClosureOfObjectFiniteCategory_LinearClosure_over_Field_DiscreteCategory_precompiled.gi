# SPDX-License-Identifier: GPL-2.0-or-later
# AdditiveClosuresForCAP: Additive closures for pre-abelian categories
#
# Implementations
#
BindGlobal( "ADD_FUNCTIONS_FOR_AdditiveClosureOfObjectFiniteCategory_LinearClosure_over_Field_DiscreteCategory_precompiled", function ( cat )
    
    ##
    AddIsEqualForObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    return NrSummandsAndMultiplicities( arg2_1 ) = NrSummandsAndMultiplicities( arg3_1 );
end
########
        
    , 100 );
    
    ##
    AddIsEqualForMorphisms( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, deduped_8_1, deduped_9_1, deduped_10_1, deduped_11_1;
    deduped_9_1 := NrSummandsAndMultiplicities( Target( arg2_1 ) )[1];
    deduped_8_1 := NrSummandsAndMultiplicities( Source( arg2_1 ) )[1];
    if deduped_8_1 <> NrSummandsAndMultiplicities( Source( arg3_1 ) )[1] then
        return false;
    elif deduped_9_1 <> NrSummandsAndMultiplicities( Target( arg3_1 ) )[1] then
        return false;
    else
        deduped_11_1 := MorphismMatrix( arg3_1 );
        deduped_10_1 := MorphismMatrix( arg2_1 );
        hoisted_7_1 := [ 1 .. deduped_9_1 ];
        hoisted_6_1 := List( deduped_11_1, function ( logic_new_func_list_2 )
                return List( logic_new_func_list_2, SupportMorphisms );
            end );
        hoisted_5_1 := List( deduped_10_1, function ( logic_new_func_list_2 )
                return List( logic_new_func_list_2, SupportMorphisms );
            end );
        hoisted_4_1 := List( deduped_11_1, function ( logic_new_func_list_2 )
                return List( logic_new_func_list_2, CoefficientsList );
            end );
        hoisted_3_1 := List( deduped_10_1, function ( logic_new_func_list_2 )
                return List( logic_new_func_list_2, CoefficientsList );
            end );
        return ForAll( [ 1 .. deduped_8_1 ], function ( i_2 )
                local hoisted_1_2, hoisted_2_2, hoisted_3_2, hoisted_4_2;
                hoisted_4_2 := hoisted_6_1[i_2];
                hoisted_3_2 := hoisted_5_1[i_2];
                hoisted_2_2 := hoisted_4_1[i_2];
                hoisted_1_2 := hoisted_3_1[i_2];
                return ForAll( hoisted_7_1, function ( j_3 )
                        return hoisted_1_2[j_3] = hoisted_2_2[j_3] and hoisted_3_2[j_3] = hoisted_4_2[j_3];
                    end );
            end );
    fi;
    return;
end
########
        
    , 100 );
    
    ##
    AddIsWellDefinedForObjects( cat,
        
########
function ( cat_1, arg2_1 )
    local deduped_1_1, deduped_2_1;
    deduped_2_1 := NrSummandsAndMultiplicities( arg2_1 );
    deduped_1_1 := deduped_2_1[2];
    if not deduped_2_1[1] = Sum( deduped_1_1 ) then
        return false;
    elif not Length( deduped_1_1 ) = NumberOfObjectsOfUnderlyingCategory( cat_1 ) then
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
    AddIsCongruentForMorphisms( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, deduped_8_1, deduped_9_1, deduped_10_1, deduped_11_1;
    deduped_9_1 := NrSummandsAndMultiplicities( Target( arg2_1 ) )[1];
    deduped_8_1 := NrSummandsAndMultiplicities( Source( arg2_1 ) )[1];
    if deduped_8_1 <> NrSummandsAndMultiplicities( Source( arg3_1 ) )[1] then
        return false;
    elif deduped_9_1 <> NrSummandsAndMultiplicities( Target( arg3_1 ) )[1] then
        return false;
    else
        deduped_11_1 := MorphismMatrix( arg3_1 );
        deduped_10_1 := MorphismMatrix( arg2_1 );
        hoisted_7_1 := [ 1 .. deduped_9_1 ];
        hoisted_6_1 := List( deduped_11_1, function ( logic_new_func_list_2 )
                return List( logic_new_func_list_2, SupportMorphisms );
            end );
        hoisted_5_1 := List( deduped_10_1, function ( logic_new_func_list_2 )
                return List( logic_new_func_list_2, SupportMorphisms );
            end );
        hoisted_4_1 := List( deduped_11_1, function ( logic_new_func_list_2 )
                return List( logic_new_func_list_2, CoefficientsList );
            end );
        hoisted_3_1 := List( deduped_10_1, function ( logic_new_func_list_2 )
                return List( logic_new_func_list_2, CoefficientsList );
            end );
        return ForAll( [ 1 .. deduped_8_1 ], function ( i_2 )
                local hoisted_1_2, hoisted_2_2, hoisted_3_2, hoisted_4_2;
                hoisted_4_2 := hoisted_6_1[i_2];
                hoisted_3_2 := hoisted_5_1[i_2];
                hoisted_2_2 := hoisted_4_1[i_2];
                hoisted_1_2 := hoisted_3_1[i_2];
                return ForAll( hoisted_7_1, function ( j_3 )
                        return hoisted_1_2[j_3] = hoisted_2_2[j_3] and hoisted_3_2[j_3] = hoisted_4_2[j_3];
                    end );
            end );
    fi;
    return;
end
########
        
    , 100 );
    
    ##
    AddIdentityMorphism( cat,
        
########
function ( cat_1, a_1 )
    local deduped_1_1, deduped_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_8_1, hoisted_9_1, hoisted_10_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1;
    deduped_16_1 := UnderlyingCategory( cat_1 );
    deduped_15_1 := ListOfObjectsOfUnderlyingCategory( cat_1 );
    deduped_14_1 := NrSummandsAndMultiplicities( a_1 );
    deduped_13_1 := [ 1 .. NumberOfObjectsOfUnderlyingCategory( cat_1 ) ];
    deduped_12_1 := [ 1 .. deduped_14_1[1] ];
    hoisted_10_1 := [  ];
    hoisted_9_1 := [  ];
    hoisted_8_1 := [ OneImmutable( CommutativeRingOfLinearCategory( cat_1 ) ) ];
    hoisted_6_1 := UnderlyingCategory( deduped_16_1 );
    hoisted_4_1 := List( deduped_15_1, UnderlyingOriginalObject );
    deduped_1_1 := deduped_14_1[2];
    hoisted_5_1 := Concatenation( List( deduped_13_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_1_1[i_2], hoisted_4_1[i_2] );
          end ) );
    deduped_3_1 := Concatenation( List( deduped_13_1, function ( i_2 )
              return ListWithIdenticalEntries( deduped_1_1[i_2], deduped_15_1[i_2] );
          end ) );
    return CreateCapCategoryMorphismWithAttributes( cat_1, a_1, a_1, MorphismMatrix, List( deduped_12_1, function ( i_2 )
              local hoisted_1_2, deduped_3_2, deduped_4_2;
              deduped_4_2 := hoisted_5_1[i_2];
              deduped_3_2 := deduped_3_1[i_2];
              hoisted_1_2 := CreateCapCategoryMorphismWithAttributes( deduped_16_1, deduped_3_2, deduped_3_2, CoefficientsList, hoisted_8_1, SupportMorphisms, [ CreateCapCategoryMorphismWithAttributes( hoisted_6_1, deduped_4_2, deduped_4_2 ) ] );
              return List( deduped_12_1, function ( j_3 )
                      if i_2 = j_3 then
                          return hoisted_1_2;
                      else
                          return CreateCapCategoryMorphismWithAttributes( deduped_16_1, deduped_3_2, deduped_3_1[j_3], CoefficientsList, hoisted_9_1, SupportMorphisms, hoisted_10_1 );
                      fi;
                      return;
                  end );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddPreCompose( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    local hoisted_3_1, deduped_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, deduped_9_1, deduped_10_1, hoisted_11_1, hoisted_12_1, hoisted_13_1, hoisted_14_1, hoisted_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1;
    deduped_22_1 := MorphismMatrix( beta_1 );
    deduped_21_1 := MorphismMatrix( alpha_1 );
    deduped_20_1 := Target( beta_1 );
    deduped_19_1 := Source( alpha_1 );
    deduped_18_1 := [ 1 .. NumberOfObjectsOfUnderlyingCategory( cat_1 ) ];
    deduped_17_1 := NrSummandsAndMultiplicities( deduped_20_1 );
    deduped_16_1 := NrSummandsAndMultiplicities( deduped_19_1 );
    hoisted_15_1 := [ 1 .. deduped_17_1[1] ];
    hoisted_14_1 := UnderlyingCategory( cat_1 );
    hoisted_13_1 := List( deduped_22_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, SupportMorphisms );
        end );
    hoisted_12_1 := List( deduped_21_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, SupportMorphisms );
        end );
    hoisted_11_1 := ZeroImmutable( CommutativeRingOfLinearCategory( cat_1 ) );
    deduped_10_1 := [ 1 .. NrSummandsAndMultiplicities( Target( alpha_1 ) )[1] ];
    deduped_9_1 := List( deduped_22_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_x_3 )
                    return Sum( CoefficientsList( logic_new_func_x_3 ) );
                end );
        end );
    hoisted_8_1 := List( deduped_21_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_x_3 )
                    return Sum( CoefficientsList( logic_new_func_x_3 ) );
                end );
        end );
    hoisted_6_1 := deduped_17_1[2];
    deduped_4_1 := ListOfObjectsOfUnderlyingCategory( cat_1 );
    hoisted_7_1 := Concatenation( List( deduped_18_1, function ( i_2 )
              return ListWithIdenticalEntries( hoisted_6_1[i_2], deduped_4_1[i_2] );
          end ) );
    hoisted_3_1 := deduped_16_1[2];
    hoisted_5_1 := Concatenation( List( deduped_18_1, function ( i_2 )
              return ListWithIdenticalEntries( hoisted_3_1[i_2], deduped_4_1[i_2] );
          end ) );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_19_1, deduped_20_1, MorphismMatrix, List( [ 1 .. deduped_16_1[1] ], function ( i_2 )
              local deduped_1_2, hoisted_2_2, hoisted_3_2;
              hoisted_3_2 := hoisted_5_1[i_2];
              hoisted_2_2 := hoisted_12_1[i_2];
              deduped_1_2 := hoisted_8_1[i_2];
              return List( hoisted_15_1, function ( j_3 )
                      local deduped_1_3, deduped_2_3;
                      deduped_2_3 := Sum( Concatenation( List( deduped_10_1, function ( k_4 )
                                  local deduped_1_4;
                                  deduped_1_4 := deduped_1_2[k_4] * deduped_9_1[k_4][j_3];
                                  return [ deduped_1_4 ]{[ 1 .. BooleanToInteger( not IsZero( deduped_1_4 ) ) ]};
                              end ) ), hoisted_11_1 );
                      deduped_1_3 := [ 1 .. BooleanToInteger( not IsZero( deduped_2_3 ) ) ];
                      return CreateCapCategoryMorphismWithAttributes( hoisted_14_1, hoisted_3_2, hoisted_7_1[j_3], CoefficientsList, [ deduped_2_3 ]{deduped_1_3}, SupportMorphisms, Concatenation( List( deduped_10_1, function ( k_4 )
                                    return Concatenation( hoisted_2_2[k_4], hoisted_13_1[k_4][j_3] ){[ 1 .. BooleanToInteger( not IsZero( deduped_1_2[k_4] * deduped_9_1[k_4][j_3] ) ) ]};
                                end ) ){deduped_1_3} );
                  end );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddObjectDatum( cat,
        
########
function ( cat_1, arg2_1 )
    return NrSummandsAndMultiplicities( arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddObjectConstructor( cat,
        
########
function ( cat_1, arg2_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, NrSummandsAndMultiplicities, arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddMorphismDatum( cat,
        
########
function ( cat_1, arg2_1 )
    return MorphismMatrix( arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddMorphismConstructor( cat,
        
########
function ( cat_1, arg2_1, arg3_1, arg4_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, arg2_1, arg4_1, MorphismMatrix, arg3_1 );
end
########
        
    , 100 );
    
    ##
    AddZeroMorphism( cat,
        
########
function ( cat_1, a_1, b_1 )
    local hoisted_1_1, deduped_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, hoisted_9_1, deduped_10_1, deduped_11_1, deduped_12_1;
    deduped_12_1 := NrSummandsAndMultiplicities( b_1 );
    deduped_11_1 := NrSummandsAndMultiplicities( a_1 );
    deduped_10_1 := [ 1 .. NumberOfObjectsOfUnderlyingCategory( cat_1 ) ];
    hoisted_9_1 := [ 1 .. deduped_12_1[1] ];
    hoisted_8_1 := [  ];
    hoisted_7_1 := [  ];
    hoisted_6_1 := UnderlyingCategory( cat_1 );
    hoisted_4_1 := deduped_12_1[2];
    deduped_2_1 := ListOfObjectsOfUnderlyingCategory( cat_1 );
    hoisted_5_1 := Concatenation( List( deduped_10_1, function ( i_2 )
              return ListWithIdenticalEntries( hoisted_4_1[i_2], deduped_2_1[i_2] );
          end ) );
    hoisted_1_1 := deduped_11_1[2];
    hoisted_3_1 := Concatenation( List( deduped_10_1, function ( i_2 )
              return ListWithIdenticalEntries( hoisted_1_1[i_2], deduped_2_1[i_2] );
          end ) );
    return CreateCapCategoryMorphismWithAttributes( cat_1, a_1, b_1, MorphismMatrix, List( [ 1 .. deduped_11_1[1] ], function ( i_2 )
              local hoisted_1_2;
              hoisted_1_2 := hoisted_3_1[i_2];
              return List( hoisted_9_1, function ( j_3 )
                      return CreateCapCategoryMorphismWithAttributes( hoisted_6_1, hoisted_1_2, hoisted_5_1[j_3], CoefficientsList, hoisted_7_1, SupportMorphisms, hoisted_8_1 );
                  end );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddIsZeroForMorphisms( cat,
        
########
function ( cat_1, arg2_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, deduped_4_1;
    deduped_4_1 := MorphismMatrix( arg2_1 );
    hoisted_3_1 := [ 1 .. NrSummandsAndMultiplicities( Target( arg2_1 ) )[1] ];
    hoisted_2_1 := List( deduped_4_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_x_3 )
                    return IsEmpty( SupportMorphisms( logic_new_func_x_3 ) );
                end );
        end );
    hoisted_1_1 := List( deduped_4_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_x_3 )
                    return IsEmpty( CoefficientsList( logic_new_func_x_3 ) );
                end );
        end );
    return ForAll( [ 1 .. NrSummandsAndMultiplicities( Source( arg2_1 ) )[1] ], function ( i_2 )
            local hoisted_1_2, hoisted_2_2;
            hoisted_2_2 := hoisted_2_1[i_2];
            hoisted_1_2 := hoisted_1_1[i_2];
            return ForAll( hoisted_3_1, function ( j_3 )
                    return hoisted_1_2[j_3] and hoisted_2_2[j_3];
                end );
        end );
end
########
        
    , 100 );
    
    ##
    AddAdditionForMorphisms( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    local hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, hoisted_9_1, hoisted_10_1, hoisted_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1;
    deduped_15_1 := MorphismMatrix( beta_1 );
    deduped_14_1 := MorphismMatrix( alpha_1 );
    deduped_13_1 := Target( alpha_1 );
    deduped_12_1 := Source( alpha_1 );
    hoisted_11_1 := [ 1 .. NrSummandsAndMultiplicities( deduped_13_1 )[1] ];
    hoisted_10_1 := UnderlyingCategory( cat_1 );
    hoisted_9_1 := List( deduped_15_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, SupportMorphisms );
        end );
    hoisted_8_1 := List( deduped_14_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, SupportMorphisms );
        end );
    hoisted_7_1 := ZeroImmutable( CommutativeRingOfLinearCategory( cat_1 ) );
    hoisted_6_1 := List( deduped_15_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, CoefficientsList );
        end );
    hoisted_5_1 := List( deduped_14_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, CoefficientsList );
        end );
    hoisted_4_1 := List( deduped_14_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, Target );
        end );
    hoisted_3_1 := List( deduped_14_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, Source );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_12_1, deduped_13_1, MorphismMatrix, List( [ 1 .. NrSummandsAndMultiplicities( deduped_12_1 )[1] ], function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, hoisted_4_2, hoisted_5_2, hoisted_6_2;
              hoisted_6_2 := hoisted_9_1[i_2];
              hoisted_5_2 := hoisted_8_1[i_2];
              hoisted_4_2 := hoisted_6_1[i_2];
              hoisted_3_2 := hoisted_5_1[i_2];
              hoisted_2_2 := hoisted_4_1[i_2];
              hoisted_1_2 := hoisted_3_1[i_2];
              return List( hoisted_11_1, function ( j_3 )
                      local deduped_1_3, deduped_2_3;
                      deduped_2_3 := Sum( Concatenation( hoisted_3_2[j_3], hoisted_4_2[j_3] ), hoisted_7_1 );
                      deduped_1_3 := [ 1 .. BooleanToInteger( not IsZero( deduped_2_3 ) ) ];
                      return CreateCapCategoryMorphismWithAttributes( hoisted_10_1, hoisted_1_2[j_3], hoisted_2_2[j_3], CoefficientsList, [ deduped_2_3 ]{deduped_1_3}, SupportMorphisms, Concatenation( hoisted_5_2[j_3], hoisted_6_2[j_3] ){deduped_1_3} );
                  end );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddSumOfMorphisms( cat,
        
########
function ( cat_1, source_1, list_of_morphisms_1, range_1 )
    local hoisted_1_1, deduped_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, deduped_9_1, deduped_10_1, deduped_11_1;
    deduped_11_1 := NrSummandsAndMultiplicities( range_1 );
    deduped_10_1 := NrSummandsAndMultiplicities( source_1 );
    deduped_9_1 := [ 1 .. NumberOfObjectsOfUnderlyingCategory( cat_1 ) ];
    hoisted_8_1 := [ 1 .. deduped_11_1[1] ];
    hoisted_7_1 := UnderlyingCategory( cat_1 );
    hoisted_6_1 := ZeroImmutable( CommutativeRingOfLinearCategory( cat_1 ) );
    hoisted_4_1 := deduped_11_1[2];
    deduped_2_1 := ListOfObjectsOfUnderlyingCategory( cat_1 );
    hoisted_5_1 := Concatenation( List( deduped_9_1, function ( i_2 )
              return ListWithIdenticalEntries( hoisted_4_1[i_2], deduped_2_1[i_2] );
          end ) );
    hoisted_1_1 := deduped_10_1[2];
    hoisted_3_1 := Concatenation( List( deduped_9_1, function ( i_2 )
              return ListWithIdenticalEntries( hoisted_1_1[i_2], deduped_2_1[i_2] );
          end ) );
    return CreateCapCategoryMorphismWithAttributes( cat_1, source_1, range_1, MorphismMatrix, List( [ 1 .. deduped_10_1[1] ], function ( i_2 )
              local hoisted_1_2;
              hoisted_1_2 := hoisted_3_1[i_2];
              return List( hoisted_8_1, function ( j_3 )
                      local deduped_1_3, deduped_2_3;
                      deduped_2_3 := Sum( Concatenation( List( list_of_morphisms_1, function ( m_4 )
                                  return CAP_JIT_INCOMPLETE_LOGIC( CoefficientsList( CAP_JIT_INCOMPLETE_LOGIC( CAP_JIT_INCOMPLETE_LOGIC( MorphismMatrix( m_4 )[i_2] )[j_3] ) ) );
                              end ) ), hoisted_6_1 );
                      deduped_1_3 := [ 1 .. BooleanToInteger( not IsZero( deduped_2_3 ) ) ];
                      return CreateCapCategoryMorphismWithAttributes( hoisted_7_1, hoisted_1_2, hoisted_5_1[j_3], CoefficientsList, [ deduped_2_3 ]{deduped_1_3}, SupportMorphisms, Concatenation( List( list_of_morphisms_1, function ( m_4 )
                                    return CAP_JIT_INCOMPLETE_LOGIC( SupportMorphisms( CAP_JIT_INCOMPLETE_LOGIC( CAP_JIT_INCOMPLETE_LOGIC( MorphismMatrix( m_4 )[i_2] )[j_3] ) ) );
                                end ) ){deduped_1_3} );
                  end );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.SumOfMorphisms :=
        
########
function ( cat_1, source_1, list_of_morphisms_1, range_1 )
    local hoisted_1_1, deduped_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, deduped_9_1, deduped_10_1, deduped_11_1;
    deduped_11_1 := NrSummandsAndMultiplicities( range_1 );
    deduped_10_1 := NrSummandsAndMultiplicities( source_1 );
    deduped_9_1 := [ 1 .. NumberOfObjectsOfUnderlyingCategory( cat_1 ) ];
    hoisted_8_1 := [ 1 .. deduped_11_1[1] ];
    hoisted_7_1 := UnderlyingCategory( cat_1 );
    hoisted_6_1 := ZeroImmutable( CommutativeRingOfLinearCategory( cat_1 ) );
    hoisted_4_1 := deduped_11_1[2];
    deduped_2_1 := ListOfObjectsOfUnderlyingCategory( cat_1 );
    hoisted_5_1 := Concatenation( List( deduped_9_1, function ( i_2 )
              return ListWithIdenticalEntries( hoisted_4_1[i_2], deduped_2_1[i_2] );
          end ) );
    hoisted_1_1 := deduped_10_1[2];
    hoisted_3_1 := Concatenation( List( deduped_9_1, function ( i_2 )
              return ListWithIdenticalEntries( hoisted_1_1[i_2], deduped_2_1[i_2] );
          end ) );
    return CreateCapCategoryMorphismWithAttributes( cat_1, source_1, range_1, MorphismMatrix, List( [ 1 .. deduped_10_1[1] ], function ( i_2 )
              local hoisted_1_2;
              hoisted_1_2 := hoisted_3_1[i_2];
              return List( hoisted_8_1, function ( j_3 )
                      local deduped_1_3, deduped_2_3;
                      deduped_2_3 := Sum( Concatenation( List( list_of_morphisms_1, function ( m_4 )
                                  return List( MorphismMatrix( m_4 ), function ( logic_new_func_list_5 )
                                              return List( logic_new_func_list_5, CoefficientsList );
                                          end )[i_2][j_3];
                              end ) ), hoisted_6_1 );
                      deduped_1_3 := [ 1 .. BooleanToInteger( not IsZero( deduped_2_3 ) ) ];
                      return CreateCapCategoryMorphismWithAttributes( hoisted_7_1, hoisted_1_2, hoisted_5_1[j_3], CoefficientsList, [ deduped_2_3 ]{deduped_1_3}, SupportMorphisms, Concatenation( List( list_of_morphisms_1, function ( m_4 )
                                    return List( MorphismMatrix( m_4 ), function ( logic_new_func_list_5 )
                                                return List( logic_new_func_list_5, SupportMorphisms );
                                            end )[i_2][j_3];
                                end ) ){deduped_1_3} );
                  end );
          end ) );
end
########
        
    ;
    
    ##
    AddAdditiveInverseForMorphisms( cat,
        
########
function ( cat_1, alpha_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, deduped_8_1, deduped_9_1, deduped_10_1;
    deduped_10_1 := MorphismMatrix( alpha_1 );
    deduped_9_1 := Target( alpha_1 );
    deduped_8_1 := Source( alpha_1 );
    hoisted_7_1 := [ 1 .. NrSummandsAndMultiplicities( deduped_9_1 )[1] ];
    hoisted_6_1 := UnderlyingCategory( cat_1 );
    hoisted_5_1 := List( deduped_10_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, SupportMorphisms );
        end );
    hoisted_4_1 := MinusOne( CommutativeRingOfLinearCategory( cat_1 ) );
    hoisted_3_1 := List( deduped_10_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_x_3 )
                    return Sum( CoefficientsList( logic_new_func_x_3 ) );
                end );
        end );
    hoisted_2_1 := List( deduped_10_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, Target );
        end );
    hoisted_1_1 := List( deduped_10_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, Source );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_8_1, deduped_9_1, MorphismMatrix, List( [ 1 .. NrSummandsAndMultiplicities( deduped_8_1 )[1] ], function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, hoisted_4_2;
              hoisted_4_2 := hoisted_5_1[i_2];
              hoisted_3_2 := hoisted_3_1[i_2];
              hoisted_2_2 := hoisted_2_1[i_2];
              hoisted_1_2 := hoisted_1_1[i_2];
              return List( hoisted_7_1, function ( j_3 )
                      local deduped_1_3, deduped_2_3;
                      deduped_2_3 := hoisted_3_2[j_3] * hoisted_4_1;
                      deduped_1_3 := [ 1 .. BooleanToInteger( not IsZero( deduped_2_3 ) ) ];
                      return CreateCapCategoryMorphismWithAttributes( hoisted_6_1, hoisted_1_2[j_3], hoisted_2_2[j_3], CoefficientsList, [ deduped_2_3 ]{deduped_1_3}, SupportMorphisms, hoisted_4_2[j_3]{deduped_1_3} );
                  end );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddSubtractionForMorphisms( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, deduped_4_1, deduped_5_1, deduped_6_1, hoisted_7_1, hoisted_8_1, hoisted_9_1, hoisted_10_1, hoisted_11_1, hoisted_12_1, hoisted_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1;
    deduped_19_1 := CommutativeRingOfLinearCategory( cat_1 );
    deduped_18_1 := MorphismMatrix( beta_1 );
    deduped_17_1 := MorphismMatrix( alpha_1 );
    deduped_16_1 := Target( alpha_1 );
    deduped_15_1 := Source( alpha_1 );
    deduped_14_1 := [ 1 .. NrSummandsAndMultiplicities( Source( beta_1 ) )[1] ];
    hoisted_13_1 := [ 1 .. NrSummandsAndMultiplicities( deduped_16_1 )[1] ];
    hoisted_12_1 := UnderlyingCategory( cat_1 );
    hoisted_10_1 := List( deduped_18_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, SupportMorphisms );
        end );
    deduped_6_1 := [ 1 .. NrSummandsAndMultiplicities( Target( beta_1 ) )[1] ];
    deduped_5_1 := MinusOne( deduped_19_1 );
    deduped_4_1 := List( deduped_18_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_x_3 )
                    return Sum( CoefficientsList( logic_new_func_x_3 ) );
                end );
        end );
    hoisted_11_1 := List( deduped_14_1, function ( i_2 )
            local hoisted_1_2, hoisted_2_2;
            hoisted_2_2 := deduped_4_1[i_2];
            hoisted_1_2 := hoisted_10_1[i_2];
            return List( deduped_6_1, function ( j_3 )
                    return hoisted_1_2[j_3]{[ 1 .. BooleanToInteger( not IsZero( hoisted_2_2[j_3] * deduped_5_1 ) ) ]};
                end );
        end );
    hoisted_9_1 := List( deduped_17_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, SupportMorphisms );
        end );
    hoisted_8_1 := ZeroImmutable( deduped_19_1 );
    hoisted_7_1 := List( deduped_14_1, function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := deduped_4_1[i_2];
            return List( deduped_6_1, function ( j_3 )
                    local deduped_1_3;
                    deduped_1_3 := hoisted_1_2[j_3] * deduped_5_1;
                    return [ deduped_1_3 ]{[ 1 .. BooleanToInteger( not IsZero( deduped_1_3 ) ) ]};
                end );
        end );
    hoisted_3_1 := List( deduped_17_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, CoefficientsList );
        end );
    hoisted_2_1 := List( deduped_17_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, Target );
        end );
    hoisted_1_1 := List( deduped_17_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, Source );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_15_1, deduped_16_1, MorphismMatrix, List( [ 1 .. NrSummandsAndMultiplicities( deduped_15_1 )[1] ], function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, hoisted_4_2, hoisted_5_2, hoisted_6_2;
              hoisted_6_2 := hoisted_11_1[i_2];
              hoisted_5_2 := hoisted_9_1[i_2];
              hoisted_4_2 := hoisted_7_1[i_2];
              hoisted_3_2 := hoisted_3_1[i_2];
              hoisted_2_2 := hoisted_2_1[i_2];
              hoisted_1_2 := hoisted_1_1[i_2];
              return List( hoisted_13_1, function ( j_3 )
                      local deduped_1_3, deduped_2_3;
                      deduped_2_3 := Sum( Concatenation( hoisted_3_2[j_3], hoisted_4_2[j_3] ), hoisted_8_1 );
                      deduped_1_3 := [ 1 .. BooleanToInteger( not IsZero( deduped_2_3 ) ) ];
                      return CreateCapCategoryMorphismWithAttributes( hoisted_12_1, hoisted_1_2[j_3], hoisted_2_2[j_3], CoefficientsList, [ deduped_2_3 ]{deduped_1_3}, SupportMorphisms, Concatenation( hoisted_5_2[j_3], hoisted_6_2[j_3] ){deduped_1_3} );
                  end );
          end ) );
end
########
        
    , 201 : IsPrecompiledDerivation := true );
    
    ##
    AddZeroObject( cat,
        
########
function ( cat_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, NrSummandsAndMultiplicities, NTuple( 2, 0, ListWithIdenticalEntries( NumberOfObjectsOfUnderlyingCategory( cat_1 ), 0 ) ) );
end
########
        
    , 100 );
    
    ##
    AddDirectSum( cat,
        
########
function ( cat_1, objects_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, NrSummandsAndMultiplicities, Sum( List( objects_1, NrSummandsAndMultiplicities ) ) );
end
########
        
    , 100 );
    
    ##
    AddUniversalMorphismIntoDirectSumWithGivenDirectSum( cat,
        
########
function ( cat_1, objects_1, T_1, tau_1, P_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, T_1, P_1, MorphismMatrix, UnionOfColumnsListList( NrSummandsAndMultiplicities( T_1 )[1], List( tau_1, MorphismMatrix ) ) );
end
########
        
    , 100 );
    
    ##
    AddUniversalMorphismFromDirectSumWithGivenDirectSum( cat,
        
########
function ( cat_1, objects_1, T_1, tau_1, P_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, P_1, T_1, MorphismMatrix, UnionOfRowsListList( NrSummandsAndMultiplicities( T_1 )[1], List( tau_1, MorphismMatrix ) ) );
end
########
        
    , 100 );
    
    ##
    AddComponentOfMorphismIntoDirectSum( cat,
        
########
function ( cat_1, alpha_1, S_1, i_1 )
    local hoisted_1_1, deduped_2_1, deduped_3_1;
    deduped_3_1 := List( S_1, function ( s_2 )
            return NrSummandsAndMultiplicities( s_2 )[1];
        end );
    deduped_2_1 := Sum( deduped_3_1{[ 1 .. i_1 - 1 ]} );
    hoisted_1_1 := [ deduped_2_1 + 1 .. deduped_2_1 + deduped_3_1[i_1] ];
    return CreateCapCategoryMorphismWithAttributes( cat_1, Source( alpha_1 ), S_1[i_1], MorphismMatrix, List( MorphismMatrix( alpha_1 ), function ( row_2 )
              return row_2{hoisted_1_1};
          end ) );
end
########
        
    , 100 );
    
    ##
    AddComponentOfMorphismFromDirectSum( cat,
        
########
function ( cat_1, alpha_1, S_1, i_1 )
    local deduped_1_1, deduped_2_1;
    deduped_2_1 := List( S_1, function ( s_2 )
            return NrSummandsAndMultiplicities( s_2 )[1];
        end );
    deduped_1_1 := Sum( deduped_2_1{[ 1 .. i_1 - 1 ]} );
    return CreateCapCategoryMorphismWithAttributes( cat_1, S_1[i_1], Target( alpha_1 ), MorphismMatrix, MorphismMatrix( alpha_1 ){[ deduped_1_1 + 1 .. deduped_1_1 + deduped_2_1[i_1] ]} );
end
########
        
    , 100 );
    
    ##
    AddMultiplyWithElementOfCommutativeRingForMorphisms( cat,
        
########
function ( cat_1, r_1, alpha_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, deduped_7_1, deduped_8_1, deduped_9_1;
    deduped_9_1 := MorphismMatrix( alpha_1 );
    deduped_8_1 := Target( alpha_1 );
    deduped_7_1 := Source( alpha_1 );
    hoisted_6_1 := [ 1 .. NrSummandsAndMultiplicities( deduped_8_1 )[1] ];
    hoisted_5_1 := UnderlyingCategory( cat_1 );
    hoisted_4_1 := List( deduped_9_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, SupportMorphisms );
        end );
    hoisted_3_1 := List( deduped_9_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_x_3 )
                    return Sum( CoefficientsList( logic_new_func_x_3 ) );
                end );
        end );
    hoisted_2_1 := List( deduped_9_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, Target );
        end );
    hoisted_1_1 := List( deduped_9_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, Source );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_7_1, deduped_8_1, MorphismMatrix, List( [ 1 .. NrSummandsAndMultiplicities( deduped_7_1 )[1] ], function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, hoisted_4_2;
              hoisted_4_2 := hoisted_4_1[i_2];
              hoisted_3_2 := hoisted_3_1[i_2];
              hoisted_2_2 := hoisted_2_1[i_2];
              hoisted_1_2 := hoisted_1_1[i_2];
              return List( hoisted_6_1, function ( j_3 )
                      local deduped_1_3, deduped_2_3;
                      deduped_2_3 := hoisted_3_2[j_3] * r_1;
                      deduped_1_3 := [ 1 .. BooleanToInteger( not IsZero( deduped_2_3 ) ) ];
                      return CreateCapCategoryMorphismWithAttributes( hoisted_5_1, hoisted_1_2[j_3], hoisted_2_2[j_3], CoefficientsList, [ deduped_2_3 ]{deduped_1_3}, SupportMorphisms, hoisted_4_2[j_3]{deduped_1_3} );
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

BindGlobal( "AdditiveClosureOfObjectFiniteCategory_LinearClosure_over_Field_DiscreteCategory_precompiled", function ( homalg_ring )
  local category_constructor, cat;
    
    category_constructor :=
        
        
        function ( homalg_ring )
    return AdditiveClosureOfObjectFiniteCategory( LinearClosure( homalg_ring, FiniteSkeletalDiscreteCategory( 3 : FinalizeCategory := true ) : FinalizeCategory := true ) );
end;
        
        
    
    cat := category_constructor( homalg_ring : FinalizeCategory := false, no_precompiled_code := true );
    
    ADD_FUNCTIONS_FOR_AdditiveClosureOfObjectFiniteCategory_LinearClosure_over_Field_DiscreteCategory_precompiled( cat );
    
    Finalize( cat );
    
    return cat;
    
end );
