# SPDX-License-Identifier: GPL-2.0-or-later
# AdditiveClosuresForCAP: Additive closures for pre-abelian categories
#
# Implementations
#
BindGlobal( "ADD_FUNCTIONS_FOR_AdditiveClosureOfObjectFiniteCategory_of_LinearClosure_over_Field_of__DiscreteCategory_precompiled", function ( cat )
    
    ##
    AddAdditionForMorphisms( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    local hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, hoisted_9_1, hoisted_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1;
    deduped_14_1 := MorphismMatrix( beta_1 );
    deduped_13_1 := MorphismMatrix( alpha_1 );
    deduped_12_1 := Target( alpha_1 );
    deduped_11_1 := Source( alpha_1 );
    hoisted_10_1 := [ 1 .. NrSummandsAndMultiplicities( deduped_12_1 )[1] ];
    hoisted_9_1 := UnderlyingCategory( cat_1 );
    hoisted_8_1 := List( deduped_14_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, SupportMorphisms );
        end );
    hoisted_7_1 := List( deduped_13_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, SupportMorphisms );
        end );
    hoisted_6_1 := List( deduped_14_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, CoefficientsList );
        end );
    hoisted_5_1 := List( deduped_13_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, CoefficientsList );
        end );
    hoisted_4_1 := List( deduped_13_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, Range );
        end );
    hoisted_3_1 := List( deduped_13_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, Source );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_11_1, deduped_12_1, MorphismMatrix, List( [ 1 .. NrSummandsAndMultiplicities( deduped_11_1 )[1] ], function ( i_2 )
              local hoisted_1_2, hoisted_2_2, hoisted_3_2, hoisted_4_2, hoisted_5_2, hoisted_6_2;
              hoisted_6_2 := hoisted_8_1[i_2];
              hoisted_5_2 := hoisted_7_1[i_2];
              hoisted_4_2 := hoisted_6_1[i_2];
              hoisted_3_2 := hoisted_5_1[i_2];
              hoisted_2_2 := hoisted_4_1[i_2];
              hoisted_1_2 := hoisted_3_1[i_2];
              return List( hoisted_10_1, function ( j_3 )
                      return CreateCapCategoryMorphismWithAttributes( hoisted_9_1, hoisted_1_2[j_3], hoisted_2_2[j_3], CoefficientsList, Concatenation( hoisted_3_2[j_3], hoisted_4_2[j_3] ), SupportMorphisms, Concatenation( hoisted_5_2[j_3], hoisted_6_2[j_3] ) );
                  end );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddPreCompose( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    local hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, deduped_9_1, hoisted_10_1, hoisted_11_1, deduped_12_1, hoisted_13_1, hoisted_14_1, hoisted_15_1, hoisted_16_1, hoisted_17_1, hoisted_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1, deduped_25_1;
    deduped_25_1 := MorphismMatrix( beta_1 );
    deduped_24_1 := MorphismMatrix( alpha_1 );
    deduped_23_1 := Target( beta_1 );
    deduped_22_1 := Source( alpha_1 );
    deduped_21_1 := [ 1 .. NumberOfObjectsOfUnderlyingCategory( cat_1 ) ];
    deduped_20_1 := NrSummandsAndMultiplicities( deduped_23_1 );
    deduped_19_1 := NrSummandsAndMultiplicities( deduped_22_1 );
    hoisted_18_1 := [ 1 .. deduped_20_1[1] ];
    hoisted_17_1 := [  ];
    hoisted_16_1 := CapJitTypedExpression( [  ], function (  )
            return rec(
                filter := IsList,
                element_type := rec(
                    filter := DummyHomalgFieldElementFilter ) );
        end );
    hoisted_14_1 := deduped_20_1[2];
    deduped_12_1 := ListOfObjectsOfUnderlyingCategory( cat_1 );
    hoisted_15_1 := Concatenation( List( deduped_21_1, function ( i_2 )
              return ListWithIdenticalEntries( hoisted_14_1[i_2], deduped_12_1[i_2] );
          end ) );
    hoisted_11_1 := deduped_19_1[2];
    hoisted_13_1 := Concatenation( List( deduped_21_1, function ( i_2 )
              return ListWithIdenticalEntries( hoisted_11_1[i_2], deduped_12_1[i_2] );
          end ) );
    hoisted_10_1 := [ 1 .. NrSummandsAndMultiplicities( Target( alpha_1 ) )[1] ];
    deduped_9_1 := UnderlyingCategory( cat_1 );
    hoisted_8_1 := List( deduped_25_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, SupportMorphisms );
        end );
    hoisted_7_1 := List( deduped_24_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, SupportMorphisms );
        end );
    hoisted_6_1 := List( deduped_25_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, CoefficientsList );
        end );
    hoisted_5_1 := List( deduped_24_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, CoefficientsList );
        end );
    hoisted_4_1 := List( deduped_25_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, Range );
        end );
    hoisted_3_1 := List( deduped_24_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, Source );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1,
                deduped_22_1,
                deduped_23_1,
                MorphismMatrix, List( [ 1 .. deduped_19_1[1] ], function ( i_2 )   # Rows
                                      local hoisted_1_2, hoisted_2_2, hoisted_3_2, hoisted_4_2;
                                      hoisted_4_2 := hoisted_13_1[i_2];
                                      hoisted_3_2 := hoisted_7_1[i_2];
                                      hoisted_2_2 := hoisted_5_1[i_2];
                                      hoisted_1_2 := hoisted_3_1[i_2];
                                      return List( hoisted_18_1, function ( j_3 )  # Columns
                                          return Iterated( List( hoisted_10_1,     # PreCompose
                                                                 function ( k_4 ) return CreateCapCategoryMorphismWithAttributes(
                                                                                                deduped_9_1,
                                                                                                hoisted_1_2[k_4],
                                                                                                hoisted_4_1[k_4][j_3],
                                                                                                CoefficientsList,
                                                                                                ListX( hoisted_2_2[k_4],
                                                                                                       hoisted_6_1[k_4][j_3],
                                                                                                       function ( a_5, b_5 ) return a_5 * b_5; end ),
                                                                                                SupportMorphisms,
                                                                                                ListX( hoisted_3_2[k_4],
                                                                                                       hoisted_8_1[k_4][j_3],
                                                                                                       function ( alpha_5, beta_5 ) return alpha_5; end ) );
                                                                 end
                                                               ),
                                                           function ( alpha_4, beta_4 )   # AdditionForMorphisms
                                                             return CreateCapCategoryMorphismWithAttributes(
                                                                           deduped_9_1,
                                                                           Source( alpha_4 ),
                                                                           Range( alpha_4 ),
                                                                           CoefficientsList, Concatenation( CoefficientsList( alpha_4 ), CoefficientsList( beta_4 ) ),
                                                                           SupportMorphisms, Concatenation( SupportMorphisms( alpha_4 ), SupportMorphisms( beta_4 ) ) );
                                                           end,
                                                           CreateCapCategoryMorphismWithAttributes( deduped_9_1, hoisted_4_2, hoisted_15_1[j_3], CoefficientsList, hoisted_16_1, SupportMorphisms, hoisted_17_1 ) ); # Initial value for iterated.
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

BindGlobal( "AdditiveClosureOfObjectFiniteCategory_of_LinearClosure_over_Field_of__DiscreteCategory_precompiled", function ( homalg_ring )
  local category_constructor, cat;
    
    category_constructor :=
        
        
        function ( homalg_ring )
    return AdditiveClosureOfObjectFiniteCategory( LinearClosure( homalg_ring, FiniteSkeletalDiscreteCategory( [ 1 .. 3 ] : FinalizeCategory := true ) : FinalizeCategory := true ) );
end;
        
        
    
    cat := category_constructor( homalg_ring : FinalizeCategory := false, no_precompiled_code := true );
    
    ADD_FUNCTIONS_FOR_AdditiveClosureOfObjectFiniteCategory_of_LinearClosure_over_Field_of__DiscreteCategory_precompiled( cat );
    
    Finalize( cat );
    
    return cat;
    
end );
