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
    local source_morphism_matrix_alpha, range_morphism_matrix_beta, coefficients_morphism_matrix_alpha, coefficients_morphism_matrix_beta, support_morphisms_morphism_matrix_alpha, support_morphisms_morphism_matrix_beta, hoisted_9_1, list_nr_summands_target_alpha, deduped_11_1, list_underlying_objects, deduped_13_1, deduped_14_1;
    deduped_14_1 := MorphismMatrix( beta_1 );
    deduped_13_1 := MorphismMatrix( alpha_1 );
    list_underlying_objects := Target( alpha_1 );
    deduped_11_1 := Source( alpha_1 );
    list_nr_summands_target_alpha := [ 1 .. NrSummandsAndMultiplicities( list_underlying_objects )[1] ];
    hoisted_9_1 := UnderlyingCategory( cat_1 );
    support_morphisms_morphism_matrix_beta := List( deduped_14_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, SupportMorphisms );
        end );
    support_morphisms_morphism_matrix_alpha := List( deduped_13_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, SupportMorphisms );
        end );
    coefficients_morphism_matrix_beta := List( deduped_14_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, CoefficientsList );
        end );
    coefficients_morphism_matrix_alpha := List( deduped_13_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, CoefficientsList );
        end );
    range_morphism_matrix_beta := List( deduped_13_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, Range );
        end );
    source_morphism_matrix_alpha := List( deduped_13_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, Source );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_11_1, list_underlying_objects, MorphismMatrix, List( [ 1 .. NrSummandsAndMultiplicities( deduped_11_1 )[1] ], function ( row_i )
              local source_morphism_matrix_alpha_row_i, coefficients_morphisms_morphism_matrix_alpha_row_i, support_morphisms_morphism_matrix_alpha_row_i, ith_underlying_object_source_alpha, hoisted_5_2, hoisted_6_2;
              hoisted_6_2 := support_morphisms_morphism_matrix_beta[row_i];
              hoisted_5_2 := support_morphisms_morphism_matrix_alpha[row_i];
              ith_underlying_object_source_alpha := coefficients_morphism_matrix_beta[row_i];
              support_morphisms_morphism_matrix_alpha_row_i := coefficients_morphism_matrix_alpha[row_i];
              coefficients_morphisms_morphism_matrix_alpha_row_i := range_morphism_matrix_beta[row_i];
              source_morphism_matrix_alpha_row_i := source_morphism_matrix_alpha[row_i];
              return List( list_nr_summands_target_alpha, function ( col_j )
                      return CreateCapCategoryMorphismWithAttributes( hoisted_9_1, source_morphism_matrix_alpha_row_i[col_j], coefficients_morphisms_morphism_matrix_alpha_row_i[col_j], CoefficientsList, Concatenation( support_morphisms_morphism_matrix_alpha_row_i[col_j], ith_underlying_object_source_alpha[col_j] ), SupportMorphisms, Concatenation( hoisted_5_2[col_j], hoisted_6_2[col_j] ) );
                  end );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddPreCompose( cat,
        
########
function ( AC_objfin, alpha, beta )
    local source_morphism_matrix_alpha, range_morphism_matrix_beta, coefficients_morphism_matrix_alpha, coefficients_morphism_matrix_beta, support_morphisms_morphism_matrix_alpha, support_morphisms_morphism_matrix_beta, LinearClosure, list_nr_summands_target_alpha, multiplicities_source_alpha, list_underlying_objects, underlying_object_list_source_alpha, multiplicities_target_beta, underlying_object_list_target_beta, empty_list2, empty_list, nr_summands_target_beta, nr_summands_and_multiplicities_source_alpha, nr_summands_and_multiplicities_target_beta, nr_underlying_objects, source_alpha, target_beta, morphism_matrix_alpha, morphism_matrix_beta;
    morphism_matrix_beta := MorphismMatrix( beta );
    morphism_matrix_alpha := MorphismMatrix( alpha );
    target_beta := Target( beta );
    source_alpha := Source( alpha );
    nr_underlying_objects := [ 1 .. NumberOfObjectsOfUnderlyingCategory( AC_objfin ) ];
    nr_summands_and_multiplicities_target_beta := NrSummandsAndMultiplicities( target_beta );
    nr_summands_and_multiplicities_source_alpha := NrSummandsAndMultiplicities( source_alpha );
    nr_summands_target_beta := [ 1 .. nr_summands_and_multiplicities_target_beta[1] ];
    empty_list := [  ];
    empty_list2 := CapJitTypedExpression( [  ], function (  )
            return rec(
                filter := IsList,
                element_type := rec(
                    filter := DummyHomalgFieldElementFilter ) );
        end );
    multiplicities_target_beta := nr_summands_and_multiplicities_target_beta[2];
    list_underlying_objects := ListOfObjectsOfUnderlyingCategory( AC_objfin );
    underlying_object_list_target_beta := Concatenation( List( nr_underlying_objects, function ( row_i )
              return ListWithIdenticalEntries( multiplicities_target_beta[row_i], list_underlying_objects[row_i] );
          end ) );
    multiplicities_source_alpha := nr_summands_and_multiplicities_source_alpha[2];
    underlying_object_list_source_alpha := Concatenation( List( nr_underlying_objects, function ( row_i )
              return ListWithIdenticalEntries( multiplicities_source_alpha[row_i], list_underlying_objects[row_i] );
          end ) );
    list_nr_summands_target_alpha := [ 1 .. NrSummandsAndMultiplicities( Target( alpha ) )[1] ];
    LinearClosure := UnderlyingCategory( AC_objfin );
    support_morphisms_morphism_matrix_beta := List( morphism_matrix_beta, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, SupportMorphisms );
        end );
    support_morphisms_morphism_matrix_alpha := List( morphism_matrix_alpha, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, SupportMorphisms );
        end );
    coefficients_morphism_matrix_beta := List( morphism_matrix_beta, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, CoefficientsList );
        end );
    coefficients_morphism_matrix_alpha := List( morphism_matrix_alpha, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, CoefficientsList );
        end );
    range_morphism_matrix_beta := List( morphism_matrix_beta, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, Range );
        end );
    source_morphism_matrix_alpha := List( morphism_matrix_alpha, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, Source );
        end );
    return CreateCapCategoryMorphismWithAttributes( AC_objfin,
                source_alpha,
                target_beta,
                MorphismMatrix, List( [ 1 .. nr_summands_and_multiplicities_source_alpha[1] ], function ( row_i )   # Rows
                                      local source_morphism_matrix_alpha_row_i, coefficients_morphisms_morphism_matrix_alpha_row_i, support_morphisms_morphism_matrix_alpha_row_i, ith_underlying_object_source_alpha;
                                      ith_underlying_object_source_alpha := underlying_object_list_source_alpha[row_i];
                                      support_morphisms_morphism_matrix_alpha_row_i := support_morphisms_morphism_matrix_alpha[row_i];
                                      coefficients_morphisms_morphism_matrix_alpha_row_i := coefficients_morphism_matrix_alpha[row_i];
                                      source_morphism_matrix_alpha_row_i := source_morphism_matrix_alpha[row_i];
                                      return List( nr_summands_target_beta, function ( col_j )   # Columns
                                          return Iterated( List( list_nr_summands_target_alpha,   # SumOfMorphisms
                                                                 function ( k_4 ) return CreateCapCategoryMorphismWithAttributes(    #PreCompose
                                                                                                LinearClosure,
                                                                                                source_morphism_matrix_alpha_row_i[k_4],
                                                                                                range_morphism_matrix_beta[k_4][col_j],
                                                                                                CoefficientsList,
                                                                                                ListX( coefficients_morphisms_morphism_matrix_alpha_row_i[k_4],
                                                                                                       coefficients_morphism_matrix_beta[k_4][col_j],
                                                                                                       function ( a_5, b_5 ) return a_5 * b_5; end ),
                                                                                                SupportMorphisms,
                                                                                                ListX( support_morphisms_morphism_matrix_alpha_row_i[k_4],
                                                                                                       support_morphisms_morphism_matrix_beta[k_4][col_j],
                                                                                                       function ( alpha_5, beta_5 ) return alpha_5; end ) );
                                                                 end
                                                               ),
                                                           function ( alpha_4, beta_4 )   # AdditionForMorphisms
                                                             return CreateCapCategoryMorphismWithAttributes(
                                                                           LinearClosure,
                                                                           Source( alpha_4 ),
                                                                           Range( alpha_4 ),
                                                                           CoefficientsList, Concatenation( CoefficientsList( alpha_4 ), CoefficientsList( beta_4 ) ),
                                                                           SupportMorphisms, Concatenation( SupportMorphisms( alpha_4 ), SupportMorphisms( beta_4 ) ) );
                                                           end,
                                                           CreateCapCategoryMorphismWithAttributes( LinearClosure, ith_underlying_object_source_alpha, underlying_object_list_target_beta[col_j], CoefficientsList, empty_list2, SupportMorphisms, empty_list ) ); # Initial value for iterated.
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
