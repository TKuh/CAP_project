# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Implementations
#
BindGlobal( "ADD_FUNCTIONS_FOR_CategoryOfKroneckerComonoids_precompiled", function ( cat )
    
    ##
    AddIsEqualForObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    return NumberElements( arg2_1 ) = NumberElements( arg3_1 );
end
########
        
    , 100 );
    
    ##
    AddIsEqualForMorphisms( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    return NrBlockColumnsAndListOfBlockColumns( arg2_1 ) = NrBlockColumnsAndListOfBlockColumns( arg3_1 );
end
########
        
    , 100 );
    
    ##
    AddIsWellDefinedForObjects( cat,
        
########
function ( cat_1, arg2_1 )
    return 0 <= NumberElements( arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddIsWellDefinedForMorphisms( cat,
        
########
function ( cat_1, alpha_1 )
    local deduped_2_1, deduped_3_1, deduped_4_1, deduped_5_1, deduped_6_1;
    deduped_6_1 := NrBlockColumnsAndListOfBlockColumns( alpha_1 );
    deduped_5_1 := deduped_6_1[2];
    deduped_4_1 := deduped_6_1[1];
    deduped_3_1 := [ 1 .. deduped_4_1 ];
    deduped_2_1 := NumberElements( Source( alpha_1 ) );
    if not deduped_4_1 = Length( deduped_5_1 ) then
        return fail;
    elif not ForAll( deduped_3_1, function ( i_2 )
                 local deduped_1_2;
                 deduped_1_2 := deduped_5_1[i_2];
                 return 1 <= deduped_1_2[1] and 1 <= deduped_1_2[2];
             end ) then
        return false;
    elif not ForAll( deduped_3_1, function ( i_2 )
                 local deduped_1_2;
                 deduped_1_2 := deduped_5_1[i_2];
                 return deduped_1_2[1] <= deduped_1_2[2];
             end ) then
        return false;
    elif not ForAll( deduped_3_1, function ( i_2 )
                 local deduped_1_2;
                 deduped_1_2 := deduped_5_1[i_2];
                 return deduped_1_2[1] <= deduped_2_1 and deduped_1_2[2] <= deduped_2_1;
             end ) then
        return false;
    elif not NumberElements( Target( alpha_1 ) ) = Sum( List( deduped_3_1, function ( i_2 )
                     local deduped_1_2;
                     deduped_1_2 := deduped_5_1[i_2];
                     return deduped_1_2[2] - deduped_1_2[1] + 1;
                 end ) ) then
        return false;
    else
        return true;
    fi;
    return;
end
########
        
    , 100 );
    
    ##
    AddObjectConstructor( cat,
        
########
function ( cat_1, arg2_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, NumberElements, arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddMorphismConstructor( cat,
        
########
function ( cat_1, arg2_1, arg3_1, arg4_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, arg2_1, arg4_1, NrBlockColumnsAndListOfBlockColumns, arg3_1 );
end
########
        
    , 100 );
    
    ##
    AddObjectDatum( cat,
        
########
function ( cat_1, arg2_1 )
    return NumberElements( arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddMorphismDatum( cat,
        
########
function ( cat_1, arg2_1 )
    return NrBlockColumnsAndListOfBlockColumns( arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddIdentityMorphism( cat,
        
########
function ( cat_1, a_1 )
    local deduped_1_1, deduped_2_1;
    deduped_2_1 := NumberElements( a_1 );
    deduped_1_1 := BigInt( 1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, a_1, a_1, NrBlockColumnsAndListOfBlockColumns, [ NTuple( 2, deduped_1_1, [ NTuple( 2, deduped_1_1, deduped_2_1 ) ] ), NTuple( 2, BigInt( 0 ), CapJitTypedExpression( [  ], function (  )
                      return rec(
                          filter := IsList,
                          element_type := rec(
                              filter := IsNTuple,
                              element_types := [ rec(
                                      filter := IsInt ), rec(
                                      filter := IsInt ) ] ) );
                  end ) ) ][1 + BooleanToInteger( deduped_2_1 = 0 )] );
end
########
        
    , 100 );
    
    ##
    AddTerminalObject( cat,
        
########
function ( cat_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, NumberElements, BigInt( 0 ) );
end
########
        
    , 100 );
    
    ##
    AddIsTerminal( cat,
        
########
function ( cat_1, arg2_1 )
    return NumberElements( arg2_1 ) = BigInt( 0 );
end
########
        
    , 100 );
    
    ##
    AddUniversalMorphismIntoTerminalObjectWithGivenTerminalObject( cat,
        
########
function ( cat_1, T_1, P_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, T_1, P_1, NrBlockColumnsAndListOfBlockColumns, NTuple( 2, BigInt( 0 ), CapJitTypedExpression( [  ], function (  )
                return rec(
                    filter := IsList,
                    element_type := rec(
                        filter := IsNTuple,
                        element_types := [ rec(
                                filter := IsInt ), rec(
                                filter := IsInt ) ] ) );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    AddDirectProduct( cat,
        
########
function ( cat_1, objects_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, NumberElements, Sum( List( [ 1 .. Length( objects_1 ) ], function ( i_2 )
                return CAP_JIT_INCOMPLETE_LOGIC( NumberElements( CAP_JIT_INCOMPLETE_LOGIC( objects_1[i_2] ) ) );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.DirectProduct :=
        
########
function ( cat_1, objects_1 )
    local hoisted_1_1;
    hoisted_1_1 := List( objects_1, NumberElements );
    return CreateCapCategoryObjectWithAttributes( cat_1, NumberElements, Sum( List( [ 1 .. Length( objects_1 ) ], function ( i_2 )
                return hoisted_1_1[i_2];
            end ) ) );
end
########
        
    ;
    
    ##
    AddProjectionInFactorOfDirectProductWithGivenDirectProduct( cat,
        
########
function ( cat_1, objects_1, k_1, P_1 )
    local deduped_1_1, deduped_2_1, deduped_3_1;
    deduped_3_1 := List( objects_1, NumberElements );
    deduped_2_1 := deduped_3_1[k_1];
    deduped_1_1 := Sum( deduped_3_1{[ 1 .. k_1 - 1 ]} );
    return CreateCapCategoryMorphismWithAttributes( cat_1, P_1, objects_1[k_1], NrBlockColumnsAndListOfBlockColumns, [ NTuple( 2, BigInt( 1 ), [ NTuple( 2, deduped_1_1 + 1, deduped_1_1 + deduped_2_1 ) ] ), NTuple( 2, BigInt( 0 ), CapJitTypedExpression( [  ], function (  )
                      return rec(
                          filter := IsList,
                          element_type := rec(
                              filter := IsNTuple,
                              element_types := [ rec(
                                      filter := IsInt ), rec(
                                      filter := IsInt ) ] ) );
                  end ) ) ][1 + BooleanToInteger( deduped_2_1 = 0 )] );
end
########
        
    , 100 );
    
    ##
    AddUniversalMorphismIntoDirectProductWithGivenDirectProduct( cat,
        
########
function ( cat_1, objects_1, T_1, tau_1, P_1 )
    local deduped_1_1, deduped_2_1;
    deduped_2_1 := [ 1 .. Length( tau_1 ) ];
    deduped_1_1 := List( tau_1, NrBlockColumnsAndListOfBlockColumns );
    return CreateCapCategoryMorphismWithAttributes( cat_1, T_1, P_1, NrBlockColumnsAndListOfBlockColumns, NTuple( 2, Sum( List( deduped_2_1, function ( i_2 )
                  return deduped_1_1[i_2][1];
              end ) ), Concatenation( List( deduped_2_1, function ( i_2 )
                  return deduped_1_1[i_2][2];
              end ) ) ) );
end
########
        
    , 100 );
    
    ##
    AddDirectProductFunctorialWithGivenDirectProducts( cat,
        
########
function ( cat_1, P_1, objects_1, L_1, objectsp_1, Pp_1 )
    local deduped_1_1, hoisted_2_1, deduped_3_1;
    deduped_3_1 := [ 1 .. Length( L_1 ) ];
    hoisted_2_1 := List( objects_1, NumberElements );
    deduped_1_1 := List( L_1, NrBlockColumnsAndListOfBlockColumns );
    return CreateCapCategoryMorphismWithAttributes( cat_1, P_1, Pp_1, NrBlockColumnsAndListOfBlockColumns, NTuple( 2, Sum( List( deduped_3_1, function ( i_2 )
                  return deduped_1_1[i_2][1];
              end ) ), Concatenation( List( deduped_3_1, function ( i_2 )
                  local deduped_1_2;
                  deduped_1_2 := Sum( List( [ 1 .. i_2 - 1 ], function ( j_3 )
                            return hoisted_2_1[j_3];
                        end ) );
                  return List( deduped_1_1[i_2][2], function ( col_3 )
                          return NTuple( 2, col_3[1] + deduped_1_2, col_3[2] + deduped_1_2 );
                      end );
              end ) ) ) );
end
########
        
    , 100 );
    
    ##
    AddTensorUnit( cat,
        
########
function ( cat_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, NumberElements, BigInt( 1 ) );
end
########
        
    , 100 );
    
    ##
    AddLeftUnitorWithGivenTensorProduct( cat,
        
########
function ( cat_1, a_1, s_1 )
    local deduped_1_1, deduped_2_1;
    deduped_2_1 := NumberElements( a_1 );
    deduped_1_1 := BigInt( 1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, a_1, a_1, NrBlockColumnsAndListOfBlockColumns, [ NTuple( 2, deduped_1_1, [ NTuple( 2, deduped_1_1, deduped_2_1 ) ] ), NTuple( 2, BigInt( 0 ), CapJitTypedExpression( [  ], function (  )
                      return rec(
                          filter := IsList,
                          element_type := rec(
                              filter := IsNTuple,
                              element_types := [ rec(
                                      filter := IsInt ), rec(
                                      filter := IsInt ) ] ) );
                  end ) ) ][1 + BooleanToInteger( deduped_2_1 = 0 )] );
end
########
        
    , 100 );
    
    ##
    AddRightUnitorWithGivenTensorProduct( cat,
        
########
function ( cat_1, a_1, s_1 )
    local deduped_1_1, deduped_2_1;
    deduped_2_1 := NumberElements( a_1 );
    deduped_1_1 := BigInt( 1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, a_1, a_1, NrBlockColumnsAndListOfBlockColumns, [ NTuple( 2, deduped_1_1, [ NTuple( 2, deduped_1_1, deduped_2_1 ) ] ), NTuple( 2, BigInt( 0 ), CapJitTypedExpression( [  ], function (  )
                      return rec(
                          filter := IsList,
                          element_type := rec(
                              filter := IsNTuple,
                              element_types := [ rec(
                                      filter := IsInt ), rec(
                                      filter := IsInt ) ] ) );
                  end ) ) ][1 + BooleanToInteger( deduped_2_1 = 0 )] );
end
########
        
    , 100 );
    
    ##
    AddTensorProductOnObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, NumberElements, NumberElements( arg2_1 ) * NumberElements( arg3_1 ) );
end
########
        
    , 100 );
    
    ##
    AddTensorProductOnMorphismsWithGivenTensorProducts( cat,
        
########
function ( cat_1, s_1, alpha_1, beta_1, r_1 )
    local deduped_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1;
    deduped_9_1 := NrBlockColumnsAndListOfBlockColumns( beta_1 );
    deduped_8_1 := NrBlockColumnsAndListOfBlockColumns( alpha_1 );
    deduped_7_1 := deduped_9_1[1];
    deduped_6_1 := [ 1 .. deduped_8_1[1] ];
    hoisted_5_1 := [ 1 .. deduped_7_1 ];
    hoisted_4_1 := NumberElements( Source( beta_1 ) );
    hoisted_3_1 := deduped_9_1[2];
    hoisted_2_1 := BigInt( 1 );
    deduped_1_1 := deduped_8_1[2];
    return CreateCapCategoryMorphismWithAttributes( cat_1, s_1, r_1, NrBlockColumnsAndListOfBlockColumns, NTuple( 2, Sum( List( deduped_6_1, function ( i_2 )
                    local deduped_1_2;
                    deduped_1_2 := deduped_1_1[i_2];
                    return deduped_1_2[2] - deduped_1_2[1] + hoisted_2_1;
                end ) ) * deduped_7_1, Concatenation( List( deduped_6_1, function ( i_2 )
                  local deduped_1_2;
                  deduped_1_2 := deduped_1_1[i_2];
                  return Concatenation( List( [ deduped_1_2[1] .. deduped_1_2[2] ], function ( j_3 )
                            local deduped_1_3;
                            deduped_1_3 := hoisted_4_1 * (j_3 - 1);
                            return List( hoisted_5_1, function ( k_4 )
                                    local deduped_1_4;
                                    deduped_1_4 := hoisted_3_1[k_4];
                                    return NTuple( 2, deduped_1_4[1] + deduped_1_3, deduped_1_4[2] + deduped_1_3 );
                                end );
                        end ) );
              end ) ) ) );
end
########
        
    , 100 );
    
    if IsBound( cat!.precompiled_functions_added ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "precompiled functions have already been added before" );
        
    fi;
    
    cat!.precompiled_functions_added := true;
    
end );

BindGlobal( "CategoryOfKroneckerComonoids_precompiled", function (  )
  local category_constructor, cat;
    
    category_constructor :=
        
        
        function (  )
    return CategoryOfKroneckerComonoids(  : no_precompiled_code := true );
end;
        
        
    
    cat := category_constructor(  : FinalizeCategory := false, no_precompiled_code := true );
    
    ADD_FUNCTIONS_FOR_CategoryOfKroneckerComonoids_precompiled( cat );
    
    Finalize( cat );
    
    return cat;
    
end );
