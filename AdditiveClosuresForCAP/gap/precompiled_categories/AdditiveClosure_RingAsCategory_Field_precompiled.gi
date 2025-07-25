# SPDX-License-Identifier: GPL-2.0-or-later
# AdditiveClosuresForCAP: Additive closures for pre-abelian categories
#
# Implementations
#
BindGlobal( "ADD_FUNCTIONS_FOR_AdditiveClosure_RingAsCategory_Field_precompiled", function ( cat )
    
    ##
    AddAdditionForMorphisms( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    local hoisted_3_1, hoisted_4_1, deduped_6_1, hoisted_7_1, deduped_8_1, deduped_9_1, deduped_10_1;
    deduped_10_1 := UnderlyingCategory( cat_1 );
    deduped_9_1 := Range( alpha_1 );
    deduped_8_1 := Source( alpha_1 );
    hoisted_7_1 := [ 1 .. Length( ObjectList( deduped_9_1 ) ) ];
    deduped_6_1 := RingAsCategoryUniqueObject( deduped_10_1 );
    hoisted_4_1 := List( MorphismMatrix( beta_1 ), function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, UnderlyingRingElement );
        end );
    hoisted_3_1 := List( MorphismMatrix( alpha_1 ), function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, UnderlyingRingElement );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_8_1, deduped_9_1, MorphismMatrix, List( [ 1 .. Length( ObjectList( deduped_8_1 ) ) ], function ( i_2 )
              local hoisted_1_2, hoisted_2_2;
              hoisted_2_2 := hoisted_4_1[i_2];
              hoisted_1_2 := hoisted_3_1[i_2];
              return List( hoisted_7_1, function ( j_3 )
                      return CreateCapCategoryMorphismWithAttributes( deduped_10_1, deduped_6_1, deduped_6_1, UnderlyingRingElement, hoisted_1_2[j_3] + hoisted_2_2[j_3] );
                  end );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddAdditiveInverseForMorphisms( cat,
        
########
function ( cat_1, alpha_1 )
    local hoisted_1_1, deduped_3_1, hoisted_4_1, deduped_5_1, deduped_6_1, deduped_7_1;
    deduped_7_1 := UnderlyingCategory( cat_1 );
    deduped_6_1 := Range( alpha_1 );
    deduped_5_1 := Source( alpha_1 );
    hoisted_4_1 := [ 1 .. Length( ObjectList( deduped_6_1 ) ) ];
    deduped_3_1 := RingAsCategoryUniqueObject( deduped_7_1 );
    hoisted_1_1 := List( MorphismMatrix( alpha_1 ), function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, function ( logic_new_func_x_3 )
                    return - UnderlyingRingElement( logic_new_func_x_3 );
                end );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_5_1, deduped_6_1, MorphismMatrix, List( [ 1 .. Length( ObjectList( deduped_5_1 ) ) ], function ( i_2 )
              local hoisted_1_2;
              hoisted_1_2 := hoisted_1_1[i_2];
              return List( hoisted_4_1, function ( j_3 )
                      return CreateCapCategoryMorphismWithAttributes( deduped_7_1, deduped_3_1, deduped_3_1, UnderlyingRingElement, hoisted_1_2[j_3] );
                  end );
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
            return Length( ObjectList( s_2 ) );
        end );
    deduped_1_1 := Sum( deduped_2_1{[ 1 .. i_1 - 1 ]} );
    return CreateCapCategoryMorphismWithAttributes( cat_1, S_1[i_1], Range( alpha_1 ), MorphismMatrix, MorphismMatrix( alpha_1 ){[ deduped_1_1 + 1 .. deduped_1_1 + deduped_2_1[i_1] ]} );
end
########
        
    , 100 );
    
    ##
    AddComponentOfMorphismIntoDirectSum( cat,
        
########
function ( cat_1, alpha_1, S_1, i_1 )
    local hoisted_1_1, deduped_2_1, deduped_3_1;
    deduped_3_1 := List( S_1, function ( s_2 )
            return Length( ObjectList( s_2 ) );
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
    AddDirectSum( cat,
        
########
function ( cat_1, objects_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, ObjectList, Concatenation( List( [ 1 .. Length( objects_1 ) ], function ( i_2 )
                return CAP_JIT_INCOMPLETE_LOGIC( ObjectList( CAP_JIT_INCOMPLETE_LOGIC( objects_1[i_2] ) ) );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.DirectSum :=
        
########
function ( cat_1, objects_1 )
    local hoisted_1_1;
    hoisted_1_1 := List( objects_1, ObjectList );
    return CreateCapCategoryObjectWithAttributes( cat_1, ObjectList, Concatenation( List( [ 1 .. Length( objects_1 ) ], function ( i_2 )
                return hoisted_1_1[i_2];
            end ) ) );
end
########
        
    ;
    
    ##
    AddDistinguishedObjectOfHomomorphismStructure( cat,
        
########
function ( cat_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, ObjectList, [ RingAsCategoryUniqueObject( UnderlyingCategory( cat_1 ) ) ] );
end
########
        
    , 100 );
    
    ##
    AddHomomorphismStructureOnMorphismsWithGivenObjects( cat,
        
########
function ( cat_1, source_1, alpha_1, beta_1, range_1 )
    local hoisted_1_1, hoisted_2_1, deduped_4_1, hoisted_5_1, hoisted_6_1, hoisted_8_1, deduped_10_1, deduped_11_1, deduped_12_1;
    deduped_12_1 := UnderlyingCategory( cat_1 );
    deduped_11_1 := Length( ObjectList( Source( beta_1 ) ) );
    deduped_10_1 := Length( ObjectList( Range( beta_1 ) ) );
    hoisted_8_1 := [ 1 .. Length( ObjectList( Source( alpha_1 ) ) ) ];
    hoisted_6_1 := [ 1 .. deduped_11_1 ];
    hoisted_5_1 := [ 1 .. deduped_10_1 ];
    deduped_4_1 := RingAsCategoryUniqueObject( deduped_12_1 );
    hoisted_2_1 := List( MorphismMatrix( beta_1 ), function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, UnderlyingRingElement );
        end );
    hoisted_1_1 := List( MorphismMatrix( alpha_1 ), function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, UnderlyingRingElement );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, source_1, range_1, MorphismMatrix, UnionOfRowsListList( Length( ObjectList( range_1 ) ), List( [ 1 .. Length( ObjectList( Range( alpha_1 ) ) ) ], function ( j_2 )
                return UnionOfColumnsListList( deduped_11_1, List( hoisted_8_1, function ( i_3 )
                          local hoisted_1_3;
                          hoisted_1_3 := hoisted_1_1[i_3][j_2];
                          return UnionOfRowsListList( deduped_10_1, List( hoisted_6_1, function ( s_4 )
                                    local hoisted_1_4;
                                    hoisted_1_4 := hoisted_2_1[s_4];
                                    return UnionOfColumnsListList( 1, List( hoisted_5_1, function ( t_5 )
                                              return [ [ CreateCapCategoryMorphismWithAttributes( deduped_12_1, deduped_4_1, deduped_4_1, UnderlyingRingElement, hoisted_1_3 * hoisted_1_4[t_5] ) ] ];
                                          end ) );
                                end ) );
                      end ) );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    AddHomomorphismStructureOnObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, ObjectList, Concatenation( ListWithIdenticalEntries( Length( ObjectList( arg2_1 ) ), Concatenation( ListWithIdenticalEntries( Length( ObjectList( arg3_1 ) ), [ RingAsCategoryUniqueObject( UnderlyingCategory( cat_1 ) ) ] ) ) ) ) );
end
########
        
    , 100 );
    
    ##
    AddIdentityMorphism( cat,
        
########
function ( cat_1, a_1 )
    local hoisted_1_1, deduped_3_1, deduped_4_1, deduped_5_1, deduped_6_1;
    deduped_6_1 := CommutativeRingOfLinearCategory( cat_1 );
    deduped_5_1 := UnderlyingCategory( cat_1 );
    deduped_4_1 := RingAsCategoryUniqueObject( deduped_5_1 );
    deduped_3_1 := [ 1 .. Length( ObjectList( a_1 ) ) ];
    hoisted_1_1 := CreateCapCategoryMorphismWithAttributes( deduped_5_1, deduped_4_1, deduped_4_1, UnderlyingRingElement, OneImmutable( deduped_6_1 ) );
    return CreateCapCategoryMorphismWithAttributes( cat_1, a_1, a_1, MorphismMatrix, List( deduped_3_1, function ( i_2 )
              return List( deduped_3_1, function ( j_3 )
                      if i_2 = j_3 then
                          return hoisted_1_1;
                      else
                          return CreateCapCategoryMorphismWithAttributes( deduped_5_1, deduped_4_1, deduped_4_1, UnderlyingRingElement, ZeroImmutable( deduped_6_1 ) );
                      fi;
                      return;
                  end );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddInterpretMorphismAsMorphismFromDistinguishedObjectToHomomorphismStructureWithGivenObjects( cat,
        
########
function ( cat_1, source_1, alpha_1, range_1 )
    local hoisted_1_1, hoisted_2_1, deduped_4_1;
    deduped_4_1 := Length( ObjectList( source_1 ) );
    hoisted_2_1 := [ 1 .. Length( ObjectList( Range( alpha_1 ) ) ) ];
    hoisted_1_1 := MorphismMatrix( alpha_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, source_1, range_1, MorphismMatrix, UnionOfColumnsListList( deduped_4_1, List( [ 1 .. Length( ObjectList( Source( alpha_1 ) ) ) ], function ( j_2 )
                local hoisted_1_2;
                hoisted_1_2 := hoisted_1_1[j_2];
                return UnionOfColumnsListList( deduped_4_1, List( hoisted_2_1, function ( s_3 )
                          return [ [ hoisted_1_2[s_3] ] ];
                      end ) );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    AddInterpretMorphismFromDistinguishedObjectToHomomorphismStructureAsMorphism( cat,
        
########
function ( cat_1, source_1, range_1, alpha_1 )
    local hoisted_2_1, hoisted_3_1, deduped_4_1;
    deduped_4_1 := Length( ObjectList( range_1 ) );
    hoisted_3_1 := [ 1 .. deduped_4_1 ];
    hoisted_2_1 := MorphismMatrix( alpha_1 )[1];
    return CreateCapCategoryMorphismWithAttributes( cat_1, source_1, range_1, MorphismMatrix, List( [ 1 .. Length( ObjectList( source_1 ) ) ], function ( j_2 )
              local hoisted_1_2;
              hoisted_1_2 := (j_2 - 1) * deduped_4_1;
              return List( hoisted_3_1, function ( s_3 )
                      return hoisted_2_1[hoisted_1_2 + s_3];
                  end );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddIsCongruentForMorphisms( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_3_1, hoisted_4_1, hoisted_5_1, deduped_6_1, deduped_7_1;
    deduped_7_1 := Length( ObjectList( Range( arg2_1 ) ) );
    deduped_6_1 := Length( ObjectList( Source( arg2_1 ) ) );
    if deduped_6_1 <> Length( ObjectList( Source( arg3_1 ) ) ) then
        return false;
    elif deduped_7_1 <> Length( ObjectList( Range( arg3_1 ) ) ) then
        return false;
    else
        hoisted_5_1 := [ 1 .. deduped_7_1 ];
        hoisted_4_1 := List( MorphismMatrix( arg3_1 ), function ( logic_new_func_list_2 )
                return List( logic_new_func_list_2, UnderlyingRingElement );
            end );
        hoisted_3_1 := List( MorphismMatrix( arg2_1 ), function ( logic_new_func_list_2 )
                return List( logic_new_func_list_2, UnderlyingRingElement );
            end );
        return ForAll( [ 1 .. deduped_6_1 ], function ( i_2 )
                local hoisted_1_2, hoisted_2_2;
                hoisted_2_2 := hoisted_4_1[i_2];
                hoisted_1_2 := hoisted_3_1[i_2];
                return ForAll( hoisted_5_1, function ( j_3 )
                        return hoisted_1_2[j_3] = hoisted_2_2[j_3];
                    end );
            end );
    fi;
    return;
end
########
        
    , 100 );
    
    ##
    AddIsEqualForMorphisms( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_3_1, hoisted_4_1, hoisted_5_1, deduped_6_1, deduped_7_1;
    deduped_7_1 := Length( ObjectList( Range( arg2_1 ) ) );
    deduped_6_1 := Length( ObjectList( Source( arg2_1 ) ) );
    if deduped_6_1 <> Length( ObjectList( Source( arg3_1 ) ) ) then
        return false;
    elif deduped_7_1 <> Length( ObjectList( Range( arg3_1 ) ) ) then
        return false;
    else
        hoisted_5_1 := [ 1 .. deduped_7_1 ];
        hoisted_4_1 := List( MorphismMatrix( arg3_1 ), function ( logic_new_func_list_2 )
                return List( logic_new_func_list_2, UnderlyingRingElement );
            end );
        hoisted_3_1 := List( MorphismMatrix( arg2_1 ), function ( logic_new_func_list_2 )
                return List( logic_new_func_list_2, UnderlyingRingElement );
            end );
        return ForAll( [ 1 .. deduped_6_1 ], function ( i_2 )
                local hoisted_1_2, hoisted_2_2;
                hoisted_2_2 := hoisted_4_1[i_2];
                hoisted_1_2 := hoisted_3_1[i_2];
                return ForAll( hoisted_5_1, function ( j_3 )
                        return hoisted_1_2[j_3] = hoisted_2_2[j_3];
                    end );
            end );
    fi;
    return;
end
########
        
    , 100 );
    
    ##
    AddIsEqualForObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_3_1;
    deduped_3_1 := Length( ObjectList( arg2_1 ) );
    if deduped_3_1 <> Length( ObjectList( arg3_1 ) ) then
        return false;
    else
        return ForAll( [ 1 .. deduped_3_1 ], function ( i_2 )
                return true;
            end );
    fi;
    return;
end
########
        
    , 100 );
    
    ##
    AddIsWellDefinedForMorphisms( cat,
        
########
function ( cat_1, alpha_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, deduped_7_1, deduped_8_1, deduped_9_1, deduped_10_1;
    deduped_10_1 := MorphismMatrix( alpha_1 );
    deduped_9_1 := Length( ObjectList( Range( alpha_1 ) ) );
    deduped_8_1 := Length( ObjectList( Source( alpha_1 ) ) );
    deduped_7_1 := [ 1 .. deduped_8_1 ];
    hoisted_6_1 := [ 1 .. deduped_9_1 ];
    hoisted_5_1 := CommutativeRingOfLinearCategory( cat_1 );
    hoisted_4_1 := List( deduped_10_1, function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, UnderlyingRingElement );
        end );
    hoisted_2_1 := List( deduped_10_1, Length );
    hoisted_1_1 := List( deduped_10_1, IsList );
    if not (IsList( deduped_10_1 ) and Length( deduped_10_1 ) = deduped_8_1) then
        return false;
    elif not ForAll( deduped_7_1, function ( i_2 )
                 return (hoisted_1_1[i_2] and hoisted_2_1[i_2] = deduped_9_1);
             end ) then
        return false;
    elif not ForAll( deduped_7_1, function ( i_2 )
                 local hoisted_1_2;
                 hoisted_1_2 := hoisted_4_1[i_2];
                 return ForAll( hoisted_6_1, function ( j_3 )
                         return (hoisted_1_2[j_3] in hoisted_5_1 and true and true);
                     end );
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
    AddIsWellDefinedForObjects( cat,
        
########
function ( cat_1, arg2_1 )
    local deduped_1_1;
    deduped_1_1 := ObjectList( arg2_1 );
    if not IsList( deduped_1_1 ) then
        return false;
    elif not ForAll( deduped_1_1, function ( obj_2 )
                 return true;
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
    AddIsZeroForMorphisms( cat,
        
########
function ( cat_1, arg2_1 )
    local hoisted_1_1, hoisted_2_1;
    hoisted_2_1 := [ 1 .. Length( ObjectList( Range( arg2_1 ) ) ) ];
    hoisted_1_1 := MorphismMatrix( arg2_1 );
    return ForAll( [ 1 .. Length( ObjectList( Source( arg2_1 ) ) ) ], function ( i_2 )
            local hoisted_1_2;
            hoisted_1_2 := hoisted_1_1[i_2];
            return ForAll( hoisted_2_1, function ( j_3 )
                    return IsZero( UnderlyingRingElement( hoisted_1_2[j_3] ) );
                end );
        end );
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
    AddMorphismDatum( cat,
        
########
function ( cat_1, arg2_1 )
    return MorphismMatrix( arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddMultiplyWithElementOfCommutativeRingForMorphisms( cat,
        
########
function ( cat_1, r_1, alpha_1 )
    local hoisted_1_1, deduped_3_1, hoisted_4_1, deduped_5_1, deduped_6_1, deduped_7_1;
    deduped_7_1 := UnderlyingCategory( cat_1 );
    deduped_6_1 := Range( alpha_1 );
    deduped_5_1 := Source( alpha_1 );
    hoisted_4_1 := [ 1 .. Length( ObjectList( deduped_6_1 ) ) ];
    deduped_3_1 := RingAsCategoryUniqueObject( deduped_7_1 );
    hoisted_1_1 := List( MorphismMatrix( alpha_1 ), function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, UnderlyingRingElement );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_5_1, deduped_6_1, MorphismMatrix, List( [ 1 .. Length( ObjectList( deduped_5_1 ) ) ], function ( i_2 )
              local hoisted_1_2;
              hoisted_1_2 := hoisted_1_1[i_2];
              return List( hoisted_4_1, function ( j_3 )
                      return CreateCapCategoryMorphismWithAttributes( deduped_7_1, deduped_3_1, deduped_3_1, UnderlyingRingElement, r_1 * hoisted_1_2[j_3] );
                  end );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddObjectConstructor( cat,
        
########
function ( cat_1, arg2_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, ObjectList, arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddObjectDatum( cat,
        
########
function ( cat_1, arg2_1 )
    return ObjectList( arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddPreCompose( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    local hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, deduped_9_1, hoisted_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1;
    deduped_15_1 := UnderlyingCategory( cat_1 );
    deduped_14_1 := Range( beta_1 );
    deduped_13_1 := Source( alpha_1 );
    deduped_12_1 := RingAsCategoryUniqueObject( deduped_15_1 );
    deduped_11_1 := Length( ObjectList( Range( alpha_1 ) ) );
    hoisted_10_1 := [ 1 .. Length( ObjectList( deduped_14_1 ) ) ];
    deduped_9_1 := Iterated( ListWithIdenticalEntries( deduped_11_1, deduped_12_1 ), function ( alpha_2, beta_2 )
            return deduped_12_1;
        end, deduped_12_1 );
    hoisted_7_1 := ZeroImmutable( CommutativeRingOfLinearCategory( cat_1 ) );
    hoisted_6_1 := [ 1 .. deduped_11_1 ];
    hoisted_5_1 := List( MorphismMatrix( beta_1 ), function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, UnderlyingRingElement );
        end );
    hoisted_4_1 := List( MorphismMatrix( alpha_1 ), function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, UnderlyingRingElement );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, deduped_13_1, deduped_14_1, MorphismMatrix, List( [ 1 .. Length( ObjectList( deduped_13_1 ) ) ], function ( i_2 )
              local hoisted_1_2;
              hoisted_1_2 := hoisted_4_1[i_2];
              return List( hoisted_10_1, function ( j_3 )
                      return CreateCapCategoryMorphismWithAttributes( deduped_15_1, deduped_9_1, deduped_9_1, UnderlyingRingElement, Iterated( List( hoisted_6_1, function ( k_4 )
                                  return hoisted_1_2[k_4] * hoisted_5_1[k_4][j_3];
                              end ), function ( alpha_4, beta_4 )
                                return alpha_4 + beta_4;
                            end, hoisted_7_1 ) );
                  end );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddSumOfMorphisms( cat,
        
########
function ( cat_1, source_1, list_of_morphisms_1, range_1 )
    local deduped_1_1, hoisted_2_1, hoisted_4_1, deduped_5_1;
    deduped_5_1 := UnderlyingCategory( cat_1 );
    hoisted_4_1 := [ 1 .. Length( ObjectList( range_1 ) ) ];
    hoisted_2_1 := ZeroImmutable( CommutativeRingOfLinearCategory( cat_1 ) );
    deduped_1_1 := RingAsCategoryUniqueObject( deduped_5_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, source_1, range_1, MorphismMatrix, List( [ 1 .. Length( ObjectList( source_1 ) ) ], function ( i_2 )
              return List( hoisted_4_1, function ( j_3 )
                      return CreateCapCategoryMorphismWithAttributes( deduped_5_1, Iterated( List( list_of_morphisms_1, function ( m_4 )
                                  return CAP_JIT_INCOMPLETE_LOGIC( Source( CAP_JIT_INCOMPLETE_LOGIC( CAP_JIT_INCOMPLETE_LOGIC( MorphismMatrix( m_4 )[i_2] )[j_3] ) ) );
                              end ), function ( alpha_4, beta_4 )
                                return deduped_1_1;
                            end, deduped_1_1 ), Iterated( List( list_of_morphisms_1, function ( m_4 )
                                  return CAP_JIT_INCOMPLETE_LOGIC( Range( CAP_JIT_INCOMPLETE_LOGIC( CAP_JIT_INCOMPLETE_LOGIC( MorphismMatrix( m_4 )[i_2] )[j_3] ) ) );
                              end ), function ( alpha_4, beta_4 )
                                return deduped_1_1;
                            end, deduped_1_1 ), UnderlyingRingElement, Iterated( List( list_of_morphisms_1, function ( m_4 )
                                  return CAP_JIT_INCOMPLETE_LOGIC( UnderlyingRingElement( CAP_JIT_INCOMPLETE_LOGIC( CAP_JIT_INCOMPLETE_LOGIC( MorphismMatrix( m_4 )[i_2] )[j_3] ) ) );
                              end ), function ( alpha_4, beta_4 )
                                return alpha_4 + beta_4;
                            end, hoisted_2_1 ) );
                  end );
          end ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.SumOfMorphisms :=
        
########
function ( cat_1, source_1, list_of_morphisms_1, range_1 )
    local deduped_1_1, hoisted_2_1, hoisted_4_1, deduped_5_1;
    deduped_5_1 := UnderlyingCategory( cat_1 );
    hoisted_4_1 := [ 1 .. Length( ObjectList( range_1 ) ) ];
    hoisted_2_1 := ZeroImmutable( CommutativeRingOfLinearCategory( cat_1 ) );
    deduped_1_1 := RingAsCategoryUniqueObject( deduped_5_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, source_1, range_1, MorphismMatrix, List( [ 1 .. Length( ObjectList( source_1 ) ) ], function ( i_2 )
              return List( hoisted_4_1, function ( j_3 )
                      return CreateCapCategoryMorphismWithAttributes( deduped_5_1, Iterated( List( list_of_morphisms_1, function ( m_4 )
                                  return List( MorphismMatrix( m_4 ), function ( logic_new_func_list_5 )
                                              return List( logic_new_func_list_5, Source );
                                          end )[i_2][j_3];
                              end ), function ( alpha_4, beta_4 )
                                return deduped_1_1;
                            end, deduped_1_1 ), Iterated( List( list_of_morphisms_1, function ( m_4 )
                                  return List( MorphismMatrix( m_4 ), function ( logic_new_func_list_5 )
                                              return List( logic_new_func_list_5, Range );
                                          end )[i_2][j_3];
                              end ), function ( alpha_4, beta_4 )
                                return deduped_1_1;
                            end, deduped_1_1 ), UnderlyingRingElement, Iterated( List( list_of_morphisms_1, function ( m_4 )
                                  return List( MorphismMatrix( m_4 ), function ( logic_new_func_list_5 )
                                              return List( logic_new_func_list_5, UnderlyingRingElement );
                                          end )[i_2][j_3];
                              end ), function ( alpha_4, beta_4 )
                                return alpha_4 + beta_4;
                            end, hoisted_2_1 ) );
                  end );
          end ) );
end
########
        
    ;
    
    ##
    AddTensorProductOnMorphismsWithGivenTensorProducts( cat,
        
########
function ( cat_1, s_1, alpha_1, beta_1, r_1 )
    local hoisted_4_1, hoisted_6_1, deduped_8_1, hoisted_9_1, deduped_10_1, deduped_11_1, deduped_12_1;
    deduped_12_1 := UnderlyingCategory( cat_1 );
    deduped_11_1 := Length( ObjectList( Target( beta_1 ) ) );
    deduped_10_1 := Length( ObjectList( Source( beta_1 ) ) );
    hoisted_9_1 := [ 0 .. Length( ObjectList( Target( alpha_1 ) ) ) * deduped_11_1 - 1 ];
    deduped_8_1 := RingAsCategoryUniqueObject( deduped_12_1 );
    hoisted_6_1 := List( MorphismMatrix( beta_1 ), function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, UnderlyingRingElement );
        end );
    hoisted_4_1 := List( MorphismMatrix( alpha_1 ), function ( logic_new_func_list_2 )
            return List( logic_new_func_list_2, UnderlyingRingElement );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, s_1, r_1, MorphismMatrix, List( [ 0 .. Length( ObjectList( Source( alpha_1 ) ) ) * deduped_10_1 - 1 ], function ( i_2 )
              local hoisted_1_2, hoisted_2_2;
              hoisted_2_2 := hoisted_6_1[1 + REM_INT( i_2, deduped_10_1 )];
              hoisted_1_2 := hoisted_4_1[1 + QUO_INT( i_2, deduped_10_1 )];
              return List( hoisted_9_1, function ( j_3 )
                      return CreateCapCategoryMorphismWithAttributes( deduped_12_1, deduped_8_1, deduped_8_1, UnderlyingRingElement, hoisted_1_2[(1 + QUO_INT( j_3, deduped_11_1 ))] * hoisted_2_2[(1 + REM_INT( j_3, deduped_11_1 ))] );
                  end );
          end ) );
end
########
        
    , 100 );
    
    ##
    AddTensorProductOnObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, ObjectList, ListWithIdenticalEntries( Length( [ 0 .. Length( ObjectList( arg2_1 ) ) * Length( ObjectList( arg3_1 ) ) - 1 ] ), RingAsCategoryUniqueObject( UnderlyingCategory( cat_1 ) ) ) );
end
########
        
    , 100 );
    
    ##
    AddTensorUnit( cat,
        
########
function ( cat_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, ObjectList, [ RingAsCategoryUniqueObject( UnderlyingCategory( cat_1 ) ) ] );
end
########
        
    , 100 );
    
    ##
    AddUniversalMorphismFromDirectSumWithGivenDirectSum( cat,
        
########
function ( cat_1, objects_1, T_1, tau_1, P_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, P_1, T_1, MorphismMatrix, UnionOfRowsListList( Length( ObjectList( T_1 ) ), List( tau_1, MorphismMatrix ) ) );
end
########
        
    , 100 );
    
    ##
    AddUniversalMorphismIntoDirectSumWithGivenDirectSum( cat,
        
########
function ( cat_1, objects_1, T_1, tau_1, P_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, T_1, P_1, MorphismMatrix, UnionOfColumnsListList( Length( ObjectList( T_1 ) ), List( tau_1, MorphismMatrix ) ) );
end
########
        
    , 100 );
    
    ##
    AddZeroMorphism( cat,
        
########
function ( cat_1, a_1, b_1 )
    local deduped_1_1, deduped_2_1;
    deduped_2_1 := UnderlyingCategory( cat_1 );
    deduped_1_1 := RingAsCategoryUniqueObject( deduped_2_1 );
    return CreateCapCategoryMorphismWithAttributes( cat_1, a_1, b_1, MorphismMatrix, ListWithIdenticalEntries( Length( ObjectList( a_1 ) ), ListWithIdenticalEntries( Length( ObjectList( b_1 ) ), CreateCapCategoryMorphismWithAttributes( deduped_2_1, deduped_1_1, deduped_1_1, UnderlyingRingElement, ZeroImmutable( CommutativeRingOfLinearCategory( cat_1 ) ) ) ) ) );
end
########
        
    , 100 );
    
    ##
    AddZeroObject( cat,
        
########
function ( cat_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, ObjectList, [  ] );
end
########
        
    , 100 );
    
    if IsBound( cat!.precompiled_functions_added ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "precompiled functions have already been added before" );
        
    fi;
    
    cat!.precompiled_functions_added := true;
    
end );

BindGlobal( "AdditiveClosure_RingAsCategory_Field_precompiled", function ( homalg_ring )
  local category_constructor, cat;
    
    category_constructor :=
        
        
        function ( homalg_ring )
    return AdditiveClosure( RING_AS_CATEGORY( homalg_ring : FinalizeCategory := true ) );
end;
        
        
    
    cat := category_constructor( homalg_ring : FinalizeCategory := false, no_precompiled_code := true );
    
    ADD_FUNCTIONS_FOR_AdditiveClosure_RingAsCategory_Field_precompiled( cat );
    
    Finalize( cat );
    
    return cat;
    
end );
