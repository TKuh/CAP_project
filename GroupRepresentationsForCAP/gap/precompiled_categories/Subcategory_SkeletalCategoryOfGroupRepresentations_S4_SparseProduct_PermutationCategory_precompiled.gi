# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Implementations
#
BindGlobal( "ADD_FUNCTIONS_FOR_Subcategory_SkeletalCategoryOfGroupRepresentations_S4_SparseProduct_PermutationCategory_precompiled", function ( cat )
    
    ##
    AddIsEqualForObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, deduped_4_1, deduped_5_1, deduped_6_1, deduped_7_1;
    deduped_7_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( arg3_1 );
    deduped_6_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( arg2_1 );
    deduped_5_1 := deduped_7_1[1];
    deduped_4_1 := deduped_6_1[1];
    hoisted_2_1 := deduped_7_1[3];
    hoisted_3_1 := List( [ 1 .. deduped_5_1 ], function ( n_2 )
            return hoisted_2_1[n_2];
        end );
    hoisted_1_1 := deduped_6_1[3];
    return deduped_4_1 = deduped_5_1 and deduped_6_1[2] = deduped_7_1[2] and ForAll( [ 1 .. deduped_4_1 ], function ( i_2 )
              return CAP_JIT_INCOMPLETE_LOGIC( hoisted_1_1[CAP_JIT_INCOMPLETE_LOGIC( i_2 )] ) = hoisted_3_1[i_2];
          end );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.IsEqualForObjects :=
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, deduped_5_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1;
    deduped_9_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( arg3_1 );
    deduped_8_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( arg2_1 );
    deduped_7_1 := deduped_9_1[1];
    deduped_6_1 := deduped_8_1[1];
    deduped_5_1 := [ 1 .. deduped_6_1 ];
    hoisted_3_1 := deduped_9_1[3];
    hoisted_4_1 := List( [ 1 .. deduped_7_1 ], function ( n_2 )
            return hoisted_3_1[n_2];
        end );
    hoisted_1_1 := deduped_8_1[3];
    hoisted_2_1 := List( deduped_5_1, function ( n_2 )
            return hoisted_1_1[n_2];
        end );
    return deduped_6_1 = deduped_7_1 and deduped_8_1[2] = deduped_9_1[2] and ForAll( deduped_5_1, function ( i_2 )
              return hoisted_2_1[i_2] = hoisted_4_1[i_2];
          end );
end
########
        
    ;
    
    ##
    AddIsEqualForMorphisms( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, deduped_9_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1;
    deduped_15_1 := TripleOfNrSupportListOfSupportListOfPermutations( arg3_1 );
    deduped_14_1 := TripleOfNrSupportListOfSupportListOfPermutations( arg2_1 );
    deduped_13_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( Source( arg3_1 ) );
    deduped_12_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( Source( arg2_1 ) );
    deduped_11_1 := deduped_15_1[1];
    deduped_10_1 := deduped_14_1[1];
    deduped_9_1 := [ 1 .. deduped_11_1 ];
    hoisted_6_1 := deduped_13_1[3];
    hoisted_7_1 := List( [ 1 .. deduped_13_1[1] ], function ( n_2 )
            return hoisted_6_1[n_2];
        end );
    hoisted_8_1 := List( deduped_9_1, function ( n_2 )
            return hoisted_7_1[n_2];
        end );
    hoisted_4_1 := deduped_15_1[3];
    hoisted_5_1 := List( deduped_9_1, function ( n_2 )
            return hoisted_4_1[n_2];
        end );
    hoisted_2_1 := deduped_12_1[3];
    hoisted_3_1 := List( [ 1 .. deduped_12_1[1] ], function ( n_2 )
            return hoisted_2_1[n_2];
        end );
    hoisted_1_1 := deduped_14_1[3];
    return deduped_10_1 = deduped_11_1 and deduped_14_1[2] = deduped_15_1[2] and ForAll( [ 1 .. deduped_10_1 ], function ( i_2 )
              local deduped_1_2;
              deduped_1_2 := CAP_JIT_INCOMPLETE_LOGIC( i_2 );
              return ListPerm( CAP_JIT_INCOMPLETE_LOGIC( hoisted_1_1[deduped_1_2] ), CAP_JIT_INCOMPLETE_LOGIC( hoisted_3_1[deduped_1_2] ) ) = ListPerm( hoisted_5_1[i_2], hoisted_8_1[i_2] );
          end );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.IsEqualForMorphisms :=
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, hoisted_9_1, hoisted_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1;
    deduped_18_1 := TripleOfNrSupportListOfSupportListOfPermutations( arg3_1 );
    deduped_17_1 := TripleOfNrSupportListOfSupportListOfPermutations( arg2_1 );
    deduped_16_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( Source( arg3_1 ) );
    deduped_15_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( Source( arg2_1 ) );
    deduped_14_1 := deduped_18_1[1];
    deduped_13_1 := deduped_17_1[1];
    deduped_12_1 := [ 1 .. deduped_14_1 ];
    deduped_11_1 := [ 1 .. deduped_13_1 ];
    hoisted_8_1 := deduped_16_1[3];
    hoisted_9_1 := List( [ 1 .. deduped_16_1[1] ], function ( n_2 )
            return hoisted_8_1[n_2];
        end );
    hoisted_10_1 := List( deduped_12_1, function ( n_2 )
            return hoisted_9_1[n_2];
        end );
    hoisted_6_1 := deduped_18_1[3];
    hoisted_7_1 := List( deduped_12_1, function ( n_2 )
            return hoisted_6_1[n_2];
        end );
    hoisted_3_1 := deduped_15_1[3];
    hoisted_4_1 := List( [ 1 .. deduped_15_1[1] ], function ( n_2 )
            return hoisted_3_1[n_2];
        end );
    hoisted_5_1 := List( deduped_11_1, function ( n_2 )
            return hoisted_4_1[n_2];
        end );
    hoisted_1_1 := deduped_17_1[3];
    hoisted_2_1 := List( deduped_11_1, function ( n_2 )
            return hoisted_1_1[n_2];
        end );
    return deduped_13_1 = deduped_14_1 and deduped_17_1[2] = deduped_18_1[2] and ForAll( deduped_11_1, function ( i_2 )
              return ListPerm( hoisted_2_1[i_2], hoisted_5_1[i_2] ) = ListPerm( hoisted_7_1[i_2], hoisted_10_1[i_2] );
          end );
end
########
        
    ;
    
    ##
    AddIsCongruentForMorphisms( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, deduped_9_1, deduped_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1;
    deduped_15_1 := TripleOfNrSupportListOfSupportListOfPermutations( arg3_1 );
    deduped_14_1 := TripleOfNrSupportListOfSupportListOfPermutations( arg2_1 );
    deduped_13_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( Source( arg3_1 ) );
    deduped_12_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( Source( arg2_1 ) );
    deduped_11_1 := deduped_15_1[1];
    deduped_10_1 := deduped_14_1[1];
    deduped_9_1 := [ 1 .. deduped_11_1 ];
    hoisted_6_1 := deduped_13_1[3];
    hoisted_7_1 := List( [ 1 .. deduped_13_1[1] ], function ( n_2 )
            return hoisted_6_1[n_2];
        end );
    hoisted_8_1 := List( deduped_9_1, function ( n_2 )
            return hoisted_7_1[n_2];
        end );
    hoisted_4_1 := deduped_15_1[3];
    hoisted_5_1 := List( deduped_9_1, function ( n_2 )
            return hoisted_4_1[n_2];
        end );
    hoisted_2_1 := deduped_12_1[3];
    hoisted_3_1 := List( [ 1 .. deduped_12_1[1] ], function ( n_2 )
            return hoisted_2_1[n_2];
        end );
    hoisted_1_1 := deduped_14_1[3];
    return deduped_10_1 = deduped_11_1 and deduped_14_1[2] = deduped_15_1[2] and ForAll( [ 1 .. deduped_10_1 ], function ( i_2 )
              local deduped_1_2;
              deduped_1_2 := CAP_JIT_INCOMPLETE_LOGIC( i_2 );
              return ListPerm( CAP_JIT_INCOMPLETE_LOGIC( hoisted_1_1[deduped_1_2] ), CAP_JIT_INCOMPLETE_LOGIC( hoisted_3_1[deduped_1_2] ) ) = ListPerm( hoisted_5_1[i_2], hoisted_8_1[i_2] );
          end );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.IsCongruentForMorphisms :=
        
########
function ( cat_1, arg2_1, arg3_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, hoisted_6_1, hoisted_7_1, hoisted_8_1, hoisted_9_1, hoisted_10_1, deduped_11_1, deduped_12_1, deduped_13_1, deduped_14_1, deduped_15_1, deduped_16_1, deduped_17_1, deduped_18_1;
    deduped_18_1 := TripleOfNrSupportListOfSupportListOfPermutations( arg3_1 );
    deduped_17_1 := TripleOfNrSupportListOfSupportListOfPermutations( arg2_1 );
    deduped_16_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( Source( arg3_1 ) );
    deduped_15_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( Source( arg2_1 ) );
    deduped_14_1 := deduped_18_1[1];
    deduped_13_1 := deduped_17_1[1];
    deduped_12_1 := [ 1 .. deduped_14_1 ];
    deduped_11_1 := [ 1 .. deduped_13_1 ];
    hoisted_8_1 := deduped_16_1[3];
    hoisted_9_1 := List( [ 1 .. deduped_16_1[1] ], function ( n_2 )
            return hoisted_8_1[n_2];
        end );
    hoisted_10_1 := List( deduped_12_1, function ( n_2 )
            return hoisted_9_1[n_2];
        end );
    hoisted_6_1 := deduped_18_1[3];
    hoisted_7_1 := List( deduped_12_1, function ( n_2 )
            return hoisted_6_1[n_2];
        end );
    hoisted_3_1 := deduped_15_1[3];
    hoisted_4_1 := List( [ 1 .. deduped_15_1[1] ], function ( n_2 )
            return hoisted_3_1[n_2];
        end );
    hoisted_5_1 := List( deduped_11_1, function ( n_2 )
            return hoisted_4_1[n_2];
        end );
    hoisted_1_1 := deduped_17_1[3];
    hoisted_2_1 := List( deduped_11_1, function ( n_2 )
            return hoisted_1_1[n_2];
        end );
    return deduped_13_1 = deduped_14_1 and deduped_17_1[2] = deduped_18_1[2] and ForAll( deduped_11_1, function ( i_2 )
              return ListPerm( hoisted_2_1[i_2], hoisted_5_1[i_2] ) = ListPerm( hoisted_7_1[i_2], hoisted_10_1[i_2] );
          end );
end
########
        
    ;
    
    ##
    AddIsWellDefinedForObjects( cat,
        
########
function ( cat_1, arg2_1 )
    local hoisted_1_1, hoisted_3_1, deduped_5_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1, deduped_10_1;
    deduped_10_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( arg2_1 );
    deduped_9_1 := deduped_10_1[3];
    deduped_8_1 := deduped_10_1[2];
    deduped_7_1 := deduped_10_1[1];
    deduped_6_1 := [ 1 .. deduped_7_1 ];
    deduped_5_1 := List( deduped_6_1, function ( n_2 )
            return deduped_9_1[n_2];
        end );
    hoisted_3_1 := List( deduped_9_1, IsBigInt );
    hoisted_1_1 := NrIrreducibleCharacters( cat_1 );
    if deduped_7_1 <> Length( deduped_8_1 ) or deduped_7_1 <> deduped_7_1 then
        return false;
    elif not ForAll( deduped_8_1, function ( n_2 )
                 return 1 <= n_2 and n_2 <= hoisted_1_1;
             end ) then
        return false;
    elif not ForAll( [ 1 .. deduped_7_1 - 1 ], function ( n_2 )
                 return deduped_8_1[n_2] < deduped_8_1[n_2 + 1];
             end ) then
        return false;
    elif not ForAll( deduped_6_1, function ( n_2 )
                 return CAP_JIT_INCOMPLETE_LOGIC( hoisted_3_1[CAP_JIT_INCOMPLETE_LOGIC( n_2 )] ) and deduped_5_1[n_2] >= 0;
             end ) then
        return false;
    elif ForAny( deduped_6_1, function ( n_2 )
              return deduped_5_1[n_2] = 0;
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
    cat!.cached_precompiled_functions.IsWellDefinedForObjects :=
        
########
function ( cat_1, arg2_1 )
    local hoisted_1_1, hoisted_3_1, hoisted_4_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1, deduped_10_1, deduped_11_1;
    deduped_11_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( arg2_1 );
    deduped_10_1 := deduped_11_1[3];
    deduped_9_1 := deduped_11_1[2];
    deduped_8_1 := deduped_11_1[1];
    deduped_7_1 := [ 1 .. deduped_8_1 ];
    deduped_6_1 := List( deduped_7_1, function ( n_2 )
            return deduped_10_1[n_2];
        end );
    hoisted_3_1 := List( deduped_10_1, IsBigInt );
    hoisted_4_1 := List( deduped_7_1, function ( n_2 )
            return hoisted_3_1[n_2];
        end );
    hoisted_1_1 := NrIrreducibleCharacters( cat_1 );
    if deduped_8_1 <> Length( deduped_9_1 ) or deduped_8_1 <> deduped_8_1 then
        return false;
    elif not ForAll( deduped_9_1, function ( n_2 )
                 return 1 <= n_2 and n_2 <= hoisted_1_1;
             end ) then
        return false;
    elif not ForAll( [ 1 .. deduped_8_1 - 1 ], function ( n_2 )
                 return deduped_9_1[n_2] < deduped_9_1[n_2 + 1];
             end ) then
        return false;
    elif not ForAll( deduped_7_1, function ( n_2 )
                 return hoisted_4_1[n_2] and deduped_6_1[n_2] >= 0;
             end ) then
        return false;
    elif ForAny( deduped_7_1, function ( n_2 )
              return deduped_6_1[n_2] = 0;
          end ) then
        return false;
    else
        return true;
    fi;
    return;
end
########
        
    ;
    
    ##
    AddIsWellDefinedForMorphisms( cat,
        
########
function ( cat_1, alpha_1 )
    local hoisted_2_1, hoisted_3_1, hoisted_4_1, deduped_5_1, hoisted_6_1, deduped_7_1, deduped_8_1, deduped_9_1, deduped_10_1, deduped_11_1;
    deduped_11_1 := TripleOfNrSupportListOfSupportListOfPermutations( alpha_1 );
    deduped_10_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( Source( alpha_1 ) );
    deduped_9_1 := deduped_11_1[2];
    deduped_8_1 := deduped_11_1[1];
    deduped_7_1 := [ 1 .. deduped_8_1 ];
    hoisted_6_1 := deduped_11_1[3];
    hoisted_3_1 := deduped_10_1[3];
    hoisted_4_1 := List( [ 1 .. deduped_10_1[1] ], function ( n_2 )
            return hoisted_3_1[n_2];
        end );
    deduped_5_1 := List( deduped_7_1, function ( n_2 )
            return hoisted_4_1[n_2];
        end );
    hoisted_2_1 := NrIrreducibleCharacters( cat_1 );
    if deduped_8_1 <> Length( deduped_9_1 ) or deduped_8_1 <> deduped_8_1 then
        return false;
    elif not ForAll( deduped_7_1, function ( i_2 )
                 local deduped_1_2;
                 deduped_1_2 := deduped_9_1[i_2];
                 return 1 <= deduped_1_2 and deduped_1_2 <= hoisted_2_1;
             end ) then
        return false;
    elif ForAny( deduped_7_1, function ( i_2 )
              local deduped_1_2;
              deduped_1_2 := deduped_5_1[i_2] = 0;
              return deduped_1_2 and deduped_1_2;
          end ) then
        return false;
    elif not ForAll( [ 1 .. deduped_8_1 - 1 ], function ( i_2 )
                 return deduped_9_1[i_2] < deduped_9_1[i_2 + 1];
             end ) then
        return false;
    elif not ForAll( deduped_7_1, function ( i_2 )
                 local deduped_2_2, deduped_3_2, deduped_4_2;
                 if not true then
                     return false;
                 else
                     deduped_4_2 := deduped_5_1[i_2];
                     deduped_3_2 := ListPerm( CAP_JIT_INCOMPLETE_LOGIC( hoisted_6_1[CAP_JIT_INCOMPLETE_LOGIC( i_2 )] ), deduped_4_2 );
                     deduped_2_2 := List( deduped_3_2, function ( i_3 )
                             return -1 + i_3;
                         end );
                     return ForAll( deduped_2_2, function ( a_3 )
                                 return IsBigInt( a_3 ) and a_3 >= 0;
                             end ) and deduped_4_2 = Length( deduped_3_2 ) and ForAll( deduped_2_2, function ( a_3 )
                               return a_3 < deduped_4_2;
                           end );
                 fi;
                 return;
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
    cat!.cached_precompiled_functions.IsWellDefinedForMorphisms :=
        
########
function ( cat_1, alpha_1 )
    local hoisted_2_1, hoisted_3_1, hoisted_4_1, deduped_5_1, hoisted_6_1, hoisted_7_1, deduped_8_1, deduped_9_1, deduped_10_1, deduped_11_1, deduped_12_1;
    deduped_12_1 := TripleOfNrSupportListOfSupportListOfPermutations( alpha_1 );
    deduped_11_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( Source( alpha_1 ) );
    deduped_10_1 := deduped_12_1[2];
    deduped_9_1 := deduped_12_1[1];
    deduped_8_1 := [ 1 .. deduped_9_1 ];
    hoisted_6_1 := deduped_12_1[3];
    hoisted_7_1 := List( deduped_8_1, function ( n_2 )
            return hoisted_6_1[n_2];
        end );
    hoisted_3_1 := deduped_11_1[3];
    hoisted_4_1 := List( [ 1 .. deduped_11_1[1] ], function ( n_2 )
            return hoisted_3_1[n_2];
        end );
    deduped_5_1 := List( deduped_8_1, function ( n_2 )
            return hoisted_4_1[n_2];
        end );
    hoisted_2_1 := NrIrreducibleCharacters( cat_1 );
    if deduped_9_1 <> Length( deduped_10_1 ) or deduped_9_1 <> deduped_9_1 then
        return false;
    elif not ForAll( deduped_8_1, function ( i_2 )
                 local deduped_1_2;
                 deduped_1_2 := deduped_10_1[i_2];
                 return 1 <= deduped_1_2 and deduped_1_2 <= hoisted_2_1;
             end ) then
        return false;
    elif ForAny( deduped_8_1, function ( i_2 )
              local deduped_1_2;
              deduped_1_2 := deduped_5_1[i_2] = 0;
              return deduped_1_2 and deduped_1_2;
          end ) then
        return false;
    elif not ForAll( [ 1 .. deduped_9_1 - 1 ], function ( i_2 )
                 return deduped_10_1[i_2] < deduped_10_1[i_2 + 1];
             end ) then
        return false;
    elif not ForAll( deduped_8_1, function ( i_2 )
                 local deduped_2_2, deduped_3_2, deduped_4_2;
                 if not true then
                     return false;
                 else
                     deduped_4_2 := deduped_5_1[i_2];
                     deduped_3_2 := ListPerm( hoisted_7_1[i_2], deduped_4_2 );
                     deduped_2_2 := List( deduped_3_2, function ( i_3 )
                             return -1 + i_3;
                         end );
                     return ForAll( deduped_2_2, function ( a_3 )
                                 return IsBigInt( a_3 ) and a_3 >= 0;
                             end ) and deduped_4_2 = Length( deduped_3_2 ) and ForAll( deduped_2_2, function ( a_3 )
                               return a_3 < deduped_4_2;
                           end );
                 fi;
                 return;
             end ) then
        return false;
    else
        return true;
    fi;
    return;
end
########
        
    ;
    
    ##
    AddObjectConstructor( cat,
        
########
function ( cat_1, arg2_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, TripleOfNrSupportListOfSupportListOfCardinalitites, arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddMorphismConstructor( cat,
        
########
function ( cat_1, arg2_1, arg3_1, arg4_1 )
    return CreateCapCategoryMorphismWithAttributes( cat_1, arg2_1, arg4_1, TripleOfNrSupportListOfSupportListOfPermutations, arg3_1 );
end
########
        
    , 100 );
    
    ##
    AddObjectDatum( cat,
        
########
function ( cat_1, arg2_1 )
    return TripleOfNrSupportListOfSupportListOfCardinalitites( arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddMorphismDatum( cat,
        
########
function ( cat_1, arg2_1 )
    return TripleOfNrSupportListOfSupportListOfPermutations( arg2_1 );
end
########
        
    , 100 );
    
    ##
    AddIdentityMorphism( cat,
        
########
function ( cat_1, a_1 )
    local hoisted_1_1, deduped_2_1, deduped_3_1;
    deduped_3_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( a_1 );
    deduped_2_1 := deduped_3_1[1];
    hoisted_1_1 := deduped_3_1[3];
    return CreateCapCategoryMorphismWithAttributes( cat_1, a_1, a_1, TripleOfNrSupportListOfSupportListOfPermutations, NTuple( 3, deduped_2_1, deduped_3_1[2], List( [ 1 .. deduped_2_1 ], function ( n_2 )
                return CAP_JIT_INCOMPLETE_LOGIC( PermList( [ 1 .. CAP_JIT_INCOMPLETE_LOGIC( hoisted_1_1[CAP_JIT_INCOMPLETE_LOGIC( n_2 )] ) ] ) );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.IdentityMorphism :=
        
########
function ( cat_1, a_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, deduped_4_1, deduped_5_1, deduped_6_1;
    deduped_6_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( a_1 );
    deduped_5_1 := deduped_6_1[1];
    deduped_4_1 := [ 1 .. deduped_5_1 ];
    hoisted_1_1 := deduped_6_1[3];
    hoisted_2_1 := List( deduped_4_1, function ( n_2 )
            return hoisted_1_1[n_2];
        end );
    hoisted_3_1 := List( deduped_4_1, function ( n_2 )
            return PermList( [ 1 .. hoisted_2_1[n_2] ] );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, a_1, a_1, TripleOfNrSupportListOfSupportListOfPermutations, NTuple( 3, deduped_5_1, deduped_6_1[2], List( deduped_4_1, function ( n_2 )
                return hoisted_3_1[n_2];
            end ) ) );
end
########
        
    ;
    
    ##
    AddPreCompose( cat,
        
########
function ( cat_1, alpha_1, beta_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, deduped_4_1, deduped_5_1, deduped_6_1;
    deduped_6_1 := TripleOfNrSupportListOfSupportListOfPermutations( beta_1 );
    deduped_5_1 := TripleOfNrSupportListOfSupportListOfPermutations( alpha_1 );
    deduped_4_1 := deduped_5_1[1];
    hoisted_2_1 := deduped_6_1[3];
    hoisted_3_1 := List( [ 1 .. deduped_6_1[1] ], function ( n_2 )
            return hoisted_2_1[n_2];
        end );
    hoisted_1_1 := deduped_5_1[3];
    return CreateCapCategoryMorphismWithAttributes( cat_1, Source( alpha_1 ), Range( beta_1 ), TripleOfNrSupportListOfSupportListOfPermutations, NTuple( 3, deduped_4_1, deduped_5_1[2], List( [ 1 .. deduped_4_1 ], function ( n_2 )
                local deduped_1_2;
                deduped_1_2 := CAP_JIT_INCOMPLETE_LOGIC( n_2 );
                return CAP_JIT_INCOMPLETE_LOGIC( CAP_JIT_INCOMPLETE_LOGIC( hoisted_1_1[deduped_1_2] ) * hoisted_3_1[deduped_1_2] );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.PreCompose :=
        
########
function ( cat_1, alpha_1, beta_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, deduped_6_1, deduped_7_1, deduped_8_1, deduped_9_1;
    deduped_9_1 := TripleOfNrSupportListOfSupportListOfPermutations( beta_1 );
    deduped_8_1 := TripleOfNrSupportListOfSupportListOfPermutations( alpha_1 );
    deduped_7_1 := deduped_8_1[1];
    deduped_6_1 := [ 1 .. deduped_7_1 ];
    hoisted_3_1 := deduped_9_1[3];
    hoisted_4_1 := List( [ 1 .. deduped_9_1[1] ], function ( n_2 )
            return hoisted_3_1[n_2];
        end );
    hoisted_1_1 := deduped_8_1[3];
    hoisted_2_1 := List( deduped_6_1, function ( n_2 )
            return hoisted_1_1[n_2];
        end );
    hoisted_5_1 := List( deduped_6_1, function ( n_2 )
            return hoisted_2_1[n_2] * hoisted_4_1[n_2];
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, Source( alpha_1 ), Range( beta_1 ), TripleOfNrSupportListOfSupportListOfPermutations, NTuple( 3, deduped_7_1, deduped_8_1[2], List( deduped_6_1, function ( n_2 )
                return hoisted_5_1[n_2];
            end ) ) );
end
########
        
    ;
    
    ##
    AddInverseForMorphisms( cat,
        
########
function ( cat_1, alpha_1 )
    local hoisted_1_1, deduped_2_1, deduped_3_1;
    deduped_3_1 := TripleOfNrSupportListOfSupportListOfPermutations( alpha_1 );
    deduped_2_1 := deduped_3_1[1];
    hoisted_1_1 := List( deduped_3_1[3], InverseImmutable );
    return CreateCapCategoryMorphismWithAttributes( cat_1, Range( alpha_1 ), Source( alpha_1 ), TripleOfNrSupportListOfSupportListOfPermutations, NTuple( 3, deduped_2_1, deduped_3_1[2], List( [ 1 .. deduped_2_1 ], function ( n_2 )
                return CAP_JIT_INCOMPLETE_LOGIC( hoisted_1_1[CAP_JIT_INCOMPLETE_LOGIC( n_2 )] );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.InverseForMorphisms :=
        
########
function ( cat_1, alpha_1 )
    local hoisted_1_1, hoisted_2_1, hoisted_3_1, deduped_4_1, deduped_5_1, deduped_6_1;
    deduped_6_1 := TripleOfNrSupportListOfSupportListOfPermutations( alpha_1 );
    deduped_5_1 := deduped_6_1[1];
    deduped_4_1 := [ 1 .. deduped_5_1 ];
    hoisted_1_1 := List( deduped_6_1[3], InverseImmutable );
    hoisted_2_1 := List( deduped_4_1, function ( n_2 )
            return hoisted_1_1[n_2];
        end );
    hoisted_3_1 := List( deduped_4_1, function ( i_2 )
            return hoisted_2_1[i_2];
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, Range( alpha_1 ), Source( alpha_1 ), TripleOfNrSupportListOfSupportListOfPermutations, NTuple( 3, deduped_5_1, deduped_6_1[2], List( deduped_4_1, function ( n_2 )
                return hoisted_3_1[n_2];
            end ) ) );
end
########
        
    ;
    
    ##
    AddCoproduct( cat,
        
########
function ( cat_1, objects_1 )
    local hoisted_2_1, deduped_3_1, deduped_4_1;
    deduped_4_1 := Union( List( objects_1, function ( x_2 )
              return TripleOfNrSupportListOfSupportListOfCardinalitites( x_2 )[2];
          end ) );
    deduped_3_1 := Length( deduped_4_1 );
    hoisted_2_1 := [ 0 ];
    return CreateCapCategoryObjectWithAttributes( cat_1, TripleOfNrSupportListOfSupportListOfCardinalitites, NTuple( 3, deduped_3_1, deduped_4_1, List( [ 1 .. deduped_3_1 ], function ( n_2 )
                local deduped_1_2;
                deduped_1_2 := deduped_4_1[CAP_JIT_INCOMPLETE_LOGIC( n_2 )];
                return CAP_JIT_INCOMPLETE_LOGIC( Sum( List( objects_1, function ( x_3 )
                            local hoisted_1_3, deduped_2_3, deduped_3_3;
                            deduped_3_3 := TripleOfNrSupportListOfSupportListOfCardinalitites( x_3 );
                            deduped_2_3 := deduped_3_3[2];
                            hoisted_1_3 := deduped_3_3[3];
                            return [ hoisted_2_1, List( [ 1 .. deduped_3_3[1] ], function ( n_4 )
                                              return hoisted_1_3[n_4];
                                          end ){Positions( deduped_2_3, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_2_3 )][1];
                        end ) ) );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.Coproduct :=
        
########
function ( cat_1, objects_1 )
    local hoisted_2_1, hoisted_3_1, deduped_4_1, deduped_5_1, deduped_6_1;
    deduped_6_1 := Union( List( objects_1, function ( x_2 )
              return TripleOfNrSupportListOfSupportListOfCardinalitites( x_2 )[2];
          end ) );
    deduped_5_1 := Length( deduped_6_1 );
    deduped_4_1 := [ 1 .. deduped_5_1 ];
    hoisted_2_1 := [ 0 ];
    hoisted_3_1 := List( deduped_4_1, function ( n_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_6_1[n_2];
            return Sum( List( objects_1, function ( x_3 )
                      local hoisted_1_3, deduped_2_3, deduped_3_3;
                      deduped_3_3 := TripleOfNrSupportListOfSupportListOfCardinalitites( x_3 );
                      deduped_2_3 := deduped_3_3[2];
                      hoisted_1_3 := deduped_3_3[3];
                      return [ hoisted_2_1, List( [ 1 .. deduped_3_3[1] ], function ( n_4 )
                                        return hoisted_1_3[n_4];
                                    end ){Positions( deduped_2_3, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_2_3 )][1];
                  end ) );
        end );
    return CreateCapCategoryObjectWithAttributes( cat_1, TripleOfNrSupportListOfSupportListOfCardinalitites, NTuple( 3, deduped_5_1, deduped_6_1, List( deduped_4_1, function ( n_2 )
                return hoisted_3_1[n_2];
            end ) ) );
end
########
        
    ;
    
    ##
    AddCoproductFunctorialWithGivenCoproducts( cat,
        
########
function ( cat_1, P_1, objects_1, L_1, objectsp_1, Pp_1 )
    local deduped_2_1, hoisted_3_1, hoisted_4_1, deduped_5_1, deduped_6_1;
    deduped_6_1 := Union( List( L_1, function ( x_2 )
              return TripleOfNrSupportListOfSupportListOfPermutations( x_2 )[2];
          end ) );
    deduped_5_1 := Length( deduped_6_1 );
    hoisted_4_1 := [ 1 .. Length( L_1 ) ];
    hoisted_3_1 := [ PermList( CapJitTypedExpression( [  ], function (  )
                  return rec(
                      filter := IsList,
                      element_type := rec(
                          filter := IsInt ) );
              end ) ) ];
    deduped_2_1 := [ 0 ];
    return CreateCapCategoryMorphismWithAttributes( cat_1, P_1, Pp_1, TripleOfNrSupportListOfSupportListOfPermutations, NTuple( 3, deduped_5_1, deduped_6_1, List( [ 1 .. deduped_5_1 ], function ( n_2 )
                local deduped_1_2, deduped_2_2;
                deduped_1_2 := deduped_6_1[CAP_JIT_INCOMPLETE_LOGIC( n_2 )];
                deduped_2_2 := List( objectsp_1, function ( x_3 )
                        local hoisted_1_3, deduped_2_3, deduped_3_3;
                        deduped_3_3 := TripleOfNrSupportListOfSupportListOfCardinalitites( x_3 );
                        deduped_2_3 := deduped_3_3[2];
                        hoisted_1_3 := deduped_3_3[3];
                        return [ deduped_2_1, List( [ 1 .. deduped_3_3[1] ], function ( n_4 )
                                          return hoisted_1_3[n_4];
                                      end ){Positions( deduped_2_3, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_2_3 )][1];
                    end );
                return CAP_JIT_INCOMPLETE_LOGIC( PermList( Concatenation( List( hoisted_4_1, function ( i_3 )
                              local hoisted_1_3, hoisted_2_3, hoisted_3_3, hoisted_4_3, hoisted_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3, deduped_10_3, deduped_11_3, deduped_12_3, deduped_13_3, deduped_14_3;
                              deduped_14_3 := CAP_JIT_INCOMPLETE_LOGIC( L_1[i_3] );
                              deduped_13_3 := TripleOfNrSupportListOfSupportListOfPermutations( deduped_14_3 );
                              deduped_12_3 := Sum( deduped_2_2{[ 1 .. i_3 - 1 ]} );
                              deduped_11_3 := TripleOfNrSupportListOfSupportListOfCardinalitites( Source( deduped_14_3 ) );
                              deduped_10_3 := deduped_13_3[2];
                              deduped_9_3 := [ 1 .. deduped_13_3[1] ];
                              deduped_8_3 := Positions( deduped_10_3, deduped_1_2 );
                              deduped_7_3 := 1 + BooleanToInteger( deduped_1_2 in deduped_10_3 );
                              hoisted_1_3 := deduped_11_3[3];
                              hoisted_2_3 := List( [ 1 .. deduped_11_3[1] ], function ( n_4 )
                                      return hoisted_1_3[n_4];
                                  end );
                              deduped_6_3 := [ deduped_2_1, List( deduped_9_3, function ( n_4 )
                                                return hoisted_2_3[n_4];
                                            end ){deduped_8_3} ][deduped_7_3][1];
                              hoisted_5_3 := List( [ deduped_12_3 .. deduped_12_3 + deduped_2_2[i_3] - 1 ], function ( i_4 )
                                      return 1 + i_4;
                                  end );
                              hoisted_3_3 := deduped_13_3[3];
                              hoisted_4_3 := CAP_JIT_INCOMPLETE_LOGIC( ListPerm( [ hoisted_3_1, List( deduped_9_3, function ( n_4 )
                                                    return hoisted_3_3[n_4];
                                                end ){deduped_8_3} ][deduped_7_3][1], deduped_6_3 ) );
                              return List( [ 1 .. CAP_JIT_INCOMPLETE_LOGIC( deduped_6_3 ) ], function ( i_4 )
                                      return hoisted_5_3[hoisted_4_3[i_4]];
                                  end );
                          end ) ) ) );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.CoproductFunctorialWithGivenCoproducts :=
        
########
function ( cat_1, P_1, objects_1, L_1, objectsp_1, Pp_1 )
    local deduped_2_1, hoisted_3_1, hoisted_4_1, hoisted_5_1, deduped_6_1, deduped_7_1, deduped_8_1;
    deduped_8_1 := Union( List( L_1, function ( x_2 )
              return TripleOfNrSupportListOfSupportListOfPermutations( x_2 )[2];
          end ) );
    deduped_7_1 := Length( deduped_8_1 );
    deduped_6_1 := [ 1 .. deduped_7_1 ];
    hoisted_4_1 := [ 1 .. Length( L_1 ) ];
    hoisted_3_1 := [ PermList( CapJitTypedExpression( [  ], function (  )
                  return rec(
                      filter := IsList,
                      element_type := rec(
                          filter := IsInt ) );
              end ) ) ];
    deduped_2_1 := [ 0 ];
    hoisted_5_1 := List( deduped_6_1, function ( n_2 )
            local deduped_1_2, hoisted_2_2, deduped_3_2, hoisted_4_2;
            deduped_1_2 := deduped_8_1[n_2];
            hoisted_4_2 := List( L_1, function ( x_3 )
                    local hoisted_1_3, hoisted_2_3, hoisted_3_3, deduped_4_3, deduped_5_3, deduped_6_3, deduped_7_3, deduped_8_3, deduped_9_3;
                    deduped_9_3 := TripleOfNrSupportListOfSupportListOfPermutations( x_3 );
                    deduped_8_3 := TripleOfNrSupportListOfSupportListOfCardinalitites( Source( x_3 ) );
                    deduped_7_3 := deduped_9_3[2];
                    deduped_6_3 := [ 1 .. deduped_9_3[1] ];
                    deduped_5_3 := Positions( deduped_7_3, deduped_1_2 );
                    deduped_4_3 := 1 + BooleanToInteger( deduped_1_2 in deduped_7_3 );
                    hoisted_2_3 := deduped_8_3[3];
                    hoisted_3_3 := List( [ 1 .. deduped_8_3[1] ], function ( n_4 )
                            return hoisted_2_3[n_4];
                        end );
                    hoisted_1_3 := deduped_9_3[3];
                    return ListPerm( [ hoisted_3_1, List( deduped_6_3, function ( n_4 )
                                        return hoisted_1_3[n_4];
                                    end ){deduped_5_3} ][deduped_4_3][1], [ deduped_2_1, List( deduped_6_3, function ( n_4 )
                                        return hoisted_3_3[n_4];
                                    end ){deduped_5_3} ][deduped_4_3][1] );
                end );
            deduped_3_2 := List( objectsp_1, function ( x_3 )
                    local hoisted_1_3, deduped_2_3, deduped_3_3;
                    deduped_3_3 := TripleOfNrSupportListOfSupportListOfCardinalitites( x_3 );
                    deduped_2_3 := deduped_3_3[2];
                    hoisted_1_3 := deduped_3_3[3];
                    return [ deduped_2_1, List( [ 1 .. deduped_3_3[1] ], function ( n_4 )
                                      return hoisted_1_3[n_4];
                                  end ){Positions( deduped_2_3, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_2_3 )][1];
                end );
            hoisted_2_2 := List( L_1, function ( x_3 )
                    local hoisted_1_3, hoisted_2_3, deduped_3_3, deduped_4_3, deduped_5_3;
                    deduped_5_3 := TripleOfNrSupportListOfSupportListOfPermutations( x_3 );
                    deduped_4_3 := TripleOfNrSupportListOfSupportListOfCardinalitites( Source( x_3 ) );
                    deduped_3_3 := deduped_5_3[2];
                    hoisted_1_3 := deduped_4_3[3];
                    hoisted_2_3 := List( [ 1 .. deduped_4_3[1] ], function ( n_4 )
                            return hoisted_1_3[n_4];
                        end );
                    return [ deduped_2_1, List( [ 1 .. deduped_5_3[1] ], function ( n_4 )
                                      return hoisted_2_3[n_4];
                                  end ){Positions( deduped_3_3, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_3_3 )][1];
                end );
            return PermList( Concatenation( List( hoisted_4_1, function ( i_3 )
                        local hoisted_1_3, hoisted_2_3, deduped_3_3;
                        deduped_3_3 := Sum( deduped_3_2{[ 1 .. i_3 - 1 ]} );
                        hoisted_2_3 := List( [ deduped_3_3 .. deduped_3_3 + deduped_3_2[i_3] - 1 ], function ( i_4 )
                                return 1 + i_4;
                            end );
                        hoisted_1_3 := hoisted_4_2[i_3];
                        return List( [ 1 .. hoisted_2_2[i_3] ], function ( i_4 )
                                return hoisted_2_3[hoisted_1_3[i_4]];
                            end );
                    end ) ) );
        end );
    return CreateCapCategoryMorphismWithAttributes( cat_1, P_1, Pp_1, TripleOfNrSupportListOfSupportListOfPermutations, NTuple( 3, deduped_7_1, deduped_8_1, List( deduped_6_1, function ( n_2 )
                return hoisted_5_1[n_2];
            end ) ) );
end
########
        
    ;
    
    ##
    AddTensorProductOnObjects( cat,
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_3_1, deduped_4_1, deduped_6_1, deduped_7_1, hoisted_9_1, hoisted_10_1, hoisted_11_1, hoisted_12_1, deduped_13_1, deduped_16_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1;
    deduped_22_1 := UnderlyingIrreducibleCharacters( cat_1 );
    deduped_21_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( arg3_1 );
    deduped_20_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( arg2_1 );
    deduped_19_1 := [ 1 .. deduped_21_1[1] ];
    deduped_18_1 := [ 1 .. deduped_20_1[1] ];
    deduped_7_1 := [ 1 .. Length( deduped_22_1 ) ];
    deduped_6_1 := [ 1 .. NrIrreducibleCharacters( cat_1 ) ];
    deduped_4_1 := deduped_21_1[2];
    deduped_3_1 := deduped_20_1[2];
    deduped_17_1 := Union( List( deduped_18_1, function ( i_2 )
              local hoisted_1_2;
              hoisted_1_2 := deduped_3_1[i_2];
              return Union( List( deduped_19_1, function ( j_3 )
                        local hoisted_1_3, hoisted_2_3;
                        hoisted_1_3 := deduped_4_1[j_3];
                        hoisted_2_3 := List( deduped_6_1, function ( k_4 )
                                return IsZero( SGREPS_ScalarProduct( deduped_22_1, k_4, hoisted_1_2, hoisted_1_3 ) );
                            end );
                        return Filtered( deduped_7_1, function ( i_4 )
                                return not hoisted_2_3[i_4];
                            end );
                    end ) );
          end ) );
    deduped_16_1 := Length( deduped_17_1 );
    deduped_13_1 := [ 0 ];
    hoisted_11_1 := deduped_21_1[3];
    hoisted_12_1 := List( deduped_19_1, function ( n_2 )
            return hoisted_11_1[n_2];
        end );
    hoisted_9_1 := deduped_20_1[3];
    hoisted_10_1 := List( deduped_18_1, function ( n_2 )
            return hoisted_9_1[n_2];
        end );
    return CreateCapCategoryObjectWithAttributes( cat_1, TripleOfNrSupportListOfSupportListOfCardinalitites, NTuple( 3, deduped_16_1, deduped_17_1, List( [ 1 .. deduped_16_1 ], function ( n_2 )
                local deduped_1_2;
                deduped_1_2 := deduped_17_1[CAP_JIT_INCOMPLETE_LOGIC( n_2 )];
                return CAP_JIT_INCOMPLETE_LOGIC( Sum( List( deduped_18_1, function ( i_3 )
                            local deduped_1_3, hoisted_2_3, deduped_4_3;
                            deduped_1_3 := deduped_3_1[i_3];
                            deduped_4_3 := Union( List( deduped_19_1, function ( j_4 )
                                      local hoisted_1_4, hoisted_2_4;
                                      hoisted_1_4 := deduped_4_1[j_4];
                                      hoisted_2_4 := List( deduped_6_1, function ( k_5 )
                                              return IsZero( SGREPS_ScalarProduct( deduped_22_1, k_5, deduped_1_3, hoisted_1_4 ) );
                                          end );
                                      return Filtered( deduped_7_1, function ( i_5 )
                                              return not hoisted_2_4[i_5];
                                          end );
                                  end ) );
                            hoisted_2_3 := hoisted_10_1[i_3];
                            return [ deduped_13_1, List( [ 1 .. Length( deduped_4_3 ) ], function ( n_4 )
                                              local deduped_1_4;
                                              deduped_1_4 := deduped_4_3[CAP_JIT_INCOMPLETE_LOGIC( n_4 )];
                                              return CAP_JIT_INCOMPLETE_LOGIC( Sum( List( deduped_19_1, function ( j_5 )
                                                          local deduped_1_5, hoisted_2_5, hoisted_3_5, hoisted_4_5, deduped_5_5;
                                                          deduped_1_5 := deduped_4_1[j_5];
                                                          hoisted_2_5 := List( deduped_6_1, function ( k_6 )
                                                                  return IsZero( SGREPS_ScalarProduct( deduped_22_1, k_6, deduped_1_3, deduped_1_5 ) );
                                                              end );
                                                          deduped_5_5 := Filtered( deduped_7_1, function ( i_6 )
                                                                  return not hoisted_2_5[i_6];
                                                              end );
                                                          hoisted_4_5 := hoisted_2_3 * hoisted_12_1[j_5];
                                                          hoisted_3_5 := List( deduped_6_1, function ( k_6 )
                                                                    return SGREPS_ScalarProduct( deduped_22_1, k_6, deduped_1_3, deduped_1_5 );
                                                                end ){deduped_5_5};
                                                          return [ deduped_13_1, List( [ 1 .. Length( deduped_5_5 ) ], function ( n_6 )
                                                                            return CAP_JIT_INCOMPLETE_LOGIC( hoisted_3_5[CAP_JIT_INCOMPLETE_LOGIC( n_6 )] * hoisted_4_5 );
                                                                        end ){Positions( deduped_5_5, deduped_1_4 )} ][1 + BooleanToInteger( deduped_1_4 in deduped_5_5 )][1];
                                                      end ) ) );
                                          end ){Positions( deduped_4_3, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_4_3 )][1];
                        end ) ) );
            end ) ) );
end
########
        
    , 100 );
    
    ##
    cat!.cached_precompiled_functions.TensorProductOnObjects :=
        
########
function ( cat_1, arg2_1, arg3_1 )
    local deduped_3_1, deduped_4_1, deduped_6_1, deduped_7_1, hoisted_9_1, hoisted_10_1, hoisted_11_1, hoisted_12_1, deduped_13_1, hoisted_16_1, deduped_17_1, deduped_18_1, deduped_19_1, deduped_20_1, deduped_21_1, deduped_22_1, deduped_23_1, deduped_24_1;
    deduped_24_1 := UnderlyingIrreducibleCharacters( cat_1 );
    deduped_23_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( arg3_1 );
    deduped_22_1 := TripleOfNrSupportListOfSupportListOfCardinalitites( arg2_1 );
    deduped_21_1 := [ 1 .. deduped_23_1[1] ];
    deduped_20_1 := [ 1 .. deduped_22_1[1] ];
    deduped_7_1 := [ 1 .. Length( deduped_24_1 ) ];
    deduped_6_1 := [ 1 .. NrIrreducibleCharacters( cat_1 ) ];
    deduped_4_1 := deduped_23_1[2];
    deduped_3_1 := deduped_22_1[2];
    deduped_19_1 := Union( List( deduped_20_1, function ( i_2 )
              local hoisted_1_2;
              hoisted_1_2 := deduped_3_1[i_2];
              return Union( List( deduped_21_1, function ( j_3 )
                        local hoisted_1_3, hoisted_2_3;
                        hoisted_1_3 := deduped_4_1[j_3];
                        hoisted_2_3 := List( deduped_6_1, function ( k_4 )
                                return IsZero( SGREPS_ScalarProduct( deduped_24_1, k_4, hoisted_1_2, hoisted_1_3 ) );
                            end );
                        return Filtered( deduped_7_1, function ( i_4 )
                                return not hoisted_2_3[i_4];
                            end );
                    end ) );
          end ) );
    deduped_18_1 := Length( deduped_19_1 );
    deduped_17_1 := [ 1 .. deduped_18_1 ];
    deduped_13_1 := [ 0 ];
    hoisted_11_1 := deduped_23_1[3];
    hoisted_12_1 := List( deduped_21_1, function ( n_2 )
            return hoisted_11_1[n_2];
        end );
    hoisted_9_1 := deduped_22_1[3];
    hoisted_10_1 := List( deduped_20_1, function ( n_2 )
            return hoisted_9_1[n_2];
        end );
    hoisted_16_1 := List( deduped_17_1, function ( n_2 )
            local deduped_1_2;
            deduped_1_2 := deduped_19_1[n_2];
            return Sum( List( deduped_20_1, function ( i_3 )
                      local deduped_1_3, hoisted_2_3, hoisted_4_3, hoisted_5_3, deduped_6_3, deduped_7_3;
                      deduped_1_3 := deduped_3_1[i_3];
                      deduped_7_3 := Union( List( deduped_21_1, function ( j_4 )
                                local hoisted_1_4, hoisted_2_4;
                                hoisted_1_4 := deduped_4_1[j_4];
                                hoisted_2_4 := List( deduped_6_1, function ( k_5 )
                                        return IsZero( SGREPS_ScalarProduct( deduped_24_1, k_5, deduped_1_3, hoisted_1_4 ) );
                                    end );
                                return Filtered( deduped_7_1, function ( i_5 )
                                        return not hoisted_2_4[i_5];
                                    end );
                            end ) );
                      deduped_6_3 := [ 1 .. Length( deduped_7_3 ) ];
                      hoisted_2_3 := hoisted_10_1[i_3];
                      hoisted_4_3 := List( deduped_6_3, function ( n_4 )
                              local deduped_1_4;
                              deduped_1_4 := deduped_7_3[n_4];
                              return Sum( List( deduped_21_1, function ( j_5 )
                                        local deduped_1_5, hoisted_2_5, hoisted_3_5, hoisted_4_5, hoisted_5_5, hoisted_6_5, deduped_7_5, deduped_8_5;
                                        deduped_1_5 := deduped_4_1[j_5];
                                        hoisted_2_5 := List( deduped_6_1, function ( k_6 )
                                                return IsZero( SGREPS_ScalarProduct( deduped_24_1, k_6, deduped_1_3, deduped_1_5 ) );
                                            end );
                                        deduped_8_5 := Filtered( deduped_7_1, function ( i_6 )
                                                return not hoisted_2_5[i_6];
                                            end );
                                        deduped_7_5 := [ 1 .. Length( deduped_8_5 ) ];
                                        hoisted_4_5 := hoisted_2_3 * hoisted_12_1[j_5];
                                        hoisted_3_5 := List( deduped_6_1, function ( k_6 )
                                                  return SGREPS_ScalarProduct( deduped_24_1, k_6, deduped_1_3, deduped_1_5 );
                                              end ){deduped_8_5};
                                        hoisted_5_5 := List( deduped_7_5, function ( n_6 )
                                                return hoisted_3_5[n_6] * hoisted_4_5;
                                            end );
                                        hoisted_6_5 := List( deduped_7_5, function ( n_6 )
                                                return hoisted_5_5[n_6];
                                            end );
                                        return [ deduped_13_1, List( deduped_7_5, function ( n_6 )
                                                          return hoisted_6_5[n_6];
                                                      end ){Positions( deduped_8_5, deduped_1_4 )} ][1 + BooleanToInteger( deduped_1_4 in deduped_8_5 )][1];
                                    end ) );
                          end );
                      hoisted_5_3 := List( deduped_6_3, function ( n_4 )
                              return hoisted_4_3[n_4];
                          end );
                      return [ deduped_13_1, List( deduped_6_3, function ( n_4 )
                                        return hoisted_5_3[n_4];
                                    end ){Positions( deduped_7_3, deduped_1_2 )} ][1 + BooleanToInteger( deduped_1_2 in deduped_7_3 )][1];
                  end ) );
        end );
    return CreateCapCategoryObjectWithAttributes( cat_1, TripleOfNrSupportListOfSupportListOfCardinalitites, NTuple( 3, deduped_18_1, deduped_19_1, List( deduped_17_1, function ( n_2 )
                return hoisted_16_1[n_2];
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

BindGlobal( "Subcategory_SkeletalCategoryOfGroupRepresentations_S4_SparseProduct_PermutationCategory_precompiled", function ( irreducible_characters )
  local category_constructor, cat;
    
    category_constructor :=
        
        
        function ( irreducible_characters )
    return SubcategoryOfSkeletalCategoryOfGroupRepresentationsOfSparseProductOfPermutationCategory( irreducible_characters : no_precompiled_code := true );
end;
        
        
    
    cat := category_constructor( irreducible_characters : FinalizeCategory := false, no_precompiled_code := true );
    
    ADD_FUNCTIONS_FOR_Subcategory_SkeletalCategoryOfGroupRepresentations_S4_SparseProduct_PermutationCategory_precompiled( cat );
    
    Finalize( cat );
    
    return cat;
    
end );
