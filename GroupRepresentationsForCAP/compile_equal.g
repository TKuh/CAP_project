######## Start compilation of
# Function added to SkeletalGroupRepresentations( SymmetricGroup( [ 1 .. 4 ] ),\
 Q ) for IsEqualForObjects
function ( cat, arg2, arg3 )
    return IsEqualForObjects( ModelingCategory( cat ), ModelingObject( cat, arg\
2 ), ModelingObject( cat, arg3 ) );
end

#### Continue compilation of
# Function added to SkeletalGroupRepresentations( SymmetricGroup( [ 1 .. 4 ] ),\
 Q ) for IsEqualForObjects
# current state:
function ( cat_1, arg2_1, arg3_1 )
    return IsEqualForObjects( ModelingCategory( CAP_JIT_INTERNAL_GLOBAL_VARIABL\
E_1 ), ModelingObject( CAP_JIT_INTERNAL_GLOBAL_VARIABLE_1, arg2_1 ), ModelingOb\
ject( CAP_JIT_INTERNAL_GLOBAL_VARIABLE_1, arg3_1 ) );
end
## start of resolving phase

######## Start compilation of
# ModelingObject method
function ( cat, obj )
    return ModelingTowerObjectConstructor( cat, ObjectDatum( cat, obj ) );
end

#### Continue compilation of
# ModelingObject method
# current state:
function ( cat_1, obj_1 )
    return ModelingTowerObjectConstructor( CAP_JIT_INTERNAL_GLOBAL_VARIABLE_1, \
ObjectDatum( CAP_JIT_INTERNAL_GLOBAL_VARIABLE_1, obj_1 ) );
end
## start of resolving phase

######## Start compilation of
# Function added to SkeletalGroupRepresentations( SymmetricGroup( [ 1 .. 4 ] ),\
 Q ) for ObjectDatum
function ( SGReps, obj )
    return ListOfPairsOfRankAndIndex( obj );
end

#### Continue compilation of
# Function added to SkeletalGroupRepresentations( SymmetricGroup( [ 1 .. 4 ] ),\
 Q ) for ObjectDatum
# current state:
function ( SGReps_1, obj_1 )
    return ListOfPairsOfRankAndIndex( obj_1 );
end
## start of resolving phase

#### Continue compilation of
# Function added to SkeletalGroupRepresentations( SymmetricGroup( [ 1 .. 4 ] ),\
 Q ) for ObjectDatum
# finished resolving phase, current state:
function ( SGReps_1, obj_1 )
    return ListOfPairsOfRankAndIndex( obj_1 );
end
## start of rule phase

######## Finished compilation of
# Function added to SkeletalGroupRepresentations( SymmetricGroup( [ 1 .. 4 ] ),\
 Q ) for ObjectDatum
# result:
function ( SGReps_1, obj_1 )
    return ListOfPairsOfRankAndIndex( obj_1 );
end

######## Start compilation of
# ModelingTowerObjectConstructor method
function ( SGReps, list_of_pairs_of_rank_and_index )
    local Coproduct, Rows, list_of_pairs_of_object_and_index;
    Coproduct := ModelingCategory( SGReps );
    Rows := UnderlyingCategoryOfRows( Coproduct );
    list_of_pairs_of_object_and_index := List( list_of_pairs_of_rank_and_index,\
 function ( pair )
            return Pair( CategoryOfRowsObject( Rows, pair[1] ), pair[2] );
        end );
    return ObjectConstructor( Coproduct, list_of_pairs_of_object_and_index );
end

#### Continue compilation of
# ModelingTowerObjectConstructor method
# current state:
function ( SGReps_1, list_of_pairs_of_rank_and_index_1 )
    local Coproduct_1, Rows_1, list_of_pairs_of_object_and_index_1;
    Coproduct_1 := ModelingCategory( CAP_JIT_INTERNAL_GLOBAL_VARIABLE_1 );
    Rows_1 := UnderlyingCategoryOfRows( Coproduct_1 );
    list_of_pairs_of_object_and_index_1 := List( list_of_pairs_of_rank_and_inde\
x_1, function ( pair_2 )
            return Pair( CategoryOfRowsObject( Rows_1, pair_2[1] ), pair_2[2] )\
;
        end );
    return ObjectConstructor( Coproduct_1, list_of_pairs_of_object_and_index_1 \
);
end
## start of resolving phase

######## Start compilation of
# Function added to ⊕ ( CategoryOfRows( Q ), 5 ) for ObjectConstructor
function ( Coproduct, pairs )
    #% CAP_JIT_DROP_NEXT_STATEMENT
    Assert( 0, ForAll( pairs, function ( pair )
            return 1 <= pair[2] and pair[2] <= NrOfSummandsOfCoproduct( Coprodu\
ct );
        end ) );
    #% CAP_JIT_DROP_NEXT_STATEMENT
    Assert( 0, ForAll( [ 1 .. Length( pairs ) - 1 ], function ( i )
            return pairs[i][2] < pairs[i + 1][2];
        end ) );
    return CreateCapCategoryObjectWithAttributes( Coproduct, ListOfPairsOfObjec\
tAndIndex, pairs );
end

#### Continue compilation of
# Function added to ⊕ ( CategoryOfRows( Q ), 5 ) for ObjectConstructor
# current state:
function ( Coproduct_1, pairs_1 )
    return CreateCapCategoryObjectWithAttributes( CAP_JIT_INTERNAL_GLOBAL_VARIA\
BLE_2, ListOfPairsOfObjectAndIndex, pairs_1 );
end
## start of resolving phase

#### Continue compilation of
# Function added to ⊕ ( CategoryOfRows( Q ), 5 ) for ObjectConstructor
# finished resolving phase, current state:
function ( Coproduct_1, pairs_1 )
    return CreateCapCategoryObjectWithAttributes( CAP_JIT_INTERNAL_GLOBAL_VARIA\
BLE_2, ListOfPairsOfObjectAndIndex, pairs_1 );
end
## start of rule phase

######## Finished compilation of
# Function added to ⊕ ( CategoryOfRows( Q ), 5 ) for ObjectConstructor
# result:
function ( Coproduct_1, pairs_1 )
    return CreateCapCategoryObjectWithAttributes( CAP_JIT_INTERNAL_GLOBAL_VARIA\
BLE_2, ListOfPairsOfObjectAndIndex, pairs_1 );
end

######## Start compilation of
# CategoryOfRowsObjectOp method
function ( category, rank )
    if not IsInt( rank ) or rank < 0 then
        Error( "the object datum must be a non-negative integer" );
    fi;
    return CreateCapCategoryObjectWithAttributes( category, RankOfObject, rank \
);
end

#### Continue compilation of
# CategoryOfRowsObjectOp method
# current state:
function ( category_1, rank_1 )
    return CreateCapCategoryObjectWithAttributes( CAP_JIT_INTERNAL_GLOBAL_VARIA\
BLE_3, RankOfObject, rank_1 );
end
## start of resolving phase

#### Continue compilation of
# CategoryOfRowsObjectOp method
# finished resolving phase, current state:
function ( category_1, rank_1 )
    return CreateCapCategoryObjectWithAttributes( CAP_JIT_INTERNAL_GLOBAL_VARIA\
BLE_3, RankOfObject, rank_1 );
end
## start of rule phase

######## Finished compilation of
# CategoryOfRowsObjectOp method
# result:
function ( category_1, rank_1 )
    return CreateCapCategoryObjectWithAttributes( CAP_JIT_INTERNAL_GLOBAL_VARIA\
BLE_3, RankOfObject, rank_1 );
end

#### Continue compilation of
# ModelingTowerObjectConstructor method
# finished resolving phase, current state:
function ( SGReps_1, list_of_pairs_of_rank_and_index_1 )
    local list_of_pairs_of_object_and_index_1;
    list_of_pairs_of_object_and_index_1 := List( list_of_pairs_of_rank_and_inde\
x_1, function ( pair_2 )
            return function (  )
                    local first_3, second_3;
                    second_3 := pair_2[2];
                    first_3 := function (  )
                            local rank_4;
                            rank_4 := pair_2[1];
                            return CreateCapCategoryObjectWithAttributes( CAP_J\
IT_INTERNAL_GLOBAL_VARIABLE_3, RankOfObject, rank_4 );
                        end(  );
                    return NTuple( 2, first_3, second_3 );
                end(  );
        end );
    return function (  )
            return CreateCapCategoryObjectWithAttributes( CAP_JIT_INTERNAL_GLOB\
AL_VARIABLE_2, ListOfPairsOfObjectAndIndex, list_of_pairs_of_object_and_index_1\
 );
        end(  );
end
## start of rule phase

######## Finished compilation of
# ModelingTowerObjectConstructor method
# result:
function ( SGReps_1, list_of_pairs_of_rank_and_index_1 )
    local list_of_pairs_of_object_and_index_1;
    list_of_pairs_of_object_and_index_1 := List( list_of_pairs_of_rank_and_inde\
x_1, function ( pair_2 )
            local inline_81_second_2, inline_81_inline_85_RETURN_VALUE_2, inlin\
e_81_inline_85_rank_2;
            inline_81_inline_85_rank_2 := pair_2[1];
            inline_81_inline_85_RETURN_VALUE_2 := CreateCapCategoryObjectWithAt\
tributes( CAP_JIT_INTERNAL_GLOBAL_VARIABLE_3, RankOfObject, inline_81_inline_85\
_rank_2 );
            inline_81_second_2 := pair_2[2];
            return NTuple( 2, inline_81_inline_85_RETURN_VALUE_2, inline_81_sec\
ond_2 );
        end );
    return CreateCapCategoryObjectWithAttributes( CAP_JIT_INTERNAL_GLOBAL_VARIA\
BLE_2, ListOfPairsOfObjectAndIndex, list_of_pairs_of_object_and_index_1 );
end

#### Continue compilation of
# ModelingObject method
# finished resolving phase, current state:
function ( cat_1, obj_1 )
    return function (  )
            local list_of_pairs_of_rank_and_index_2, list_of_pairs_of_object_an\
d_index_2;
            list_of_pairs_of_rank_and_index_2 := function (  )
                    return ListOfPairsOfRankAndIndex( obj_1 );
                end(  );
            list_of_pairs_of_object_and_index_2 := List( list_of_pairs_of_rank_\
and_index_2, function ( pair_3 )
                    local inline_81_second_3, inline_81_inline_85_RETURN_VALUE_\
3, inline_81_inline_85_rank_3;
                    inline_81_inline_85_rank_3 := pair_3[1];
                    inline_81_inline_85_RETURN_VALUE_3 := CreateCapCategoryObje\
ctWithAttributes( CAP_JIT_INTERNAL_GLOBAL_VARIABLE_3, RankOfObject, inline_81_i\
nline_85_rank_3 );
                    inline_81_second_3 := pair_3[2];
                    return NTuple( 2, inline_81_inline_85_RETURN_VALUE_3, inlin\
e_81_second_3 );
                end );
            return CreateCapCategoryObjectWithAttributes( CAP_JIT_INTERNAL_GLOB\
AL_VARIABLE_2, ListOfPairsOfObjectAndIndex, list_of_pairs_of_object_and_index_2\
 );
        end(  );
end
## start of rule phase

######## Finished compilation of
# ModelingObject method
# result:
function ( cat_1, obj_1 )
    local inline_86_list_of_pairs_of_object_and_index_1;
    inline_86_list_of_pairs_of_object_and_index_1 := List( ListOfPairsOfRankAnd\
Index( obj_1 ), function ( pair_2 )
            local inline_81_second_2, inline_81_inline_85_RETURN_VALUE_2, inlin\
e_81_inline_85_rank_2;
            inline_81_inline_85_rank_2 := pair_2[1];
            inline_81_inline_85_RETURN_VALUE_2 := CreateCapCategoryObjectWithAt\
tributes( CAP_JIT_INTERNAL_GLOBAL_VARIABLE_3, RankOfObject, inline_81_inline_85\
_rank_2 );
            inline_81_second_2 := pair_2[2];
            return NTuple( 2, inline_81_inline_85_RETURN_VALUE_2, inline_81_sec\
ond_2 );
        end );
    return CreateCapCategoryObjectWithAttributes( CAP_JIT_INTERNAL_GLOBAL_VARIA\
BLE_2, ListOfPairsOfObjectAndIndex, inline_86_list_of_pairs_of_object_and_index\
_1 );
end

######## Start compilation of
# Function added to ⊕ ( CategoryOfRows( Q ), 5 ) for IsEqualForObjects
function ( Coproduct, object_1, object_2 )
    local Rows, pairs_1, pairs_2;
    Rows := UnderlyingCategoryOfRows( Coproduct );
    pairs_1 := ListOfPairsOfObjectAndIndex( object_1 );
    pairs_2 := ListOfPairsOfObjectAndIndex( object_2 );
    if Length( pairs_1 ) <> Length( pairs_2 ) then
        return false;
    else
        return ForAll( [ 1 .. Length( pairs_1 ) ], function ( i )
                return pairs_1[i][2] = pairs_2[i][2] and IsEqualForObjects( Row\
s, pairs_1[i][1], pairs_2[i][1] );
            end );
    fi;
    return;
end

#### Continue compilation of
# Function added to ⊕ ( CategoryOfRows( Q ), 5 ) for IsEqualForObjects
# current state:
function ( Coproduct_1, object_1_1, object_2_1 )
    local Rows_1, pairs_1_1, pairs_2_1;
    pairs_2_1 := ListOfPairsOfObjectAndIndex( object_2_1 );
    pairs_1_1 := ListOfPairsOfObjectAndIndex( object_1_1 );
    if Length( pairs_1_1 ) <> Length( pairs_2_1 ) then
        return false;
    else
        Rows_1 := UnderlyingCategoryOfRows( CAP_JIT_INTERNAL_GLOBAL_VARIABLE_2 \
);
        return ForAll( [ 1 .. Length( pairs_1_1 ) ], function ( i_2 )
                return pairs_1_1[i_2][2] = pairs_2_1[i_2][2] and IsEqualForObje\
cts( Rows_1, pairs_1_1[i_2][1], pairs_2_1[i_2][1] );
            end );
    fi;
    return;
end
## start of resolving phase

######## Start compilation of
# Function added to Rows( Q ) for IsEqualForObjects
function ( cat, object_1, object_2 )
    return RankOfObject( object_1 ) = RankOfObject( object_2 );
end

#### Continue compilation of
# Function added to Rows( Q ) for IsEqualForObjects
# current state:
function ( cat_1, object_1_1, object_2_1 )
    return RankOfObject( object_1_1 ) = RankOfObject( object_2_1 );
end
## start of resolving phase

#### Continue compilation of
# Function added to Rows( Q ) for IsEqualForObjects
# finished resolving phase, current state:
function ( cat_1, object_1_1, object_2_1 )
    return RankOfObject( object_1_1 ) = RankOfObject( object_2_1 );
end
## start of rule phase

######## Finished compilation of
# Function added to Rows( Q ) for IsEqualForObjects
# result:
function ( cat_1, object_1_1, object_2_1 )
    return RankOfObject( object_1_1 ) = RankOfObject( object_2_1 );
end

#### Continue compilation of
# Function added to ⊕ ( CategoryOfRows( Q ), 5 ) for IsEqualForObjects
# finished resolving phase, current state:
function ( Coproduct_1, object_1_1, object_2_1 )
    local pairs_1_1, pairs_2_1;
    pairs_2_1 := ListOfPairsOfObjectAndIndex( object_2_1 );
    pairs_1_1 := ListOfPairsOfObjectAndIndex( object_1_1 );
    if Length( pairs_1_1 ) <> Length( pairs_2_1 ) then
        return false;
    else
        return ForAll( [ 1 .. Length( pairs_1_1 ) ], function ( i_2 )
                return pairs_1_1[i_2][2] = pairs_2_1[i_2][2] and function (  )
                          local object_1_3, object_2_3;
                          object_2_3 := pairs_2_1[i_2][1];
                          object_1_3 := pairs_1_1[i_2][1];
                          return RankOfObject( object_1_3 ) = RankOfObject( obj\
ect_2_3 );
                      end(  );
            end );
    fi;
    return;
end
## start of rule phase

######## Finished compilation of
# Function added to ⊕ ( CategoryOfRows( Q ), 5 ) for IsEqualForObjects
# result:
function ( Coproduct_1, object_1_1, object_2_1 )
    if Length( ListOfPairsOfObjectAndIndex( object_1_1 ) ) <> Length( ListOfPai\
rsOfObjectAndIndex( object_2_1 ) ) then
        return false;
    else
        return ForAll( [ 1 .. Length( ListOfPairsOfObjectAndIndex( object_1_1 )\
 ) ], function ( i_2 )
                return ListOfPairsOfObjectAndIndex( object_1_1 )[i_2][2] = List\
OfPairsOfObjectAndIndex( object_2_1 )[i_2][2] and RankOfObject( ListOfPairsOfOb\
jectAndIndex( object_1_1 )[i_2][1] ) = RankOfObject( ListOfPairsOfObjectAndInde\
x( object_2_1 )[i_2][1] );
            end );
    fi;
    return;
end

#### Continue compilation of
# Function added to SkeletalGroupRepresentations( SymmetricGroup( [ 1 .. 4 ] ),\
 Q ) for IsEqualForObjects
# finished resolving phase, current state:
function ( cat_1, arg2_1, arg3_1 )
    return function (  )
            local object_1_2, object_2_2;
            object_2_2 := function (  )
                    local inline_86_list_of_pairs_of_object_and_index_3;
                    inline_86_list_of_pairs_of_object_and_index_3 := List( List\
OfPairsOfRankAndIndex( arg3_1 ), function ( pair_4 )
                            local inline_81_second_4, inline_81_inline_85_RETUR\
N_VALUE_4, inline_81_inline_85_rank_4;
                            inline_81_inline_85_rank_4 := pair_4[1];
                            inline_81_inline_85_RETURN_VALUE_4 := CreateCapCate\
goryObjectWithAttributes( CAP_JIT_INTERNAL_GLOBAL_VARIABLE_3, RankOfObject, inl\
ine_81_inline_85_rank_4 );
                            inline_81_second_4 := pair_4[2];
                            return NTuple( 2, inline_81_inline_85_RETURN_VALUE_\
4, inline_81_second_4 );
                        end );
                    return CreateCapCategoryObjectWithAttributes( CAP_JIT_INTER\
NAL_GLOBAL_VARIABLE_2, ListOfPairsOfObjectAndIndex, inline_86_list_of_pairs_of_\
object_and_index_3 );
                end(  );
            object_1_2 := function (  )
                    local inline_86_list_of_pairs_of_object_and_index_3;
                    inline_86_list_of_pairs_of_object_and_index_3 := List( List\
OfPairsOfRankAndIndex( arg2_1 ), function ( pair_4 )
                            local inline_81_second_4, inline_81_inline_85_RETUR\
N_VALUE_4, inline_81_inline_85_rank_4;
                            inline_81_inline_85_rank_4 := pair_4[1];
                            inline_81_inline_85_RETURN_VALUE_4 := CreateCapCate\
goryObjectWithAttributes( CAP_JIT_INTERNAL_GLOBAL_VARIABLE_3, RankOfObject, inl\
ine_81_inline_85_rank_4 );
                            inline_81_second_4 := pair_4[2];
                            return NTuple( 2, inline_81_inline_85_RETURN_VALUE_\
4, inline_81_second_4 );
                        end );
                    return CreateCapCategoryObjectWithAttributes( CAP_JIT_INTER\
NAL_GLOBAL_VARIABLE_2, ListOfPairsOfObjectAndIndex, inline_86_list_of_pairs_of_\
object_and_index_3 );
                end(  );
            if Length( ListOfPairsOfObjectAndIndex( object_1_2 ) ) <> Length( L\
istOfPairsOfObjectAndIndex( object_2_2 ) ) then
                return false;
            else
                return ForAll( [ 1 .. Length( ListOfPairsOfObjectAndIndex( obje\
ct_1_2 ) ) ], function ( i_3 )
                        return ListOfPairsOfObjectAndIndex( object_1_2 )[i_3][2\
] = ListOfPairsOfObjectAndIndex( object_2_2 )[i_3][2] and RankOfObject( ListOfP\
airsOfObjectAndIndex( object_1_2 )[i_3][1] ) = RankOfObject( ListOfPairsOfObjec\
tAndIndex( object_2_2 )[i_3][1] );
                    end );
            fi;
            return;
        end(  );
end
## start of rule phase

######## Finished compilation of
# Function added to SkeletalGroupRepresentations( SymmetricGroup( [ 1 .. 4 ] ),\
 Q ) for IsEqualForObjects
# result:
function ( cat_1, arg2_1, arg3_1 )
    if Length( ListOfPairsOfRankAndIndex( arg2_1 ) ) <> Length( ListOfPairsOfRa\
nkAndIndex( arg3_1 ) ) then
        return false;
    else
        return ForAll( [ 1 .. Length( ListOfPairsOfRankAndIndex( arg2_1 ) ) ], \
function ( i_2 )
                return List( ListOfPairsOfRankAndIndex( arg2_1 ), function ( pa\
ir_3 )
                                local inline_81_second_3, inline_81_inline_85_R\
ETURN_VALUE_3, inline_81_inline_85_rank_3;
                                inline_81_inline_85_rank_3 := pair_3[1];
                                inline_81_inline_85_RETURN_VALUE_3 := CreateCap\
CategoryObjectWithAttributes( CAP_JIT_INTERNAL_GLOBAL_VARIABLE_3, RankOfObject,\
 inline_81_inline_85_rank_3 );
                                inline_81_second_3 := pair_3[2];
                                return NTuple( 2, inline_81_inline_85_RETURN_VA\
LUE_3, inline_81_second_3 );
                            end )[i_2][2] = List( ListOfPairsOfRankAndIndex( ar\
g3_1 ), function ( pair_3 )
                                local inline_81_second_3, inline_81_inline_85_R\
ETURN_VALUE_3, inline_81_inline_85_rank_3;
                                inline_81_inline_85_rank_3 := pair_3[1];
                                inline_81_inline_85_RETURN_VALUE_3 := CreateCap\
CategoryObjectWithAttributes( CAP_JIT_INTERNAL_GLOBAL_VARIABLE_3, RankOfObject,\
 inline_81_inline_85_rank_3 );
                                inline_81_second_3 := pair_3[2];
                                return NTuple( 2, inline_81_inline_85_RETURN_VA\
LUE_3, inline_81_second_3 );
                            end )[i_2][2] and RankOfObject( List( ListOfPairsOf\
RankAndIndex( arg2_1 ), function ( pair_3 )
                                  local inline_81_second_3, inline_81_inline_85\
_RETURN_VALUE_3, inline_81_inline_85_rank_3;
                                  inline_81_inline_85_rank_3 := pair_3[1];
                                  inline_81_inline_85_RETURN_VALUE_3 := CreateC\
apCategoryObjectWithAttributes( CAP_JIT_INTERNAL_GLOBAL_VARIABLE_3, RankOfObjec\
t, inline_81_inline_85_rank_3 );
                                  inline_81_second_3 := pair_3[2];
                                  return NTuple( 2, inline_81_inline_85_RETURN_\
VALUE_3, inline_81_second_3 );
                              end )[i_2][1] ) = RankOfObject( List( ListOfPairs\
OfRankAndIndex( arg3_1 ), function ( pair_3 )
                                  local inline_81_second_3, inline_81_inline_85\
_RETURN_VALUE_3, inline_81_inline_85_rank_3;
                                  inline_81_inline_85_rank_3 := pair_3[1];
                                  inline_81_inline_85_RETURN_VALUE_3 := CreateC\
apCategoryObjectWithAttributes( CAP_JIT_INTERNAL_GLOBAL_VARIABLE_3, RankOfObjec\
t, inline_81_inline_85_rank_3 );
                                  inline_81_second_3 := pair_3[2];
                                  return NTuple( 2, inline_81_inline_85_RETURN_\
VALUE_3, inline_81_second_3 );
                              end )[i_2][1] );
            end );
    fi;
    return;
end

######## Start post-processing of
# Function added to SkeletalGroupRepresentations( SymmetricGroup( [ 1 .. 4 ] ),\
 Q ) for IsEqualForObjects (compiled)

######## Finished post-processing of
# Function added to SkeletalGroupRepresentations( SymmetricGroup( [ 1 .. 4 ] ),\
 Q ) for IsEqualForObjects (compiled)
# result:
function ( cat_1, arg2_1, arg3_1 )
    local deduped_1_1, hoisted_2_1, hoisted_3_1, deduped_4_1, deduped_5_1, dedu\
ped_6_1;
    deduped_6_1 := ListOfPairsOfRankAndIndex( arg3_1 );
    deduped_5_1 := ListOfPairsOfRankAndIndex( arg2_1 );
    deduped_4_1 := Length( deduped_5_1 );
    if deduped_4_1 <> Length( deduped_6_1 ) then
        return false;
    else
        deduped_1_1 := UnderlyingCategoryOfRows( ModelingCategory( cat_1 ) );
        hoisted_3_1 := List( deduped_6_1, function ( pair_2 )
                return NTuple( 2, CreateCapCategoryObjectWithAttributes( dedupe\
d_1_1, RankOfObject, pair_2[1] ), pair_2[2] );
            end );
        hoisted_2_1 := List( deduped_5_1, function ( pair_2 )
                return NTuple( 2, CreateCapCategoryObjectWithAttributes( dedupe\
d_1_1, RankOfObject, pair_2[1] ), pair_2[2] );
            end );
        return ForAll( [ 1 .. deduped_4_1 ], function ( i_2 )
                local deduped_1_2, deduped_2_2;
                deduped_2_2 := hoisted_3_1[i_2];
                deduped_1_2 := hoisted_2_1[i_2];
                return deduped_1_2[2] = deduped_2_2[2] and RankOfObject( dedupe\
d_1_2[1] ) = RankOfObject( deduped_2_2[1] );
            end );
    fi;
    return;
end

######## Start post-processing of
# Function added to SkeletalGroupRepresentations( SymmetricGroup( [ 1 .. 4 ] ),\
 Q ) for IsEqualForObjects (compiled)

######## Finished post-processing of
# Function added to SkeletalGroupRepresentations( SymmetricGroup( [ 1 .. 4 ] ),\
 Q ) for IsEqualForObjects (compiled)
# result:
function ( cat_1, arg2_1, arg3_1 )
    local deduped_2_1, hoisted_3_1, deduped_4_1, deduped_5_1, deduped_6_1;
    deduped_6_1 := ListOfPairsOfRankAndIndex( arg3_1 );
    deduped_5_1 := ListOfPairsOfRankAndIndex( arg2_1 );
    deduped_4_1 := Length( deduped_5_1 );
    if deduped_4_1 <> Length( deduped_6_1 ) then
        return false;
    else
        deduped_2_1 := UnderlyingCategoryOfRows( ModelingCategory( cat_1 ) );
        hoisted_3_1 := List( deduped_6_1, function ( pair_2 )
                return NTuple( 2, CreateCapCategoryObjectWithAttributes( dedupe\
d_2_1, RankOfObject, pair_2[1] ), pair_2[2] );
            end );
        return ForAll( [ 1 .. deduped_4_1 ], function ( i_2 )
                local deduped_1_2, deduped_2_2, deduped_3_2;
                deduped_3_2 := hoisted_3_1[i_2];
                deduped_2_2 := CAP_JIT_INCOMPLETE_LOGIC( deduped_5_1[i_2] );
                deduped_1_2 := CAP_JIT_INCOMPLETE_LOGIC( NTuple( 2, CreateCapCa\
tegoryObjectWithAttributes( deduped_2_1, RankOfObject, deduped_2_2[1] ), dedupe\
d_2_2[2] ) );
                return deduped_1_2[2] = deduped_3_2[2] and RankOfObject( dedupe\
d_1_2[1] ) = RankOfObject( deduped_3_2[1] );
            end );
    fi;
    return;
end
