# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Implementations
#
BindGlobal( "ADD_FUNCTIONS_FOR_SkeletalCategoryOfGroupRepresentations_A4_Q_precompiled", function ( cat )
    
    ##
    AddTensorUnit( cat,
        
########
function ( cat_1 )
    return CreateCapCategoryObjectWithAttributes( cat_1, TripleOfNrSupportListOfSupportListOfRanks, NTuple( 3, 1, [ IndexOfTrivialCharacter( cat_1 ) ], [ 1 ] ) );
end
########
        
    , 100 );
    
    if IsBound( cat!.precompiled_functions_added ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "precompiled functions have already been added before" );
        
    fi;
    
    cat!.precompiled_functions_added := true;
    
end );

BindGlobal( "SkeletalCategoryOfGroupRepresentations_A4_Q_precompiled", function ( group, homalg_field )
  local category_constructor, cat;
    
    category_constructor :=
        
        
        function ( group, homalg_field )
    return SkeletalCategoryOfGroupRepresentations( group, homalg_field : no_precompiled_code := true );
end;
        
        
    
    cat := category_constructor( group, homalg_field : FinalizeCategory := false, no_precompiled_code := true );
    
    ADD_FUNCTIONS_FOR_SkeletalCategoryOfGroupRepresentations_A4_Q_precompiled( cat );
    
    Finalize( cat );
    
    return cat;
    
end );
