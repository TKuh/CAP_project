# SPDX-License-Identifier: GPL-2.0-or-later
# LinearClosuresForCAP: Linear closures
#
# Declarations
#

# Read precompiled categories
ReadPackage( "AdditiveClosuresForCAP", "gap/precompiled_categories/AdditiveClosureOfObjectFiniteCategory_LinearClosure_over_Field_DiscreteCategory_precompiled.gi" );

##
InstallMethod( ADDITIVE_CLOSURE_OF_LINEAR_CLOSURE_OF_FINITE_SKELETAL_DISCRETE_CATEGORY,
               [ IsLinearClosure ],
               
  FunctionWithNamedArguments(
  [
    [ "FinalizeCategory", true ],
  ],
  function( CAP_NAMED_ARGUMENTS, L )
    local homalg_ring, AC_objfin;
    
    homalg_ring := CommutativeRingOfLinearCategory( L );
    
    AC_objfin := AdditiveClosureOfObjectFiniteCategory( L : FinalizeCategory := false );
    
    if ValueOption( "no_precompiled_code" ) <> true then
        
        if HasIsFieldForHomalg( homalg_ring ) and IsFieldForHomalg( homalg_ring ) then
            
            ADD_FUNCTIONS_FOR_AdditiveClosureOfObjectFiniteCategory_LinearClosure_over_Field_DiscreteCategory_precompiled( AC_objfin );
            
        fi;
        
    fi;
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        
        Finalize( AC_objfin );
        
    fi;
    
    return AC_objfin;
    
end ) );

##
InstallMethod( AdditiveClosureDisconnectedOfLinearClosureOfFiniteSkeletalDiscreteCategory,
               [ IsLinearClosure ],
               ADDITIVE_CLOSURE_DISCONNECTED_OF_LINEAR_CLOSURE_OF_FINITE_SKELETAL_DISCRETE_CATEGORY
);

InstallMethod( ADDITIVE_CLOSURE_DISCONNECTED_OF_LINEAR_CLOSURE_OF_FINITE_SKELETAL_DISCRETE_CATEGORY,
               [ IsLinearClosure ],
               
  FunctionWithNamedArguments(
  [
    [ "FinalizeCategory", true ],
  ],
  function( CAP_NAMED_ARGUMENTS, L )
    local PrecompiledAddCl, ACD;
    
    PrecompiledAddCl :=
        ADDITIVE_CLOSURE_OF_LINEAR_CLOSURE_OF_FINITE_SKELETAL_DISCRETE_CATEGORY( L : FinalizeCategory := true );
    
    ACD :=
        AdditiveClosureOfObjectFiniteDisconnectedCategory( L
            : FinalizeCategory := false,
              UsePrecompiledUnderlyingAdditiveClosure := true,
              PrecompiledUnderlyingAdditiveClosure := PrecompiledAddCl );
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        
        Finalize( ACD );
        
    fi;
    
    return ACD;
    
end ) );

