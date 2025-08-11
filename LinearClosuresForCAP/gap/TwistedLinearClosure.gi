# SPDX-License-Identifier: GPL-2.0-or-later
# LinearClosuresForCAP: Linear closures
#
# Implementations
#

####################################
##
## Constructors
##
####################################

##
InstallGlobalFunction( TWISTED_LINEAR_CLOSURE_CONSTRUCTOR_USING_CategoryOfRows,
                       
  FunctionWithNamedArguments(
  [
    [ "FinalizeCategory", true ],
  ],
  function( CAP_NAMED_ARGUMENTS, rows, underlying_category, cocycle, arg... ) ## rows = CategoryOfRows( ... )
    local ring, name, category, is_finite, sorting_function, with_nf;
    
    ring := UnderlyingRing( rows );
    
    Assert( 0, HasIsCommutative( ring ) and IsCommutative( ring ) );
    
    name := Concatenation( "TwistedLinearClosure( ", Name( underlying_category )," )" );
    
    category := CreateCapCategory( name,
                    IsTwistedLinearClosure,
                    IsObjectInTwistedLinearClosure,
                    IsMorphismInTwistedLinearClosure,
                    IsCapCategoryTwoCell
                    : overhead := false );
    
    category!.compiler_hints := rec(
        category_attribute_names := [
            "UnderlyingCategory",
            "CommutativeRingOfLinearCategory",
            "Cocycle",
        ],
    );
    
    with_nf := false;
    
    if Length( arg ) = 1 then
        
        with_nf := arg[1];
        
        sorting_function := fail;
        
    elif Length( arg ) = 2 then
        
        with_nf := arg[1];
        
        sorting_function := arg[2];
        
        category!.sorting_function := sorting_function;
        
    fi;
    
    category!.with_nf := with_nf;
    
    SetCocycle( category, cocycle );
    
    SET_COMMON_ATTRIBUTES_FOR_LINEAR_CLOSURE( category, underlying_category, ring );
    
    if with_nf and
       HasIsEquippedWithHomomorphismStructure( underlying_category ) and
       IsEquippedWithHomomorphismStructure( underlying_category )
       #= comment for Julia
       and IsPackageMarkedForLoading( "FinSetsForCAP", ">= 2023.07-03" )
       # =#
    then
        
        SET_HOMOMORPHISM_STRUCTURE_ATTRIBUTES_FOR_LINEAR_CLOSURE( category, rows );
        
    fi;
    
    INSTALL_FUNCTIONS_FOR_LINEAR_CLOSURE( rows, category );
    
    ##
    AddPreCompose( category,
      function( cat, alpha, beta )
        local coeffs_alpha, coeffs_beta, supp_alpha, supp_beta, coeffs, supp, a, b, gamma, coeff;
        
        coeffs_alpha := CoefficientsList( alpha );
        
        coeffs_beta := CoefficientsList( beta );
        
        supp_alpha := SupportMorphisms( alpha );
        
        supp_beta := SupportMorphisms( beta );
        
        coeffs := [];
        
        supp := [];
        
        for a in [ 1 .. Length( coeffs_alpha ) ] do
            
            for b in [ 1 .. Length( coeffs_beta ) ] do
                
                gamma := PreCompose( supp_alpha[a], supp_beta[b] );
                
                coeff := ( coeffs_alpha[a] * coeffs_beta[b] ) * cocycle( supp_alpha[a], supp_beta[b], gamma );
                
                Add( supp, gamma );
                
                Add( coeffs, coeff );
                
            od;
            
        od;
        
        return MorphismConstructor( cat, Source( alpha ), Pair( coeffs, supp ), Range( beta ) );
        
    end );
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        
        Finalize( category );
        
    fi;
    
    return category;
    
end ) );

##
InstallGlobalFunction( TWISTED_LINEAR_CLOSURE_CONSTRUCTOR,
  function( ring, underlying_category, cocycle, arg... )
    local rows;
    
    rows := CategoryOfRows( ring : FinalizeCategory := true
            #= comment for Julia
            , overhead := false
            # =#
            );
    
    return CallFuncList( TWISTED_LINEAR_CLOSURE_CONSTRUCTOR_USING_CategoryOfRows,
                   Concatenation( [ rows, underlying_category, cocycle ], arg ) );
    
end );
##
InstallMethod( TwistedLinearClosure,
               [ IsCategoryOfRows, IsCapCategory, IsFunction ],
  function( rows, underlying_category, cocycle )
    
    return TWISTED_LINEAR_CLOSURE_CONSTRUCTOR_USING_CategoryOfRows( rows, underlying_category, cocycle, false );
    
end );

## sorting_function:
## compares two morphisms alpha: a -> b, beta: a -> b
## such that, if we take the quotient by IsCongruentForMorphisms, we get a total ordering on morphisms
InstallMethod( TwistedLinearClosure,
               [ IsCategoryOfRows, IsCapCategory, IsFunction, IsFunction ],
  function( rows, underlying_category, cocycle, sorting_function )
    
    return TWISTED_LINEAR_CLOSURE_CONSTRUCTOR_USING_CategoryOfRows( rows, underlying_category, cocycle, true, sorting_function );
    
end );

##
InstallMethod( TwistedLinearClosure,
               [ IsHomalgRing, IsCapCategory, IsFunction ],
  function( ring, underlying_category, cocycle )
    
    return TWISTED_LINEAR_CLOSURE_CONSTRUCTOR( ring, underlying_category, cocycle, false );
    
end );

##
InstallMethod( TwistedLinearClosure,
               [ IsHomalgRing, IsCapCategory, IsFunction, IsFunction ],
  function( ring, underlying_category, cocycle, sorting_function )
    
    return TWISTED_LINEAR_CLOSURE_CONSTRUCTOR( ring, underlying_category, cocycle, true, sorting_function );
    
end );

