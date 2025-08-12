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
InstallOtherMethod( LinearClosure,
                    [ IsCategoryOfRows, IsFiniteSkeletalDiscreteCategory ],
                    LINEAR_CLOSURE_OF_FINITE_SKELETAL_DISCRETE_CATEGORY_CONSTRUCTOR );

##
InstallOtherMethod( LinearClosure,
                    [ IsHomalgRing, IsFiniteSkeletalDiscreteCategory ],
                    
  function( ring, discrete_category )
    local rows;
    
    rows := CategoryOfRows( ring : FinalizeCategory := true
            #= comment for Julia
            , overhead := false
            # =#
            );
    
    return LINEAR_CLOSURE_OF_FINITE_SKELETAL_DISCRETE_CATEGORY_CONSTRUCTOR( rows, discrete_category );
    
end );

InstallGlobalFunction( LINEAR_CLOSURE_OF_FINITE_SKELETAL_DISCRETE_CATEGORY_CONSTRUCTOR,

  FunctionWithNamedArguments(
  [
    [ "FinalizeCategory", true ],
  ],
  function( CAP_NAMED_ARGUMENTS, rows, discrete_category ) ## rows = CategoryOfRows( ... )
    local ring, name, LC, compare_function;
    
    ring := CommutativeRingOfLinearCategory( rows );
    
    Assert( 0, HasIsCommutative( ring ) and IsCommutative( ring ) );
    
    name := Concatenation( "LinearClosure( ", Name( discrete_category )," )" );
    
    LC := CreateCapCategory( name,
                             IsLinearClosure,
                             IsObjectInLinearClosureOfFiniteSkeletalDiscreteCategory,
                             IsMorphismInLinearClosureOfFiniteSkeletalDiscreteCategory,
                             IsCapCategoryTwoCell
                             : overhead := false );
    
    LC!.compiler_hints := rec(
        category_attribute_names := [
            "UnderlyingCategory",
            "CommutativeRingOfLinearCategory",
        ],
    );
    
    SetIsLinearClosureOfACategory( LC, true );
    
    SET_COMMON_ATTRIBUTES_FOR_LINEAR_CLOSURE( LC, discrete_category, ring );
    
    ####################################
    # Primitive operations
    ####################################
    
    ##
    AddObjectConstructor( LC,
      function( LC, underlying_object )
        
        return CreateCapCategoryObjectWithAttributes( LC,
                                                      UnderlyingOriginalObject, underlying_object );
        
    end );
    
    ##
    AddObjectDatum( LC,
      function( LC, object )
        
        return UnderlyingOriginalObject( object );
        
    end );
    
    ##
    AddMorphismConstructor( LC,
      function( LC, source, coefficient, target )
        
        return CreateCapCategoryMorphismWithAttributes( LC,
                                                        source,
                                                        target,
                                                        Coefficient, coefficient );
        
    end );
    
    ##
    AddMorphismDatum( LC,
      function( LC, morphism )
        
        return Coefficient( morphism );
        
    end );
    
    ##
    AddIsEqualForObjects( LC,
      function( LC, obj_1, obj_2 )
        
        return IsEqualForObjects( UnderlyingCategory( LC ),
                                  UnderlyingOriginalObject( obj_1 ),
                                  UnderlyingOriginalObject( obj_2 ) );
        
    end );
    
    compare_function :=
      function( LC, alpha, beta )
        
        return IsEqualForObjects( LC, Source( alpha ), Source( beta ) ) and
               IsEqualForObjects( LC, Target( alpha ), Target( beta ) ) and
               Coefficient( alpha ) = Coefficient( beta );
        
    end;
    
    ##
    AddIsEqualForMorphisms( LC, compare_function );
    
    ##
    AddIsCongruentForMorphisms( LC, compare_function );
    
    ##
    AddIsWellDefinedForObjects( LC,
      function( LC, object )
        
        return IsIdenticalObj( UnderlyingCategory( LC ), CapCategory( UnderlyingOriginalObject( object ) ) );
        
    end );
    
    ##
    AddIsWellDefinedForMorphisms( LC,
      function( LC, alpha )
        local coefficient, element_filter;
        
        coefficient := Coefficient( alpha );
        
        element_filter := RingElementFilter( CommutativeRingOfLinearCategory( LC ) );
        
        if element_filter( coefficient ) then
            
            return true;
            
        fi;
        
        return false;
        
    end );
    
    ##
    AddPreCompose( LC,
      function( LC, alpha, beta )
        local DC, coefficient;
        
        DC := UnderlyingCategory( LC );
        
        coefficient := Coefficient( alpha ) * Coefficient( beta );
        
        return MorphismConstructor( LC, Source( alpha ), coefficient, Target( beta ) );
        
    end );
    
    ##
    AddIdentityMorphism( LC,
      function( LC, object )
        local DC, coefficient;
        
        DC := UnderlyingCategory( LC );
        
        # 1·id_object
        coefficient := One( ring );
        
        return MorphismConstructor( LC, object, coefficient, object );
        
    end );
    
    ##
    AddZeroMorphism( LC,
      function( LC, object_1, object_2 )
        
        return MorphismConstructor( LC,
                    object_1,
                    Zero( CommutativeRingOfLinearCategory( LC ) ),
                    object_2 );
        
    end );
    
    ##
    AddIsZeroForMorphisms( LC,
      function( LC, alpha )
        
        return Coefficient( alpha ) = Zero( CommutativeRingOfLinearCategory( LC ) );
        
    end );
    
    ##
    AddAdditionForMorphisms( LC,
      function( LC, alpha, beta )
        
        return MorphismConstructor( LC,
                                    Source( alpha ),
                                    Coefficient( alpha ) + Coefficient( beta ),
                                    Target( alpha ) );
        
    end );
    
    ##
    AddSumOfMorphisms( LC,
      function( LC, source, morphisms, target )
        local coefficient;
        
        coefficient := List( morphisms, mor -> Coefficient( mor ) );
        
        return MorphismConstructor( LC, source, Sum( coefficient ), target );
        
    end );
    
    ##
    AddAdditiveInverseForMorphisms( LC,
      function( LC, alpha )
        
        return MorphismConstructor( LC,
                    Source( alpha ),
                    Coefficient( alpha ) * MinusOne( CommutativeRingOfLinearCategory( LC ) ),
                    Target( alpha ) );
        
    end );
    
    ##
    AddSubtractionForMorphisms( LC,
      function( LC, alpha, beta )

        return MorphismConstructor( LC,
                                    Source( alpha ),
                                    Coefficient( alpha ) - Coefficient( beta ),
                                    Target( alpha ) );
        
    end );
    
    ##
    AddMultiplyWithElementOfCommutativeRingForMorphisms( LC,
      function( LC, r, alpha )
        
        return MorphismConstructor( LC,
                                    Source( alpha ),
                                    r * Coefficient( alpha ),
                                    Target( alpha ) );
        
    end );
    
    ##
    AddSetOfObjectsOfCategory( LC,
      function( LC )
        
        return List( SetOfObjectsOfCategory( UnderlyingCategory( LC ) ), obj -> ObjectConstructor( LC, obj ) );
        
    end );
    
    if CAP_NAMED_ARGUMENTS.FinalizeCategory then
        
        Finalize( LC );
        
    fi;
    
    return LC;
    
end ) );

####################################
##
## Convenience
##
####################################

InstallOtherMethod( \/,
               [ IsMorphismInFiniteSkeletalDiscreteCategory, IsLinearClosure ],
               
    function( mor, LC )
        
        return MorphismConstructor( LC,
                                    ObjectConstructor( LC, Source( mor ) ),
                                    Pair( [ One( CommutativeRingOfLinearCategory( LC ) ) ], [ mor ] ),
                                    ObjectConstructor( LC, Target( mor ) ) );
        
end );

####################################
##
## View
##
####################################

##
InstallMethod( ViewString,
               [ IsMorphismInLinearClosureOfFiniteSkeletalDiscreteCategory ],
    
    function( alpha )
        local DC, coefficient, source, id_source;
        
        DC := UnderlyingCategory( CapCategory( alpha ) );
        
        coefficient := Coefficient( alpha );
        
        if coefficient = 0 then
            
            return "0";
            
        fi;
        
        source := Source( alpha );
        
        id_source := IdentityMorphism( DC, UnderlyingOriginalObject( source ) );
        
        return Concatenation( ViewString( coefficient ), "·", ViewString( id_source ) );
        
end );

