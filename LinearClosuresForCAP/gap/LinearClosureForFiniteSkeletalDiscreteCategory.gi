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
                             IsObjectInLinearClosure,
                             IsMorphismInLinearClosure,
                             IsCapCategoryTwoCell
                             : overhead := false );
    
    LC!.compiler_hints := rec(
        category_attribute_names := [
            "UnderlyingCategory",
            "CommutativeRingOfLinearCategory", ], );
    
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
      function( LC, source, pair, target )
        
        return CreateCapCategoryMorphismWithAttributes( LC,
                                                        source,
                                                        target,
                                                        CoefficientsList, pair[1],
                                                        SupportMorphisms, pair[2] );
        
    end );
    
    ##
    AddMorphismDatum( LC,
      function( LC, morphism )
        
        return Pair( SupportMorphisms( morphism ), CoefficientsList( morphism ) );
        
    end );
    
    ##
    AddIsEqualForObjects( LC,
      function( LC, obj_1, obj_2 )
        
        return IsEqualForObjects( UnderlyingCategory( LC ), UnderlyingOriginalObject( obj_1 ), UnderlyingOriginalObject( obj_2 ) );
        
    end );
    
    compare_function :=
      function( LC, alpha, beta )
        local DC;
        
        DC := UnderlyingCategory( LC );
        
        return CoefficientsList( alpha ) = CoefficientsList( beta ) and
               SupportMorphisms( alpha ) = SupportMorphisms( beta );
        
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
    
    #
    AddIsWellDefinedForMorphisms( LC,
      function( LC, alpha )
        local coefficient, support, element_filter;
        
        coefficient := CoefficientsList( alpha );
        
        support := SupportMorphisms( alpha );
        
        element_filter := RingElementFilter( CommutativeRingOfLinearCategory( LC ) );
        
        if not IsList( coefficient ) then
            
            return false;
            
        elif not IsList( support ) then
            
            return false;
            
        elif 1 < Length( coefficient ) then
            
            return false;
            
        elif 1 < Length( support ) then
            
            return false;
            
        elif not IsEmpty( coefficient ) and not element_filter( coefficient[1] ) then
            
            return false;
            
        elif not IsEmpty( support ) and not IsMorphismInFiniteSkeletalDiscreteCategory( support[1] ) then
            
            return false;
            
        else
            
            return true;
            
        fi;
        
    end );
    
    ##
    AddPreCompose( LC,
      function( LC, alpha, beta )
        local DC, ring, source, target, coefficient_alpha, coefficient_beta, coefficient, support_morphism, coefficient_list;
        
        DC := UnderlyingCategory( LC );
        
        ring := CommutativeRingOfLinearCategory( LC );
        
        source := Source( alpha );
        target := Target( beta );
        
        # If CoefficientsList( alpha ) is empty, the following returns 0.
        # Otherwise returns the integer inside the coefficient list.
        coefficient_alpha := Sum( CoefficientsList( alpha ) );
        
        coefficient_beta := Sum( CoefficientsList( beta ) );
        
        coefficient := coefficient_alpha * coefficient_beta;
        
        support_morphism := Concatenation( SupportMorphisms( alpha ), SupportMorphisms( beta ) );
        
        # If coefficient is 0, then the following becomes support_morphism := [], as required for a zero morphism.
        # Otherwise it turns into support_morphism := [ support_morphism[1] ].
        # Note: here we don't need to call a PreCompose in the underlying category.
        support_morphism := support_morphism{[ 1 .. BooleanToInteger( not IsZero( coefficient ) ) ]};
        
        # If coefficient is 0, then the following becomes coefficient = [], as required for a zero morphism.
        # Otherwise it turns into coefficient := [ coefficient ].
        coefficient_list := [ coefficient ]{[ 1 .. BooleanToInteger( not IsZero( coefficient ) ) ]};
        
        return MorphismConstructor( LC, Source( alpha ), Pair( coefficient_list, support_morphism ), Target( alpha ) );
        
    end );
    
    ##
    AddIdentityMorphism( LC,
      function( LC, object )
        local DC, coefficient, support_morphism;
        
        DC := UnderlyingCategory( LC );
        
        coefficient := [ One( ring ) ];
        
        support_morphism := [ IdentityMorphism( DC, UnderlyingOriginalObject( object ) ) ];
        
        # 1·id_object
        return MorphismConstructor( LC, object, Pair( coefficient, support_morphism ), object );
        
    end );
    
    ##
    AddZeroMorphism( LC,
      function( LC, object_1, object_2 )
        
        return MorphismConstructor( LC,
                       object_1,
                       Pair( CapJitTypedExpression( [ ], cat -> CapJitDataTypeOfListOf( CapJitDataTypeOfElementOfRing( CommutativeRingOfLinearCategory( cat ) ) ) ),
                             CapJitTypedExpression( [ ], cat -> CapJitDataTypeOfListOf( CapJitDataTypeOfMorphismOfCategory( UnderlyingCategory( cat ) ) ) ) ),
                       object_2 );
        
    end );
    
    ##
    AddIsZeroForMorphisms( LC,
      function( LC, alpha )
        
        return IsEmpty( CoefficientsList( alpha ) ) and IsEmpty( SupportMorphisms( alpha ) );
        
    end );
    
    ##
    AddAdditionForMorphisms( LC,
      function( LC, alpha, beta )
        local ring, coefficient, support_morphism, coefficient_list;
        
        ring := CommutativeRingOfLinearCategory( LC );
        
        coefficient := Sum( Concatenation( CoefficientsList( alpha ), CoefficientsList( beta ) ), Zero( ring ) );
        
        support_morphism := Concatenation( SupportMorphisms( alpha ), SupportMorphisms( beta ) );
        
        # If coefficient is 0, then the following becomes support_morphism := [], as required for a zero morphism.
        # Otherwise it turns into support_morphism := [ support_morphism[1] ].
        support_morphism := support_morphism{[ 1 .. BooleanToInteger( not IsZero( coefficient ) ) ]};
        
        # If coefficient is 0, then the following becomes coefficient = [], as required for a zero morphism.
        # Otherwise it turns into coefficient := [ coefficient ].
        coefficient_list := [ coefficient ]{[ 1 .. BooleanToInteger( not IsZero( coefficient ) ) ]};
        
        return MorphismConstructor( LC, Source( alpha ), Pair( coefficient_list, support_morphism ), Target( alpha ) );
        
    end );
    
    ##
    AddSumOfMorphisms( LC,
      function( LC, source, morphisms, target )
        local ring, coefficient, support_morphism, coefficient_list;
        
        ring := CommutativeRingOfLinearCategory( LC );
        
        coefficient := Sum( Concatenation( List( morphisms, mor -> CoefficientsList( mor ) ) ), Zero( ring ) );
        
        support_morphism := Concatenation( List( morphisms, mor -> SupportMorphisms( mor ) ) );
        
        # If coefficient is 0, then the following becomes support_morphism := [], as required for a zero morphism.
        # Otherwise it turns into support_morphism := [ support_morphism[1] ].
        support_morphism := support_morphism{[ 1 .. BooleanToInteger( not IsZero( coefficient ) ) ]};
        
        # If coefficient is 0, then the following becomes coefficient = [], as required for a zero morphism.
        # Otherwise it turns into coefficient := [ coefficient ].
        coefficient_list := [ coefficient ]{[ 1 .. BooleanToInteger( not IsZero( coefficient ) ) ]};
        
        return MorphismConstructor( LC, source, Pair( coefficient_list, support_morphism ), target );
        
    end );
    
    ##
    AddAdditiveInverseForMorphisms( LC,
      function( LC, alpha )
        local ring, source, target, coefficient, support_morphism, coefficient_list;
        
        ring := CommutativeRingOfLinearCategory( LC );
        
        source := Source( alpha );
        target := Target( alpha );
        
        # If CoefficientsList( alpha ) is empty, the following returns 0.
        # Otherwise returns the integer inside the coefficient list.
        coefficient := Sum( CoefficientsList( alpha ) );
        
        coefficient := coefficient * MinusOne( CommutativeRingOfLinearCategory( LC ) );
        
        support_morphism := SupportMorphisms( alpha );
        
        # If coefficient is 0, then the following becomes support_morphism := [], as required for a zero morphism.
        # Otherwise it turns into support_morphism := [ support_morphism[1] ].
        support_morphism := support_morphism{[ 1 .. BooleanToInteger( not IsZero( coefficient ) ) ]};
        
        # If coefficient is 0, then the following becomes coefficient = [], as required for a zero morphism.
        # Otherwise it turns into coefficient := [ coefficient ].
        coefficient_list := [ coefficient ]{[ 1 .. BooleanToInteger( not IsZero( coefficient ) ) ]};
        
        return MorphismConstructor( LC, Source( alpha ), Pair( coefficient_list, support_morphism ), Target( alpha ) );
        
    end );
    
    ##
    AddSubtractionForMorphisms( LC,
      function( LC, alpha, beta )
        local ring, coefficient, support_morphism, coefficient_list;
        
        ring := CommutativeRingOfLinearCategory( LC );
        
        # If the difference is empty, the following returns 0.
        # Otherwise returns the integer inside the difference of coefficient lists.
        coefficient := Sum( CoefficientsList( alpha ) - CoefficientsList( beta ) );
        
        support_morphism := Concatenation( SupportMorphisms( alpha ), SupportMorphisms( beta ) );
        
        # If coefficient is 0, then the following becomes support_morphism := [], as required for a zero morphism.
        # Otherwise it turns into support_morphism := [ support_morphism[1] ].
        support_morphism := support_morphism{[ 1 .. BooleanToInteger( not IsZero( coefficient ) ) ]};
        
        # If coefficient is 0, then the following becomes coefficient = [], as required for a zero morphism.
        # Otherwise it turns into coefficient := [ coefficient ].
        coefficient_list := [ coefficient ]{[ 1 .. BooleanToInteger( not IsZero( coefficient ) ) ]};
        
        return MorphismConstructor( LC, Source( alpha ), Pair( coefficient_list, support_morphism ), Target( alpha ) );
        
    end );
    
    ##
    AddMultiplyWithElementOfCommutativeRingForMorphisms( LC,
      function( LC, r, alpha )
        local coefficient, support_morphism, coefficient_list;
        
        coefficient := Sum( CoefficientsList( alpha ) );
        
        coefficient := coefficient * r;
        
        support_morphism := SupportMorphisms( alpha );
        
        # If coefficient is 0, then the following becomes support_morphism := [], as required for a zero morphism.
        # Otherwise it turns into support_morphism := [ support_morphism[1] ].
        support_morphism := support_morphism{[ 1 .. BooleanToInteger( not IsZero( coefficient ) ) ]};
        
        # If coefficient is 0, then the following becomes coefficient = [], as required for a zero morphism.
        # Otherwise it turns into coefficient := [ coefficient ].
        coefficient_list := [ coefficient ]{[ 1 .. BooleanToInteger( not IsZero( coefficient ) ) ]};
        
        return MorphismConstructor( LC, Source( alpha ), Pair( coefficient_list, support_morphism ), Target( alpha ) );
        
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
               [ IsMorphismInLinearClosure ],
    
    function( alpha )
        local DC, coefficient, source, id_source;
        
        if IsZeroForMorphisms( alpha ) then
            
            return "0";
            
        fi;
        
        DC := UnderlyingCategory( CapCategory( alpha ) );
        
        coefficient := CoefficientsList( alpha )[1];
        
        source := Source( alpha );
        
        id_source := IdentityMorphism( DC, UnderlyingOriginalObject( source ) );
        
        return Concatenation( ViewString( coefficient ), "·", ViewString( id_source ) );
        
end );

