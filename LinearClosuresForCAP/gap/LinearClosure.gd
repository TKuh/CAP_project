# SPDX-License-Identifier: GPL-2.0-or-later
# LinearClosuresForCAP: Linear closures
#
# Declarations
#
#! @Chapter Linear closure of a category

####################################
##
#! @Section GAP Categories
##
####################################

##
DeclareCategory( "IsLinearClosure",
                 IsCapCategory );

##
DeclareCategory( "IsObjectInLinearClosure",
                 IsCapCategoryObject );

##
DeclareCategory( "IsMorphismInLinearClosure",
                 IsCapCategoryMorphism );

#! @Description
#!  The property of <A>C</A> being a linear closure of a category.
#! @Arguments C
DeclareProperty( "IsLinearClosureOfACategory",
        IsCapCategory );

AddCategoricalProperty( [ "IsLinearClosureOfACategory", "IsLinearClosureOfACategory" ] );

####################################
##
#! @Section Constructors
##
####################################

DeclareOperation( "LinearClosure",
                  [ IsCategoryOfRows, IsCapCategory ] );

DeclareOperation( "LinearClosure",
                  [ IsCategoryOfRows, IsCapCategory, IsFunction ] );

DeclareOperation( "LinearClosure",
                  [ IsHomalgRing, IsCapCategory ] );

DeclareOperation( "LinearClosure",
                  [ IsHomalgRing, IsCapCategory, IsFunction ] );

DeclareOperation( "LinearClosureObject",
                  [ IsCapCategory, IsLinearClosure ] );

DeclareOperation( "LinearClosureObject",
                  [ IsLinearClosure, IsCapCategoryObject ] );

CapJitAddTypeSignature( "LinearClosureObject", [ IsLinearClosure, IsCapCategoryObject ], function ( input_types )
    
    return CapJitDataTypeOfObjectOfCategory( input_types[1].category );
    
end );

DeclareOperation( "LinearClosureMorphism",
                  [ IsLinearClosure, IsObjectInLinearClosure, IsList, IsList, IsObjectInLinearClosure ] );

DeclareOperation( "LinearClosureMorphism",
                  [ IsObjectInLinearClosure, IsList, IsList, IsObjectInLinearClosure ] );

DeclareOperation( "LinearClosureMorphismNC",
                  [ IsObjectInLinearClosure, IsList, IsList, IsObjectInLinearClosure ] );

CapJitAddTypeSignature( "LinearClosureMorphismNC", [ IsLinearClosure, IsObjectInLinearClosure, IsList, IsList, IsObjectInLinearClosure ], function ( input_types )
    
    return CapJitDataTypeOfMorphismOfCategory( input_types[1].category );
    
end );

####################################
##
#! @Section Attributes
##
####################################

DeclareAttribute( "UnderlyingCategory",
                   IsLinearClosure );

CapJitAddTypeSignature( "UnderlyingCategory", [ IsLinearClosure ], function ( input_types )
    
    return CapJitDataTypeOfCategory( UnderlyingCategory( input_types[1].category ) );
    
end );

DeclareAttribute( "UnderlyingRing",
                   IsLinearClosure );

DeclareAttribute( "UnderlyingOriginalObject",
                   IsObjectInLinearClosure );

CapJitAddTypeSignature( "UnderlyingOriginalObject", [ IsObjectInLinearClosure ], function ( input_types )
    
    Assert( 0, IsLinearClosure( input_types[1].category ) );
    
    return CapJitDataTypeOfObjectOfCategory( UnderlyingCategory( input_types[1].category ) );
    
end );

DeclareAttribute( "CoefficientsList",
                  IsMorphismInLinearClosure );

CapJitAddTypeSignature( "CoefficientsList", [ IsMorphismInLinearClosure ], function ( input_types )
    
    Assert( 0, IsLinearClosure( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( CapJitDataTypeOfElementOfRing( CommutativeRingOfLinearCategory( input_types[1].category ) ) );
    
end );

DeclareAttribute( "SupportMorphisms",
                  IsMorphismInLinearClosure );

CapJitAddTypeSignature( "SupportMorphisms", [ IsMorphismInLinearClosure ], function ( input_types )
    
    Assert( 0, IsLinearClosure( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( CapJitDataTypeOfMorphismOfCategory( UnderlyingCategory( input_types[1].category ) ) );
    
end );

####################################
##
#! @Section Functors
##
####################################

#! @Description
#!  The arguments are a functor <A>F</A>$:C\to D$, some linear closure <A>linear_closure</A> of $C$ over some
#!  commutative ring $S$ and a function <A>ring_map</A>; where $D$ is a linear category over some commutative ring $R$.
#!  The <A>ring_map</A> is a function that converts an element $s$ in $S$ to an element in $R$,
#!  such that <A>ring_map</A> defines a ring homomorphism.
#!  The output is the linear extension functor of <A>F</A> from <A>linear_closure</A> to $D$.
#! @Arguments F, linear_closure, ring_map
#! @Returns
DeclareOperation( "ExtendFunctorToLinearClosureOfSource",
      [ IsCapFunctor, IsLinearClosure, IsFunction ] );

#! @Description
#!  The arguments are a functor <A>F</A>$:C\to D$, some linear closure <A>linear_closure</A> of $C$ over some
#!  commutative ring $S$; where $D$ is a linear category over $S$.
#!  The output is the linear extension functor of <A>F</A> from <A>linear_closure</A> to $D$.
#! @Arguments F, linear_closure
#! @Returns
DeclareOperation( "ExtendFunctorToLinearClosureOfSource",
      [ IsCapFunctor, IsLinearClosure ] );

####################################
##
#! @Section Operations
##
####################################

DeclareOperation( "*",
                  [ IsMorphismInLinearClosure, IsMorphismInLinearClosure ] );

DeclareOperation( "/",
                  [ IsCapCategoryMorphism, IsLinearClosure ] );

####################################
##
#! @Section Global functions
##
####################################

DeclareGlobalFunction( "SET_COMMON_ATTRIBUTES_FOR_LINEAR_CLOSURE" );

DeclareGlobalFunction( "LINEAR_CLOSURE_CONSTRUCTOR" );

DeclareGlobalFunction( "LINEAR_CLOSURE_CONSTRUCTOR_USING_CategoryOfRows" );

DeclareGlobalFunction( "LINEAR_CLOSURE_MORPHISM_SIMPLIFY" );

DeclareGlobalFunction( "INSTALL_FUNCTIONS_FOR_LINEAR_CLOSURE" );

