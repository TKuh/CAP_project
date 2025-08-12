# SPDX-License-Identifier: GPL-2.0-or-later
# LinearClosuresForCAP: Linear closures
#
# Declarations
#

#! @Chapter Linear closure of a finite skeletal discrete category

#! @BeginChunk Intro_LinearClosureOfFiniteSkeletalDiscreteCategory
#! 
#! The only morphisms in a skeletal discrete category are the identity morphisms.
#! Hence, for a morphism in the linear closure of such a category,
#! specifying a source, a range and a coefficient is already enough determine
#! determine it uniquely. If the source and range are equal, its underlying
#! support morphism must be an indentity morphism. If they are not equal,
#! then an underlying support morphism does not exists, and the morphism
#! must be a zero morphism (introduced by the transition to the linear closure).

#! This also makes a lazy datastructure superfluous,
#! since there will always only be at most one support morphism, so its
#! coefficient can be computed right away.
#! 
#! @EndChunk

####################################
##
#! @Section GAP Categories
##
####################################

##
DeclareCategory( "IsObjectInLinearClosureOfFiniteSkeletalDiscreteCategory",
                 IsCapCategoryObject );

##
DeclareCategory( "IsMorphismInLinearClosureOfFiniteSkeletalDiscreteCategory",
                 IsCapCategoryMorphism );

####################################
##
#! @Section Constructors
##
####################################

DeclareOperation( "LinearClosure",
                  [ IsCategoryOfRows, IsFiniteSkeletalDiscreteCategory ] );

DeclareOperation( "LinearClosure",
                  [ IsHomalgRing, IsFiniteSkeletalDiscreteCategory ] );

####################################
##
#! @Section Attributes
##
####################################

DeclareAttribute( "UnderlyingOriginalObject",
                   IsObjectInLinearClosureOfFiniteSkeletalDiscreteCategory );

CapJitAddTypeSignature( "UnderlyingOriginalObject", [ IsObjectInLinearClosureOfFiniteSkeletalDiscreteCategory ], function ( input_types )
    
    Assert( 0, IsLinearClosure( input_types[1].category ) );
    
    return CapJitDataTypeOfObjectOfCategory( UnderlyingCategory( input_types[1].category ) );
    
end );

DeclareAttribute( "Coefficient",
                  IsMorphismInLinearClosureOfFiniteSkeletalDiscreteCategory );

CapJitAddTypeSignature( "Coefficient", [ IsMorphismInLinearClosureOfFiniteSkeletalDiscreteCategory ], function ( input_types )
    
    Assert( 0, IsLinearClosure( input_types[1].category ) );
    
    return CapJitDataTypeOfElementOfRing( CommutativeRingOfLinearCategory( input_types[1].category ) );
    
end );

####################################
##
#! @Section Global functions
##
####################################

DeclareGlobalFunction( "LINEAR_CLOSURE_OF_FINITE_SKELETAL_DISCRETE_CATEGORY_CONSTRUCTOR" );

