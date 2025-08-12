# SPDX-License-Identifier: GPL-2.0-or-later
# LinearClosuresForCAP: Linear closures
#
# Declarations
#
#! @Chapter Twisted linear closure of a category

####################################
##
#! @Section GAP Categories
##
####################################

##
DeclareCategory( "IsTwistedLinearClosure",
                 IsLinearClosure );

##
DeclareCategory( "IsObjectInTwistedLinearClosure",
                 IsObjectInLinearClosure );

##
DeclareCategory( "IsMorphismInTwistedLinearClosure",
                 IsMorphismInLinearClosure );

####################################
##
#! @Section Constructors
##
####################################

DeclareOperation( "TwistedLinearClosure",
                  [ IsCategoryOfRows, IsCapCategory, IsFunction, IsFunction ] );

DeclareOperation( "TwistedLinearClosure",
                  [ IsCategoryOfRows, IsCapCategory, IsFunction ] );

DeclareOperation( "TwistedLinearClosure",
                  [ IsHomalgRing, IsCapCategory, IsFunction, IsFunction ] );

DeclareOperation( "TwistedLinearClosure",
                  [ IsHomalgRing, IsCapCategory, IsFunction ] );

####################################
##
#! @Section Attributes
##
####################################

DeclareAttribute( "UnderlyingCategory",
                   IsTwistedLinearClosure );

DeclareAttribute( "UnderlyingRing",
                   IsTwistedLinearClosure );

DeclareAttribute( "Cocycle",
                   IsTwistedLinearClosure );

DeclareAttribute( "UnderlyingOriginalObject",
                   IsObjectInTwistedLinearClosure );

DeclareAttribute( "CoefficientsList",
                  IsMorphismInTwistedLinearClosure );

DeclareAttribute( "SupportMorphisms",
                  IsMorphismInTwistedLinearClosure );

####################################
##
#! @Section Operations
##
####################################

DeclareOperation( "*",
                  [ IsMorphismInTwistedLinearClosure, IsMorphismInTwistedLinearClosure ] );

DeclareOperation( "/",
                  [ IsCapCategoryMorphism, IsTwistedLinearClosure ] );

####################################
##
#! @Section Global functions
##
####################################

DeclareGlobalFunction( "TWISTED_LINEAR_CLOSURE_CONSTRUCTOR" );

DeclareGlobalFunction( "TWISTED_LINEAR_CLOSURE_CONSTRUCTOR_USING_CategoryOfRows" );

