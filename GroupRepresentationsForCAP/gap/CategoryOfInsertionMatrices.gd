# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Declarations
#

#
# No morphisms 0 -> 1,2,3,...
# 
# Only 1,2,3,... -> 0
#

####################################
##
#! @Section GAP Categories
##
####################################

#! @Description
#!  TODO
#! @Arguments TODO
#! @Returns TODO
DeclareCategory( "IsCategoryOfInsertionMatrices",
                 IsCapCategory );

#! @Description
#!  TODO
#! @Arguments TODO
#! @Returns TODO
DeclareCategory( "IsObjectInCategoryOfInsertionMatrices",
                 IsCapCategoryObject );

#! @Description
#!  TODO
#! @Arguments TODO
#! @Returns TODO
DeclareCategory( "IsMorphismInCategoryOfInsertionMatrices",
                 IsCapCategoryMorphism );

####################################
##
#! @Section Constructors
##
####################################

#! @Description
#!  TODO
#! @Arguments TODO
#! @Returns TODO
DeclareOperation( "CategoryOfInsertionMatrices", [ ] );

####################################
#
#! @Section Attributes
#
####################################

#! @Description
#!  TODO
#! @Arguments TODO
#! @Returns TODO
DeclareAttribute( "NumberElements", IsObjectInCategoryOfInsertionMatrices );

CapJitAddTypeSignature( "NumberElements", [ IsObjectInCategoryOfInsertionMatrices ], IsBigInt );

#! @Description
#!  TODO
#! @Arguments TODO
#! @Returns TODO
DeclareAttribute( "NrBlockColumnsAndListOfBlockColumns", IsMorphismInCategoryOfInsertionMatrices );

CapJitAddTypeSignature( "NrBlockColumnsAndListOfBlockColumns", [ IsMorphismInCategoryOfInsertionMatrices ],
                                            
  function ( input_types )
    
    Assert( 0, IsCategoryOfInsertionMatrices( input_types[1].category ) );
    
    return CapJitDataTypeOfNTupleOf( 2,
                IsBigInt,
                CapJitDataTypeOfListOf( CapJitDataTypeOfNTupleOf( 2, IsBigInt, IsBigInt ) ) );
    
end );

#! @Description
#!  TODO
#! @Arguments TODO
#! @Returns TODO
DeclareAttribute( "NrBlockColumns", IsMorphismInCategoryOfInsertionMatrices );

CapJitAddTypeSignature( "NrBlockColumns", [ IsMorphismInCategoryOfInsertionMatrices ], IsBigInt );

#! @Description
#!  TODO
#! @Arguments TODO
#! @Returns TODO
DeclareAttribute( "ListOfBlockColumns", IsMorphismInCategoryOfInsertionMatrices );

CapJitAddTypeSignature( "ListOfBlockColumns", [ IsMorphismInCategoryOfInsertionMatrices ],
                                            
  function ( input_types )
    
    Assert( 0, IsCategoryOfInsertionMatrices( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( CapJitDataTypeOfNTupleOf( 2, IsBigInt, IsBigInt ) );
    
end );

#######################################
##
#! @Section Functors
##
#######################################

##
DeclareOperation( "Functorins_matToCategoryOfRows",
                  [ IsCapCategory, IsCapCategory ] );

