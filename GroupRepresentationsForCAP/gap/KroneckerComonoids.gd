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
DeclareCategory( "IsCategoryOfKroneckerComonoids",
                 IsCapCategory );

#! @Description
#!  TODO
#! @Arguments TODO
#! @Returns TODO
DeclareCategory( "IsObjectInCategoryOfKroneckerComonoids",
                 IsCapCategoryObject );

#! @Description
#!  TODO
#! @Arguments TODO
#! @Returns TODO
DeclareCategory( "IsMorphismInCategoryOfKroneckerComonoids",
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
DeclareOperation( "CategoryOfKroneckerComonoids", [ ] );

####################################
#
#! @Section Attributes
#
####################################

#! @Description
#!  TODO
#! @Arguments TODO
#! @Returns TODO
DeclareAttribute( "UnderlyingPermutationCategory", IsCategoryOfKroneckerComonoids );

#! @Description
#!  TODO
#! @Arguments TODO
#! @Returns TODO
DeclareAttribute( "IsomorphismFromCoreToPermutationCategory", IsCategoryOfKroneckerComonoids );

#! @Description
#!  TODO
#! @Arguments TODO
#! @Returns TODO
DeclareAttribute( "NumberElements", IsObjectInCategoryOfKroneckerComonoids );

CapJitAddTypeSignature( "NumberElements", [ IsObjectInCategoryOfKroneckerComonoids ], IsBigInt );

#! @Description
#!  TODO
#! @Arguments TODO
#! @Returns TODO
DeclareAttribute( "NrBlockColumnsAndListOfBlockColumns", IsMorphismInCategoryOfKroneckerComonoids );

CapJitAddTypeSignature( "NrBlockColumnsAndListOfBlockColumns", [ IsMorphismInCategoryOfKroneckerComonoids ],
                                            
  function ( input_types )
    
    Assert( 0, IsCategoryOfKroneckerComonoids( input_types[1].category ) );
    
    return CapJitDataTypeOfNTupleOf( 2,
                IsBigInt,
                CapJitDataTypeOfListOf( CapJitDataTypeOfNTupleOf( 2, IsBigInt, IsBigInt ) ) );
    
end );

#! @Description
#!  TODO
#! @Arguments TODO
#! @Returns TODO
DeclareAttribute( "NrBlockColumns", IsMorphismInCategoryOfKroneckerComonoids );

CapJitAddTypeSignature( "NrBlockColumns", [ IsMorphismInCategoryOfKroneckerComonoids ], IsBigInt );

#! @Description
#!  TODO
#! @Arguments TODO
#! @Returns TODO
DeclareAttribute( "ListOfBlockColumns", IsMorphismInCategoryOfKroneckerComonoids );

CapJitAddTypeSignature( "ListOfBlockColumns", [ IsMorphismInCategoryOfKroneckerComonoids ],
                                            
  function ( input_types )
    
    Assert( 0, IsCategoryOfKroneckerComonoids( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( CapJitDataTypeOfNTupleOf( 2, IsBigInt, IsBigInt ) );
    
end );

#######################################
##
#! @Section Functors
##
#######################################

##
DeclareOperation( "EmbeddingOfKroneckerComonoidsIntoCategoryOfRows",
                  [ IsCapCategory, IsCapCategory ] );

#######################################
##
#! @Section Global functions
##
#######################################

#! @Description
#!  The arguments are
#!  * a category of Kronecker comonoids,
#!  * a source object,
#!  * a morphism $m$,
#!  * an identity morphism $id$,
#!  * a target object.
#!  The output is the tensor product on morphisms $m \otimes id$.
#!  Warning: We assume that the identity morphism $id$ is normalized, i.e.,
#!           it must consist of at most a single block column.
DeclareGlobalFunction( "CATEGORY_OF_KRONECKER_COMONOIDS_TensorProductOfMorphismWithIdentityWithGivenTensorProducts" );

DeclareGlobalFunction( "CATEGORY_OF_KRONECKER_COMONOIDS_TensorProductOfIdentityWithMorphismWithGivenTensorProducts" );

#! @Description
#!  The inputs are
#!  * a category of insertion matrices,
#!  * a morphism in the given category,
#!  * an integer <C>s</C>.
#!  The output is a morphism with block columns,
#!  which are shifted downwards <C>s</C>-many times.
#!  Warning: the source and target of the morphism must be large enough
#!           so that the shifed blocks are still in its boundaries.
#!  Example: Let m := [ 1, [ 2, 6 ] ].
#!           Shifting m by 1 becomes [ 1, [ 7, 11 ] ];
#!           shifting m by 2 becomes [ 1, [ 12, 16 ] ];
#!           shifting m by 3 becomes [ 1, [ 17, 21 ] ].
#! @Arguments category, morphism, int
#! @Returns morphism
DeclareGlobalFunction( "CATEGORY_OF_KRONECKER_COMONOIDS_RowDownwardShift" );

