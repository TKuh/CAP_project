# SPDX-License-Identifier: GPL-2.0-or-later
# LinearClosuresForCAP: Linear closures
#
# Declarations
#

#! @Description
#!  The argument is ... The output is ...
#! @Arguments C
#! @Returns the category ...
DeclareOperation( "ADDITIVE_CLOSURE_OF_LINEAR_CLOSURE_OF_FINITE_SKELETAL_DISCRETE_CATEGORY",
                  [ IsLinearClosure ] );

#! @Description
#!  The argument is ... The output is ...
#! @Arguments C
#! @Returns the category ...
DeclareAttribute( "AdditiveClosureDisconnectedOfLinearClosureOfFiniteSkeletalDiscreteCategory",
                  IsLinearClosure );

#! @Description
#!  The argument is ... The output is ...
#! @Arguments C
#! @Returns the category ...
DeclareOperation( "ADDITIVE_CLOSURE_DISCONNECTED_OF_LINEAR_CLOSURE_OF_FINITE_SKELETAL_DISCRETE_CATEGORY",
                  [ IsLinearClosure ] );

