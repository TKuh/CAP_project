# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Declarations
#
#! @Chapter Skeletal Group Representations

####################################
##
#! @Section GAP Categories
##
####################################

#! @Description
#!  The &GAP; category of skeletal categories of group representations.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsSkeletalCategoryOfGroupRepresentations",
                 IsCapCategory );

#! @Description
#!  The &GAP; category of objects in a skeletal category of group representations.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsObjectInSkeletalCategoryOfGroupRepresentations",
                 IsCapCategoryObject );

#! @Description
#!  The &GAP; category of morphisms in a skeletal category of group representations.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsMorphismInSkeletalCategoryOfGroupRepresentations",
                 IsCapCategoryMorphism );

####################################
##
#! @Section Constructors
##
####################################

#! @Description
#! @Returns a category
#! @Arguments k, nr_simple_objects
DeclareOperation( "SkeletalCategoryOfGroupRepresentations",
                  [ IsGroup, IsFieldForHomalg ] );

####################################
##
#! @Section Attributes
##
####################################

#! @Description
#!  The argument is a skeletal category of representations $C = \bigoplus_{i \leq |\mathrm{Irr}(G)|} \mathrm{Rows}_k$.
#!  The output is the underlying group $G$.
#! @Returns G
#! @Arguments C
DeclareAttribute( "UnderlyingGroups",
                  IsSkeletalCategoryOfGroupRepresentations );

#! @Description
#!  The argument is a skeletal category of representations $C = \bigoplus_{i \leq |\mathrm{Irr}(G)|} \mathrm{Rows}_k$.
#!  The output is the underlying character table of the group $G$.
#! @Returns Character table
#! @Arguments C
DeclareAttribute( "UnderlyingCharacterTable",
                  IsSkeletalCategoryOfGroupRepresentations );

#! @Description
#!  The argument is a skeletal category of representations $C = \bigoplus_{i \leq |\mathrm{Irr}(G)|} \mathrm{Rows}_k$.
#!  The output is the list of irreducible characters of the group $G$.
#! @Returns List of irreducible characters
#! @Arguments C
DeclareAttribute( "UnderlyingIrreducibleCharacters",
                  IsSkeletalCategoryOfGroupRepresentations );

#! @Description
#!  The argument is a skeletal category of representations $C = \bigoplus_{i \leq |\mathrm{Irr}(G)|} \mathrm{Rows}_k$.
#!  The output is the number of irreducible characters of the group $G$.
#! @Returns integer
#! @Arguments C
DeclareAttribute( "NrIrreducibleCharacters",
                  IsSkeletalCategoryOfGroupRepresentations );


#! @Description
#!  The argument is a skeletal category of representations $C = \bigoplus_{i \leq |\mathrm{Irr}(G)|} \mathrm{Rows}_k$.
#!  The output is the underlying splitting field $k$.
#! @Returns k
#! @Arguments C
DeclareAttribute( "UnderlyingSplittingField",
                  IsSkeletalCategoryOfGroupRepresentations );

#! @Description
#!  The argument is an object in a skeletal category of representations $C = \bigoplus_{i \leq |\mathrm{Irr}(G)|} \mathrm{Rows}_k$.
#!  It returns a list of pairs of the format $[ [ r_i, \chi_i ], \dots, [ r_j, \chi_j ] ]$
#!  representing a direct sum $m_i \oplus \dots \oplus m_j in C$ where
#!  * $chi_i, \dots, chi_j$ are the irreducible characters of $G$ and
#!  * $m_i, ..., m_j$ are non-negative integers representing the ranks of vectorspace objects of the $\mathrm{Rows}_k$.
#! @Arguments object
#! @Returns a list of pairs consisting of a non-negative integer and an irreducible character
DeclareAttribute( "PairsOfRankAndCharacter", IsObjectInSkeletalCategoryOfGroupRepresentations );

CapJitAddTypeSignature( "PairsOfRankAndCharacter", [ IsObjectInSkeletalCategoryOfGroupRepresentations ],
  function ( input_types )
    
    Assert( 0, IsSkeletalCategoryOfGroupRepresentations( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf(
                CapJitDataTypeOfNTupleOf( 2,
                                          IsBigInt,
                                          IsCharacter ) );
    
end );

####################################
##
#! @Section Operations
##
####################################

#! @Description
#!  The argument is an object in a skeletal category of representations $C = \bigoplus_{i \leq |\mathrm{Irr}(G)|} \mathrm{Rows}_k$.
#!  It returns the list of ranks $[ m_1, \dots, m_{n} ]$ for $n = |\mathrm{Irr}(G)|$ of $A$.
#! @Arguments object
#! @Returns a list of integers.
DeclareOperation( "Ranks", [ IsObjectInSkeletalCategoryOfGroupRepresentations ] );

CapJitAddTypeSignature( "Ranks", [ IsObjectInSkeletalCategoryOfGroupRepresentations ],
  function( input_types )
    
    Assert( 0, IsSkeletalCategoryOfGroupRepresentations( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

#! @Description
#!  TODO:
#!  The arguments are an object $O$ in a coproduct of categories of rows and an integer $i$.
#!  The output is the rank of the $i$'th summand of $O$.
#! @Arguments O, i
#! @Returns integer
DeclareOperation( "[]", [ IsObjectInSkeletalCategoryOfGroupRepresentations, IsInt ] );

CapJitAddTypeSignature( "[]", [ IsObjectInSkeletalCategoryOfGroupRepresentations, IsInt ], function ( input_types )
    
    Assert( 0, IsSkeletalCategoryOfGroupRepresentations( input_types[1].category ) );
    
    return IsBigInt;
    
end );

#! @Description
#!  TODO:
#!  The arguments are a morphism $\alpha \colon A \to B$ in a disconnected additive closure $C^\oplus$  of an object finite
#!  pre-additive category $C$ and two integers $i,j$.
#!  The output is the $i$'th morphism matrix in <C>ListOfMatrices</C>($\alpha$), i.e.,
#!  the morphism matrix for the $i$'th object of the underlying category.
#! @Arguments alpha, i, j
#! @Returns a morphism $C$
DeclareOperation( "[]", [ IsMorphismInSkeletalCategoryOfGroupRepresentations, IsInt ] );

CapJitAddTypeSignature( "[]", [ IsMorphismInSkeletalCategoryOfGroupRepresentations, IsInt ], function ( input_types )
    
    Assert( 0, IsSkeletalCategoryOfGroupRepresentations( input_types[1].category ) );
    
    return IsHomalgMatrix;
    
end );
