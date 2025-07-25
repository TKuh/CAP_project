# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Declarations
#
#! @Chapter Skeletal Group Representations

#! @BeginChunk SkeletalGroupRepresentationsIntroduction

#! TODO: zero matrices can not be ignored (in contrast to CoproductOfCategoryOfRows),
#! because of the TensorProductOnMorphisms: it requires a DirectSumFunctorial over
#! certain morphisms, where zero matrices of the form nx0 or 0xn for n > 0
#! have an impact and necessarily must be available in a morphism datum.
#! Only 0x0 matrices can still be ignored.

#! @EndChunk

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
DeclareAttribute( "UnderlyingGroup",
                  IsSkeletalCategoryOfGroupRepresentations );

#! @Description
#!  The argument is a skeletal category of representations $C = \bigoplus_{i \leq |\mathrm{Irr}(G)|} \mathrm{Rows}_k$.
#!  The output is the underlying character table of the group $G$.
#! @Returns Character table
#! @Arguments C
DeclareAttribute( "UnderlyingCharacterTable",
                  IsSkeletalCategoryOfGroupRepresentations );

CapJitAddTypeSignature( "UnderlyingCharacterTable", [ IsSkeletalCategoryOfGroupRepresentations ], IsCharacterTable );

#! @Description
#!  The argument is a skeletal category of representations $C = \bigoplus_{i \leq |\mathrm{Irr}(G)|} \mathrm{Rows}_k$.
#!  The output is the list of irreducible characters of the group $G$.
#! @Returns List of irreducible characters
#! @Arguments C
DeclareAttribute( "UnderlyingIrreducibleCharacters",
                  IsSkeletalCategoryOfGroupRepresentations );

CapJitAddTypeSignature( "UnderlyingIrreducibleCharacters", [ IsSkeletalCategoryOfGroupRepresentations ],
  function ( input_types )
    
    return CapJitDataTypeOfListOf( IsIrreducibleCharacter );
    
end );

#! @Description
#!  The argument is a skeletal category of representations $C = \bigoplus_{i \leq |\mathrm{Irr}(G)|} \mathrm{Rows}_k$.
#!  The output is the number of irreducible characters of the group $G$.
#! @Returns integer
#! @Arguments C
DeclareAttribute( "NrIrreducibleCharacters",
                  IsSkeletalCategoryOfGroupRepresentations );

CapJitAddTypeSignature( "NrIrreducibleCharacters", [ IsSkeletalCategoryOfGroupRepresentations ], IsBigInt );

#! @Description
#!  The argument is a skeletal category of representations $C = \bigoplus_{i \leq |\mathrm{Irr}(G)|} \mathrm{Rows}_k$.
#!  The output is the underlying splitting field $k$.
#! @Returns k
#! @Arguments C
DeclareAttribute( "UnderlyingSplittingField",
                  IsSkeletalCategoryOfGroupRepresentations );

CapJitAddTypeSignature( "UnderlyingSplittingField", [ IsSkeletalCategoryOfGroupRepresentations ], IsFieldForHomalg );

#! @Description
#!  The argument is a skeletal category of representations $C = \bigoplus_{i \leq |\mathrm{Irr}(G)|} \mathrm{Rows}_k$.
#!  The output is the underlying coproduct category of rows of $C$.
#! @Returns k
#! @Arguments C
DeclareAttribute( "UnderlyingCoproductOfCategoryOfRows",
                  IsSkeletalCategoryOfGroupRepresentations );

CapJitAddTypeSignature( "UnderlyingCoproductOfCategoryOfRows", [ IsSkeletalCategoryOfGroupRepresentations ], IsCoproductOfCategoryOfRowsWithSparseDatastructure );

#! @Description
#!  The argument is an object in a skeletal category of representations $C = \bigoplus_{i \leq |\mathrm{Irr}(G)|} \mathrm{Rows}_k$.
#!  It returns a list of pairs of the format $[ [ r_i, \chi_i ], \dots, [ r_j, \chi_j ] ]$
#!  representing a direct sum $r_i \oplus \dots \oplus r_j in C$ where
#!  * $r_i, ..., r_j$ are non-negative integers representing the ranks of vectorspace objects of the $\mathrm{Rows}_k$ and
#!  * $chi_i, \dots, chi_j$ are the indices of irreducible characters of $G$.
#! @Arguments object
#! @Returns a list
DeclareAttribute( "ListOfPairsOfRankAndIndex", IsObjectInSkeletalCategoryOfGroupRepresentations );

CapJitAddTypeSignature( "ListOfPairsOfRankAndIndex", [ IsObjectInSkeletalCategoryOfGroupRepresentations ],
  function ( input_types )
    
    Assert( 0, IsSkeletalCategoryOfGroupRepresentations( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf(
                CapJitDataTypeOfNTupleOf( 2,
                                          IsBigInt,
                                          IsBigInt ) );
    
end );

#! @Description
#!  The argument is a morphism in a skeletal category of representations $C = \bigoplus_{i \leq |\mathrm{Irr}(G)|} \mathrm{Rows}_k$.
#!  It returns a list of pairs of the format $[ [ m_i, \chi_i ], \dots, [ m_j, \chi_j ] ]$ where
#!  * $m_i, ..., m_j$ are matrices over $k$ and
#!  * $chi_i, \dots, chi_j$ are the indices of irreducible characters of $G$.
#! @Arguments object
#! @Returns a list
DeclareAttribute( "ListOfPairsOfMatrixAndIndex", IsMorphismInSkeletalCategoryOfGroupRepresentations );

CapJitAddTypeSignature( "ListOfPairsOfMatrixAndIndex", [ IsMorphismInSkeletalCategoryOfGroupRepresentations ],
  function ( input_types )
    
    Assert( 0, IsSkeletalCategoryOfGroupRepresentations( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf(
                CapJitDataTypeOfNTupleOf( 2,
                                          IsHomalgMatrix,
                                          IsBigInt ) );
    
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

#! @Description
#!  Given an object with datum $[ [ r_i, i ], \dots, [ r_j, j ] ]$
#!  and an integer $1 \leq k \leq n$, return the component $r_k$.
#!  If this component is not part of the datum, return 0.
#! @Arguments object, integer
#! @Returns an object
DeclareOperation( "Component", [ IsObjectInSkeletalCategoryOfGroupRepresentations, IsBigInt ] );

CapJitAddTypeSignature( "Component", [ IsObjectInSkeletalCategoryOfGroupRepresentations, IsBigInt ],
  function ( input_types )
    
    Assert( 0, IsSkeletalCategoryOfGroupRepresentations( input_types[1].category ) );
    
    return IsBigInt;
    
end );

#! @Description
#!  Given a morphism $m$ with datum $[ [ m_i, i ], \dots, [ m_j, j ] ]$
#!  and an integer $1 \leq k \leq n$, return the component $m_k$.
#!  If this component is not part of the datum, return
#!  <C>HomalgZeroMatrix</C>( <C>Source</C>( $m$ )[$k$], <C>Target</C>( $m$ )[$k$], $R$ ).
#! @Arguments morphism, integer
#! @Returns a matrix
DeclareOperation( "Component", [ IsMorphismInSkeletalCategoryOfGroupRepresentations, IsBigInt ] );

CapJitAddTypeSignature( "Component", [ IsMorphismInSkeletalCategoryOfGroupRepresentations, IsBigInt ],
  function ( input_types )
    
    Assert( 0, IsCoproductOfCategoryOfRowsWithSparseDatastructure( input_types[1].category ) );
    
    return IsHomalgMatrix;
    
end );

####################################
##
#! @Section Global functions
##
####################################

CapJitAddTypeSignature( "*", [ IsIrreducibleCharacter, IsIrreducibleCharacter ], IsCharacter );

CapJitAddTypeSignature( "*", [ IsCharacter, IsCharacter ], IsCharacter );

# CapJitAddTypeSignature( "ScalarProduct", [ IsCharacter, IsCharacter ], IsBigInt );

CapJitAddTypeSignature( "ScalarProduct", [ IsIrreducibleCharacter, IsCharacter ], IsBigInt );

#! @Description
DeclareGlobalFunction( "INSTALL_FUNCTIONS_FOR_SKELETAL_CATEGORY_OF_GROUP_REPRESENTATIONS" );

#! @Description
#!  This function takes as arguments a category of rows, a list of irreducible characters
#!  and a character, which is a product of these irreducible chararacters.
#!  It returns a list of pairs containing
#!    1. the multiplicity of each irreducible character as an object in the category of rows,
#!    2. the index of the irreducible character
#!       in the list of all irreducible characters
#!  occuring in the direct sum decomposion of the given product character.
#!  These pairs will be strictly ordered by the second index.
#!  
#!  Example in S4: χ₂·χ₃ = 1χ₂⊕ 1χ₄,
#!                 so this function returns [ [ RowsObject(1), 2 ], [ RowsObject(1), 4 ] ].
#! @Arguments a category of rows, a list of irreducible characters, a character
#! @Returns a list of pairs
DeclareGlobalFunction( "CATEGORY_OF_SKELETAL_GROUP_REPRESENTATIONS_DECOMPOSE_CHARACTER" );

# Irreducible characters.
CapJitAddTypeSignature( "CATEGORY_OF_SKELETAL_GROUP_REPRESENTATIONS_DECOMPOSE_CHARACTER", [ IsCategoryOfRows, IsList, IsIrreducibleCharacter ],
  function ( input_types )
    
    Assert( 0, IsCategoryOfRows( input_types[1].category ) );
    
    return
        CapJitDataTypeOfListOf(
            CapJitDataTypeOfNTupleOf( 2,
                CapJitDataTypeOfObjectOfCategory( input_types[1].category ),
                IsBigInt ) );
    
end );

# General characters.
CapJitAddTypeSignature( "CATEGORY_OF_SKELETAL_GROUP_REPRESENTATIONS_DECOMPOSE_CHARACTER", [ IsCategoryOfRows, IsList, IsCharacter ],
  function ( input_types )
    
    Assert( 0, IsCategoryOfRows( input_types[1].category ) );
    
    return
        CapJitDataTypeOfListOf(
            CapJitDataTypeOfNTupleOf( 2,
                CapJitDataTypeOfObjectOfCategory( input_types[1].category ),
                IsBigInt ) );
    
end );
