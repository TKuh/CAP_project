# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Declarations
#

#! @Chapter Skeletal Group Representations

#! @BeginChunk ProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations

# TODO: Copy and adjust the introduction from SparseProductOfCartesianCategory
# Explain that source and target of every morphism are equal, since the same happens
# in the category of permutations.

#! @EndChunk

####################################
##
#! @Section GAP Categories
##
####################################

#! @Description
#!  The &GAP; category of 
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations",
                 IsCapCategory );

#! @Description
#!  The &GAP; category of objects in 
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsObjectInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations",
                 IsCapCategoryObject );

#! @Description
#!  The &GAP; category of morphisms in 
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsMorphismInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations",
                 IsCapCategoryMorphism );

####################################
##
#! @Section Constructors
##
####################################

#! @Description
#! @Arguments category
#! @Returns a category
DeclareOperation( "SparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations",
                  [ IsList ] );

if false then
#! @Description
#!  The input is a category
#!  <A>C</A><C> := ProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations(</C> $G, F$ <C>)</C> and
#!  a triple consisting of
#!    * an integer $0 \leq i \leq |\mathrm{Irr}(G)|$,
#!    * a list $l_1$ of strictly increasing integers with $\texttt{Length}(l_1) = i$,
#!    * a list $l_2$ of integers with $\texttt{Length}(l_2) = i$.
#! @Arguments C, list
#! @Returns an object
DeclareOperation( "ObjectConstructor", [ IsSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations, IsList ] );
fi;

if false then
#! @Description
#!  The input is a category
#!  <A>C</A><C> := ProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations(</C> $G, F$ <C>)</C>,
#!  a source object <A>S</A>,
#!  a triple consisting of
#!    * an integer $0 \leq i \leq |\mathrm{Irr}(G)|$,
#!    * a list $l_1$ of strictly increasing integers with $\texttt{Length}(l_1) = i$,
#!    * a list $l_2$ of Homalg matrices with $\texttt{Length}(l_2) = i$,
#!  and a target object <A>T</A>.
#! @Arguments C, S, list, T
#! @Returns an morphism
DeclareOperation( "MorphismConstructor", [ IsSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations, IsList ] );
fi;

####################################
##
#! @Section Attributes
##
####################################

#! @Description
#!  Return the number of irreducible characters of the group $G$.
#! @Arguments category
#! @Returns integer
DeclareAttribute( "NrIrreducibleCharacters", IsSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "NrIrreducibleCharacters", [ IsSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations ], IsBigInt );

#! @Description
#!  Return the irreducible characters of the group $G$.
#! @Arguments category
#! @Returns list of characters
DeclareAttribute( "UnderlyingIrreducibleCharacters", IsSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "UnderlyingIrreducibleCharacters", [ IsSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations ],
  function ( input_types )
    
    return CapJitDataTypeOfListOf( IsIrreducibleCharacter );
    
end );

#! @Description
#!  The argument is an object in a category $C = \bigoplus_{i \leq |\mathrm{Irr}(G)|} \mathrm{Rows}_k$.
#!  It returns a list of pairs of the format $[ [ r_i, \chi_i ], \dots, [ r_j, \chi_j ] ]$
#!  representing a direct sum $r_i \oplus \dots \oplus r_j in C$ where
#!  * $r_i, ..., r_j$ are non-negative integers representing the ranks of vectorspace objects of the $\mathrm{Rows}_k$ and
#!  * $chi_i, \dots, chi_j$ are the indices of irreducible characters of $G$.
#! @Arguments object
#! @Returns a list
DeclareAttribute( "TripleOfNrSupportListOfSupportListOfCardinalitites", IsObjectInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "TripleOfNrSupportListOfSupportListOfCardinalitites", [ IsObjectInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations( input_types[1].category ) );
    
    return CapJitDataTypeOfNTupleOf( 3,
            IsBigInt,
            CapJitDataTypeOfListOf( IsBigInt ),
            CapJitDataTypeOfListOf( IsBigInt ) );
            
end );

#! @Description
#!  The argument is a morphism in a category $C = \bigoplus_{i \leq |\mathrm{Irr}(G)|} \mathrm{Rows}_k$.
#!  It returns a list of pairs of the format $[ [ m_i, \chi_i ], \dots, [ m_j, \chi_j ] ]$ where
#!  * $m_i, ..., m_j$ are matrices over $k$ and
#!  * $chi_i, \dots, chi_j$ are the indices of irreducible characters of $G$.
#! @Arguments object
#! @Returns a list
DeclareAttribute( "TripleOfNrSupportListOfSupportListOfPermutations", IsMorphismInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "TripleOfNrSupportListOfSupportListOfPermutations", [ IsMorphismInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations( input_types[1].category ) );
    
    return CapJitDataTypeOfNTupleOf( 3,
            IsBigInt,
            CapJitDataTypeOfListOf( IsBigInt ),
            CapJitDataTypeOfListOf( IsPerm ) );
    
end );

#! @Description
#!  Given an object
#!  with datum $[ n, l_1, l_2 ]$, return the integer $n$.
#! @Arguments object
#! @Returns an integer
DeclareAttribute( "NrSupport", IsObjectInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "NrSupport", [ IsObjectInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations ], IsBigInt );

#! @Description
#!  Given a morphism
#!  with datum $[ n, l_1, l_2 ]$, return the integer $n$.
#! @Arguments morphism
#! @Returns an integer
DeclareAttribute( "NrSupport", IsMorphismInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "NrSupport", [ IsMorphismInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations ], IsBigInt );

#! @Description
#!  For an object with datum $[ n, l_1, l_2 ]$,
#!  return the list of integers $l_1$.
#! @Arguments object
#! @Returns a list of integers
DeclareAttribute( "Support", IsObjectInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "Support", [ IsObjectInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

#! @Description
#!  For a morphism with datum $[ n, l_1, l_2 ]$,
#!  return the list of integers $l_1$.
#! @Arguments morphism
#! @Returns a list of integers
DeclareAttribute( "Support", IsMorphismInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "Support", [ IsMorphismInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

#! @Description
#!  Given an object with datum $[ n, l_1, l_2 ]$,
#!  return the list of integers $l_2$.
#! @Arguments object
#! @Returns a list of intgers
DeclareAttribute( "Components", IsObjectInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "Components", [ IsObjectInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

#! @Description
#!  Given a morphism with datum $[ n, l_1, l_2 ]$,
#!  return the list of Homalg matrices $l_2$.
#! @Arguments morphism
#! @Returns a list of Homalg matrices
DeclareAttribute( "Components", IsMorphismInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "Components", [ IsMorphismInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( IsPerm );
    
end );

####################################
##
#! @Section Operations
##
####################################

#! @Description
#!  TODO:
#!  The arguments are an object $O$ and an integer $i$.
#!  The output is the rank of the $i$'th summand of $O$.
#! @Arguments O, i
#! @Returns integer
DeclareOperation( "[]", [ IsObjectInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations, IsInt ] );

#! @Description
#!  TODO:
#!  The arguments are a morphism $\alpha \colon A \to B$ in a disconnected additive closure $C^\oplus$  of an object finite
#!  pre-additive category $C$ and two integers $i,j$.
#!  The output is the $i$'th morphism matrix in <C>ListOfMatrices</C>($\alpha$), i.e.,
#!  the morphism matrix for the $i$'th object of the underlying category.
#! @Arguments alpha, i, j
#! @Returns a morphism $C$
DeclareOperation( "[]", [ IsMorphismInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations, IsInt ] );

#! @Description
#!  Given an object in <A>C</A> $\coloneqq \bigoplus_{i=1}^n \mathrm{Rows}_R$ with
#!  datum $[ n, l_1, l_2 ]$ and an integer $1 \leq k \leq n$,
#!  If $k$ is a supporting summand, i.e., $k \in l_1$,
#!  return the integer of $l_2$ at position $\texttt{Pos}(l_2, k)$.
#!  If $k$ is not a supporting summand then return 0.
#! @Arguments object, integer
#! @Returns an integer
DeclareOperation( "Component",
                  [ IsObjectInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations, IsBigInt ] );

CapJitAddTypeSignature( "Component",
                        [ IsObjectInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations, IsBigInt ],
                        IsBigInt );

#! @Description
#!  Given a morphism $m$ in <A>C</A> $\coloneqq \bigoplus_{i=1}^n \mathrm{Rows}_R$ with
#!  datum $[ n, l_1, l_2 ]$ and an integer $1 \leq k \leq n$,
#!  If $k$ is a supporting summand, i.e., $k \in l_1$,
#!  return the Homalg matrix of $l_2$ at position $\texttt{Pos}(l_2, k)$.
#!  If $k$ is not a supporting summand then return
#!  a zero matrix of dimensions <C>Component( Source</C>( $m$ ), $k$ ) $times$ <C>Component( Target</C>( $m$ ), $k$ ) ).
#! @Arguments morphism, integer
#! @Returns a Homalg matrix
DeclareOperation( "Component",
                  [ IsMorphismInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations, IsBigInt ] );

CapJitAddTypeSignature( "Component",
                        [ IsMorphismInSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations, IsBigInt ],
                        IsPerm );

#######################################
##
#! @Section Global functions
##
#######################################

#! @Description
#!  The arguments are a category TODO
#!  and two positions of characters in <C>UnderlyingIrreducibleCharacters</C>( <A>C</A> ).
#!  It returns an object in ... triple $[ n, l_1, l_2 ]$ where
#!    1. $n = \texttt{Length}(l_1) = \texttt{Length}(l_2)$,
#!    2. $l_1$ is the support, i.e., the positions of all
#!       non-zero characters occuring in the decomposition,
#!    3. $l_2$ is the multiplicity of each irreducible character,
#!       occuring in the decomposion, as an object in the underlying category of rows.
#!  Example in S4: χ₂·χ₃ = 1χ₂⊕1χ₄,
#!                 so this function returns [ 2, [ 2, 4 ], [ RowsObject(1), RowsObject(1) ] ].
#! @Arguments a category, integer, integer
#! @Returns object
DeclareOperation( "ProductOfCharactersAsObjectInModelingProductCategory",
                  [ IsSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations, IsBigInt, IsBigInt ] );

CapJitAddTypeSignature( "ProductOfCharactersAsObjectInModelingProductCategory",
                        [ IsSparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations, IsBigInt, IsBigInt ],
                        
  function ( input_types )
    local direct_product_category;
    
    direct_product_category := ModelingCategory( input_types[1].catgory );
    
    return CapJitDataTypeOfObjectOfCategory( direct_product_category );
    
end );

DeclareGlobalFunction( "PRODUCT_OF_CATEGORY_OF_PERMUTATIONS_AS_SUBCAT_TensorProductProductOfMorphismWithIdentityWithGivenTensorProducts" );

DeclareGlobalFunction( "PRODUCT_OF_CATEGORY_OF_PERMUTATIONS_AS_SUBCAT_TensorProductProductOfIdentityWithMorphismWithGivenProducts" );

