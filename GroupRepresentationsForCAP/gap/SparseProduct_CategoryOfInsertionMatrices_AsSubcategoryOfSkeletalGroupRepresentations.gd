# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Declarations
#

#! @Chapter Skeletal Group Representations

#! @BeginChunk ProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations

# TODO: Copy and adjust the introduction from SparseProductOfCartesianCategory

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
DeclareCategory( "IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations",
                 IsCapCategory );

#! @Description
#!  The &GAP; category of objects in a skeletal category of group representations.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations",
                 IsCapCategoryObject );

#! @Description
#!  The &GAP; category of morphisms in a skeletal category of group representations.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsMorphismInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations",
                 IsCapCategoryMorphism );

####################################
##
#! @Section Constructors
##
####################################

#! @Description
#! @Arguments category
#! @Returns a category
DeclareOperation( "SparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations",
                  [ IsList ] );

if false then
#! @Description
#!  The input is a category
#!  <A>C</A><C> := ProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations(</C> $G, F$ <C>)</C> and
#!  a triple consisting of
#!    * an integer $0 \leq i \leq |\mathrm{Irr}(G)|$,
#!    * a list $l_1$ of strictly increasing integers with $\texttt{Length}(l_1) = i$,
#!    * a list $l_2$ of integers with $\texttt{Length}(l_2) = i$.
#! @Arguments C, list
#! @Returns an object
DeclareOperation( "ObjectConstructor", [ IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations, IsList ] );
fi;

if false then
#! @Description
#!  The input is a category
#!  <A>C</A><C> := ProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations(</C> $G, F$ <C>)</C>,
#!  a source object <A>S</A>,
#!  a triple consisting of
#!    * an integer $0 \leq i \leq |\mathrm{Irr}(G)|$,
#!    * a list $l_1$ of strictly increasing integers with $\texttt{Length}(l_1) = i$,
#!    * a list $l_2$ of Homalg matrices with $\texttt{Length}(l_2) = i$,
#!  and a target object <A>T</A>.
#! @Arguments C, S, list, T
#! @Returns an morphism
DeclareOperation( "MorphismConstructor", [ IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations, IsList ] );
fi;

####################################
##
#! @Section Attributes
##
####################################

#! @Description
#!  Return the number of irreducible characters of the group $G$.
#! @Arguments a CAP category
#! @Returns an integer
DeclareAttribute( "NrIrreducibleCharacters", IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "NrIrreducibleCharacters", [ IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ], IsBigInt );

#! @Description
#!  Return the list of irreducible characters of $G$.
#! @Arguments C
#! @Returns list of irreducible characters
DeclareAttribute( "UnderlyingIrreducibleCharacters", IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "UnderlyingIrreducibleCharacters", [ IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ],
  function ( input_types )
    
    return CapJitDataTypeOfListOf( IsIrreducibleCharacter );
    
end );

#! @Description
#!  TODO
#! @Arguments
#! @Returns TODO
DeclareAttribute( "UnderlyingProductCategoryOfPermutationCategory",
                   IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations );

#! @Description
#!  TODO
#! @Arguments
#! @Returns TODO
DeclareAttribute( "IsomorphismFromCoreToProductCategoryOfPermutationCategory",
                   IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations );

#! @Description
#!  The argument is an object in a category $C = \bigoplus_{i \leq |\mathrm{Irr}(G)|} \mathrm{Rows}_k$.
#!  It returns a list of pairs of the format $[ [ r_i, \chi_i ], \dots, [ r_j, \chi_j ] ]$
#!  representing a direct sum $r_i \oplus \dots \oplus r_j in C$ where
#!  * $r_i, ..., r_j$ are non-negative integers representing the ranks of vectorspace objects of the $\mathrm{Rows}_k$ and
#!  * $chi_i, \dots, chi_j$ are the indices of irreducible characters of $G$.
#! @Arguments object
#! @Returns a list
DeclareAttribute( "TripleOfNrSupportListOfSupportListOfNumberElements", IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "TripleOfNrSupportListOfSupportListOfNumberElements", [ IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations( input_types[1].category ) );
    
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
DeclareAttribute( "TripleOfNrSupportListOfSupportListOfNrBlockColumnsAndListOfBlockColumns", IsMorphismInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "TripleOfNrSupportListOfSupportListOfNrBlockColumnsAndListOfBlockColumns", [ IsMorphismInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations( input_types[1].category ) );
    
    return CapJitDataTypeOfNTupleOf( 3,
            IsBigInt,
            CapJitDataTypeOfListOf( IsBigInt ),
            CapJitDataTypeOfListOf(
                CapJitDataTypeOfNTupleOf( 2,
                    IsBigInt,
                    CapJitDataTypeOfListOf(
                        CapJitDataTypeOfNTupleOf( 2,
                            IsBigInt,
                            IsBigInt ) ) ) ) );
                            
end );

#! @Description
#!  Given an object
#!  with datum $[ n, l_1, l_2 ]$, return the integer $n$.
#! @Arguments object
#! @Returns an integer
DeclareAttribute( "NrSupport", IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "NrSupport", [ IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ], IsBigInt );

#! @Description
#!  Given a morphism
#!  with datum $[ n, l_1, l_2 ]$, return the integer $n$.
#! @Arguments morphism
#! @Returns an integer
DeclareAttribute( "NrSupport", IsMorphismInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "NrSupport", [ IsMorphismInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ], IsBigInt );

#! @Description
#!  For an object with datum $[ n, l_1, l_2 ]$,
#!  return the list of integers $l_1$.
#! @Arguments object
#! @Returns a list of integers
DeclareAttribute( "Support", IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "Support", [ IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

#! @Description
#!  For a morphism with datum $[ n, l_1, l_2 ]$,
#!  return the list of integers $l_1$.
#! @Arguments morphism
#! @Returns a list of integers
DeclareAttribute( "Support", IsMorphismInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "Support", [ IsMorphismInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

#! @Description
#!  Given an object with datum $[ n, l_1, l_2 ]$,
#!  return the list of integers $l_2$.
#! @Arguments object
#! @Returns a list of intgers
DeclareAttribute( "Components", IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "Components", [ IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

#! @Description
#!  Given a morphism with datum $[ n, l_1, l_2 ]$,
#!  return the list of Homalg matrices $l_2$.
#! @Arguments morphism
#! @Returns a list of Homalg matrices
DeclareAttribute( "Components", IsMorphismInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations );

CapJitAddTypeSignature( "Components", [ IsMorphismInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf(
                CapJitDataTypeOfNTupleOf( 2,
                    IsBigInt,
                    CapJitDataTypeOfListOf(
                        CapJitDataTypeOfNTupleOf( 2,
                            IsBigInt,
                            IsBigInt ) ) ) );
                            
end );

DeclareAttribute( "DecompositionIntoSimpleObjects",
                  IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations );

####################################
##
#! @Section Operations
##
####################################

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
                  [ IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations, IsBigInt, IsBigInt ] );

CapJitAddTypeSignature( "ProductOfCharactersAsObjectInModelingProductCategory",
                        [ IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations, IsBigInt, IsBigInt ],
                        
  function ( input_types )
    local direct_product_category;
    
    direct_product_category := ModelingCategory( input_types[1].catgory );
    
    return CapJitDataTypeOfObjectOfCategory( direct_product_category );
    
end );

#! @Description
#!  TODO:
#!  The arguments are an object $O$ and an integer $i$.
#!  The output is the rank of the $i$'th summand of $O$.
#! @Arguments O, i
#! @Returns integer
DeclareOperation( "[]", [ IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations, IsInt ] );

#! @Description
#!  TODO:
#!  The arguments are a morphism $\alpha \colon A \to B$ in a disconnected additive closure $C^\oplus$  of an object finite
#!  pre-additive category $C$ and two integers $i,j$.
#!  The output is the $i$'th morphism matrix in <C>ListOfMatrices</C>($\alpha$), i.e.,
#!  the morphism matrix for the $i$'th object of the underlying category.
#! @Arguments alpha, i, j
#! @Returns a morphism $C$
DeclareOperation( "[]", [ IsMorphismInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations, IsInt ] );

#! @Description
#!  Given an object in <A>C</A> $\coloneqq \bigoplus_{i=1}^n \mathrm{Rows}_R$ with
#!  datum $[ n, l_1, l_2 ]$ and an integer $1 \leq k \leq n$,
#!  If $k$ is a supporting summand, i.e., $k \in l_1$,
#!  return the integer of $l_2$ at position $\texttt{Pos}(l_2, k)$.
#!  If $k$ is not a supporting summand then return 0.
#! @Arguments object, integer
#! @Returns an integer
DeclareOperation( "Component", [ IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations, IsBigInt ] );

CapJitAddTypeSignature( "Component", [ IsObjectInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations, IsBigInt ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations( input_types[1].category ) );
    
    return rec( filter := IsBigInt );
    
end );

#! @Description
#!  Given a morphism $m$ in <A>C</A> $\coloneqq \bigoplus_{i=1}^n \mathrm{Rows}_R$ with
#!  datum $[ n, l_1, l_2 ]$ and an integer $1 \leq k \leq n$,
#!  If $k$ is a supporting summand, i.e., $k \in l_1$,
#!  return the Homalg matrix of $l_2$ at position $\texttt{Pos}(l_2, k)$.
#!  If $k$ is not a supporting summand then return
#!  a zero matrix of dimensions <C>Component( Source</C>( $m$ ), $k$ ) $times$ <C>Component( Target</C>( $m$ ), $k$ ) ).
#! @Arguments morphism, integer
#! @Returns a Homalg matrix
DeclareOperation( "Component", [ IsMorphismInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations, IsBigInt ] );

CapJitAddTypeSignature( "Component", [ IsMorphismInSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations, IsBigInt ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfInsertionMatricesAsSubcategoryOfSkeletalGroupRepresentations( input_types[1].category ) );
    
    return CapJitDataTypeOfNTupleOf( 2,
                IsBigInt,
                CapJitDataTypeOfNTupleOf( 2,
                    IsBigInt,
                    IsBigInt ) );
                    
end );

#######################################
##
#! @Section Global functions
##
#######################################

DeclareGlobalFunction( "PRODUCT_OF_CATEGORY_OF_INSERTION_MATRICES_AS_SUBCAT_TensorProductOfMorphismWithIdentityWithGivenTensorProducts" );

DeclareGlobalFunction( "PRODUCT_OF_CATEGORY_OF_INSERTION_MATRICES_AS_SUBCAT_TensorProductOfIdentityWithMorphismWithGivenTensorProducts" );

#! @Description
#!  The arguments are the same as for RightDistributivityExpandingWithGivenObjects
#!  except that this function also gets a list of integer multiplicities and
#!  TODO: the list of objects <C>L</C> must consist of objects who are only
#!  supported at a single factor of the product category.
#!  The output is the same as that of RightDistributivityExpandingWithGivenObjects
#!  with the objects of <C>L</C> being decomposed into simple objects.
#!  The advantage of this function is, that it can handle the multiplicities
#!  in this special case of objects in <C>L</C> (contrary to the general RightDistributivityExpanding).
#!  Example: let $A := [ 1, [1], [3] ], B := [ 1, [2], [5] ]$.
#!           Then $A$ and $B$ are supported at only one factor and computing
#!           <C>RightDistributivityExpandingForUniquelySupportedObjectsWithGivenObjects</C>
#!           with the argument <C>L</C> = $[ A, B ]$ is the same as decomposing $A$ and $B$ into
#!           $A = A' \times A' \times A', B = B' \times B' \times B' \times B' \times B'$ with
#!           $A' := [ 1, [1], [1] ], B' := [ 1, [2], [1] ]$ and calling
#!           <C>RightDistributivityExpandingWithGivenObjects</C>
#!           with <C>L</C> = $[ A', A', A', B', B', B', B', B' ]$.
#! @Returns morphism
#! @Arguments category, source, L, mulitplicities, object, target
DeclareGlobalFunction( "RightDistributivityExpandingWithGivenMultiplicitiesAndObjects" );

DeclareGlobalFunction( "LeftDistributivityExpandingWithGivenMultiplicitiesAndObjects" );

