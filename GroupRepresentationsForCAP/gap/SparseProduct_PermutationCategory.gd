# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Declarations
#
#! @Chapter Direct products of the category of permutations

#! @BeginChunk SparseProductOfPermutationCategoryIntroduction

#! @EndChunk

####################################
##
#! @Section GAP Categories
##
####################################

#! @Description
#!  The &GAP; category of n-fold direct products of a category of permutations.
#! @Arguments category
#! @Returns true or false
DeclareCategory( "IsSparseProductOfPermutationCategory",
                 IsCapCategory );

#! @Description
#!  The &GAP; category of objects in n-fold direct products of a category of permutations.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsObjectInSparseProductOfPermutationCategory",
                 IsCapCategoryObject );

#! @Description
#!  The &GAP; category of morphisms in n-fold direct products of a category of permutations.
#! @Arguments morphism
#! @Returns true or false
DeclareCategory( "IsMorphismInSparseProductOfPermutationCategory",
                 IsCapCategoryMorphism );

####################################
##
#! @Section Constructors
##
####################################

#! @Description
#!  Construct an n-fold direct product $\prod_{i=1}^n P$.
#! @Arguments n, A
#! @Returns a category
DeclareOperation( "SparseProductOfPermutationCategory",
                  [ IsBigInt, IsCapCategory ] );

if false then
#! @Description
#!  The input is a coproduct
#!  <A>D</A><C> := SparseOfProductOfPermutationCategory(</C> $P, n$ <C>)</C>
#!  and a triple consisting of
#!  * an integer $0 \leq i \leq n$,
#!  * a list $l_1$ of strictly increasing integers with $\texttt{Length}(l_1) = i$,
#!  * a list $l_2$ of objects in $P$ with $\texttt{Length}(l_2) = i$.
#! @Arguments D, list
#! @Returns an object
DeclareOperation( "ObjectConstructor", [ IsSparseProductOfPermutationCategory, IsList ] );
fi;

if false then
#! @Description
#!  The input is a direct product
#!  <A>D</A><C> := SparseOfProductOfPermutationCategory(</C> $n, P$ <C>)</C>,
#!  a source object <A>S</A>,
#!  a triple consisting of
#!    * a positive integer $i \leq n$,
#!    * a list $l_1$ of strictly increasing integers with $\texttt{Length}(l_1) = i$,
#!    * a list $l_2$ of morphisms in $P$ with $\texttt{Length}(l_2) = i$,
#!  and a target object <A>T</A>.
#! @Arguments D, S, list, T
#! @Returns an morphism
DeclareOperation( "MorphismConstructor", [ IsSparseProductOfPermutationCategory, IsList ] );
fi;

####################################
#
#! @Section Attributes
#
####################################

#! @Description
#!  Return the underlying category of permutations of $\prod_{i=1}^n P$.
#! @Arguments category
#! @Returns a category
DeclareAttribute( "UnderlyingPermutationCategory", IsSparseProductOfPermutationCategory );

CapJitAddTypeSignature( "UnderlyingPermutationCategory", [ IsSparseProductOfPermutationCategory ],
  function( input_types )
    
    return CapJitDataTypeOfCategory( UnderlyingPermutationCategory( input_types[1].category ) );
    
end );

#! @Description
#!  Return the number of factors $n$ of $\prod_{i=1}^n P$.
#! @Arguments category
#! @Returns an integer
DeclareAttribute( "NrFactors", IsSparseProductOfPermutationCategory );

CapJitAddTypeSignature( "NrFactors", [ IsSparseProductOfPermutationCategory ], IsBigInt );

#! @Description
#!  Return a triple of the form
#!  * a positive integer $i \leq n$,
#!  * a list of strictly increasing integers with $\texttt{Length}(l_1) = i$,
#!  * a list of objects in $A$ with $\texttt{Length}(l_2) = i$.
#! @Arguments object
#! @Returns a list
DeclareAttribute( "TripleOfNrSupportListOfSupportListOfObjects", IsObjectInSparseProductOfPermutationCategory );

CapJitAddTypeSignature( "TripleOfNrSupportListOfSupportListOfObjects", [ IsObjectInSparseProductOfPermutationCategory ],
  function( input_types )
    local A;
    
    Assert( 0, IsSparseProductOfPermutationCategory( input_types[1].category ) );
    
    A := UnderlyingPermutationCategory( input_types[1].category );
    
    return CapJitDataTypeOfNTupleOf( 3,
                IsBigInt,
                CapJitDataTypeOfListOf( IsBigInt ),
                CapJitDataTypeOfListOf( CapJitDataTypeOfObjectOfCategory( A ) ) );
    
end );

#! @Description
#!  Return a triple of the form
#!  * a positive integer $i \leq n$,
#!  * a list of strictly increasing integers with $\texttt{Length}(l_1) = i$,
#!  * a list of morphisms in $A$ with $\texttt{Length}(l_2) = i$.
#! @Arguments morphism
#! @Returns a list
DeclareAttribute( "TripleOfNrSupportListOfSupportListOfMorphisms", IsMorphismInSparseProductOfPermutationCategory );

CapJitAddTypeSignature( "TripleOfNrSupportListOfSupportListOfMorphisms", [ IsMorphismInSparseProductOfPermutationCategory ],
  function( input_types )
    local A;
    
    Assert( 0, IsSparseProductOfPermutationCategory( input_types[1].category ) );
    
    A := UnderlyingPermutationCategory( input_types[1].category );
    
    return CapJitDataTypeOfNTupleOf( 3,
                IsBigInt,
                CapJitDataTypeOfListOf( IsBigInt ),
                CapJitDataTypeOfListOf( CapJitDataTypeOfMorphismOfCategory( A ) ) );
    
end );

#! @Description
#!  Given an object in <A>D</A> $\coloneqq \prod_{i=1}^n P$ with
#!  datum $[ n, l_1, l_2 ]$,
#!  return the integer $n$.
#! @Arguments object
#! @Returns an integer
DeclareAttribute( "NrSupport", IsObjectInSparseProductOfPermutationCategory );

CapJitAddTypeSignature( "NrSupport", [ IsObjectInSparseProductOfPermutationCategory ], IsBigInt );

#! @Description
#!  Given a morphism in <A>D</A> $\coloneqq \prod_{i=1}^n P$ with
#!  datum $[ n, l_1, l_2 ]$,
#!  return the integer $n$.
#! @Arguments morphism
#! @Returns an integer
DeclareAttribute( "NrSupport", IsMorphismInSparseProductOfPermutationCategory );

CapJitAddTypeSignature( "NrSupport", [ IsMorphismInSparseProductOfPermutationCategory ], IsBigInt );

#! @Description
#!  For an object with datum $[ n, l_1, l_2 ]$,
#!  return the list of integers $l_1$.
#! @Arguments object
#! @Returns a list of integers
DeclareAttribute( "Support", IsObjectInSparseProductOfPermutationCategory );

CapJitAddTypeSignature( "Support", [ IsObjectInSparseProductOfPermutationCategory ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfPermutationCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

#! @Description
#!  For a morphism with datum $[ n, l_1, l_2 ]$,
#!  return the list of integers $l_1$.
#! @Arguments morphism
#! @Returns a list of integers
DeclareAttribute( "Support", IsMorphismInSparseProductOfPermutationCategory );

CapJitAddTypeSignature( "Support", [ IsMorphismInSparseProductOfPermutationCategory ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfPermutationCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

#! @Description
#!  Given an object in <A>D</A> $\coloneqq \prod_{i=1}^n P$ with
#!  datum $[ n, l_1, l_2 ]$,
#!  return the list of objects $l_2$.
#! @Arguments object
#! @Returns a list of objects in the underlying additive category.
DeclareAttribute( "Components", IsObjectInSparseProductOfPermutationCategory );

CapJitAddTypeSignature( "Components", [ IsObjectInSparseProductOfPermutationCategory ],
  function ( input_types )
    local A;
    
    Assert( 0, IsSparseProductOfPermutationCategory( input_types[1].category ) );
    
    A := UnderlyingPermutationCategory( input_types[1].category );
    
    return CapJitDataTypeOfListOf( CapJitDataTypeOfObjectOfCategory( A ) );
    
end );

#! @Description
#!  Given a morphism in <A>D</A> $\coloneqq \prod_{i=1}^n P$ with
#!  datum $[ n, l_1, l_2 ]$,
#!  return the list of morphisms $l_2$.
#! @Arguments morphism
#! @Returns a list of morphisms in the underlying additive category.
DeclareAttribute( "Components", IsMorphismInSparseProductOfPermutationCategory );

CapJitAddTypeSignature( "Components", [ IsMorphismInSparseProductOfPermutationCategory ],
  function ( input_types )
    local A;
    
    Assert( 0, IsSparseProductOfPermutationCategory( input_types[1].category ) );
    
    A := UnderlyingPermutationCategory( input_types[1].category );
    
    return CapJitDataTypeOfListOf( CapJitDataTypeOfMorphismOfCategory( A ) );
    
end );

####################################
##
#! @Section Operations
##
####################################

#! @Description
#!  Given an object in <A>D</A> $\coloneqq \prod_{i=1}^n P$ with
#!  datum $[ n, l_1, l_2 ]$ and an integer $1 \leq k \leq n$,
#!  If $k$ is a supporting factor, i.e., $k \in l_1$,
#!  return the object of $l_2$ at position $\texttt{Pos}(l_2, k)$.
#!  If $k$ is not a supporting factor return <C>ZeroObject</C>( $A$ ).
#! @Arguments object, integer
#! @Returns an object
DeclareOperation( "Component", [ IsObjectInSparseProductOfPermutationCategory, IsBigInt ] );

CapJitAddTypeSignature( "Component", [ IsObjectInSparseProductOfPermutationCategory, IsBigInt ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfPermutationCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfObjectOfCategory( UnderlyingPermutationCategory( input_types[1].category ) );
    
end );

#! @Description
#!  Given a morphism $m$ in <A>D</A> $\coloneqq \prod_{i=1}^n P$ with
#!  datum $[ n, l_1, l_2 ]$ and an integer $1 \leq k \leq n$,
#!  If $k$ is a supporting factor, i.e., $k \in l_1$,
#!  return the morphism of $l_2$ at position $\texttt{Pos}(l_2, k)$.
#!  If $k$ is not a supporting factor return
#!  <C>ZeroMorphism</C>( $A$, <C>Component( Source</C>( $m$ ), $k$ ), <C>Component( Target</C>( $m$ ), $k$ ) ).
#! @Arguments morphism, integer
#! @Returns a morphism
DeclareOperation( "Component", [ IsMorphismInSparseProductOfPermutationCategory, IsBigInt ] );

CapJitAddTypeSignature( "Component", [ IsMorphismInSparseProductOfPermutationCategory, IsBigInt ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfPermutationCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfMorphismOfCategory( UnderlyingPermutationCategory( input_types[1].category ) );
    
end );

#! @Description
#!  Delegates to <Ref Oper="Component" Label="for IsObjectInSparseProductOfPermutationCategory, IsBigInt" />.
#! @Arguments object, integer
#! @Returns an object
DeclareOperation( "[]", [ IsObjectInSparseProductOfPermutationCategory, IsInt ] );

CapJitAddTypeSignature( "[]", [ IsObjectInSparseProductOfPermutationCategory, IsInt ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfPermutationCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfObjectOfCategory( UnderlyingPermutationCategory( input_types[1].category ) );
    
end );

#! @Description
#!  Delegates to <Ref Oper="Component" Label="for IsMorphismInSparseProductOfPermutationCategory, IsBigInt" />.
#! @Arguments morphism, integer
#! @Returns a morphism
DeclareOperation( "[]", [ IsMorphismInSparseProductOfPermutationCategory, IsInt ] );

CapJitAddTypeSignature( "[]", [ IsMorphismInSparseProductOfPermutationCategory, IsInt ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfPermutationCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfMorphismOfCategory( UnderlyingPermutationCategory( input_types[1].category ) );
    
end );

####################################
##
#! @Section Global functions
##
####################################

DeclareGlobalFunction( "INSTALL_FUNCTIONS_FOR_SPARSE_DIRECT_PRODUCT_OF_PERMUTATIONCATEGORY" );

