# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Declarations
#
#! @Chapter Direct products of the category of permutations

#! @BeginChunk SparseProductOfCategoryOfPermutationsIntroduction

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
DeclareCategory( "IsSparseProductOfCategoryOfPermutations",
                 IsCapCategory );

#! @Description
#!  The &GAP; category of objects in n-fold direct products of a category of permutations.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsObjectInSparseProductOfCategoryOfPermutations",
                 IsCapCategoryObject );

#! @Description
#!  The &GAP; category of morphisms in n-fold direct products of a category of permutations.
#! @Arguments morphism
#! @Returns true or false
DeclareCategory( "IsMorphismInSparseProductOfCategoryOfPermutations",
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
DeclareOperation( "SparseProductOfCategoryOfPermutations",
                  [ IsBigInt, IsCapCategory ] );

if false then
#! @Description
#!  The input is a coproduct
#!  <A>D</A><C> := SparseOfProductOfCategoryOfPermutations(</C> $P, n$ <C>)</C>
#!  and a triple consisting of
#!  * an integer $0 \leq i \leq n$,
#!  * a list $l_1$ of strictly increasing integers with $\texttt{Length}(l_1) = i$,
#!  * a list $l_2$ of objects in $P$ with $\texttt{Length}(l_2) = i$.
#! @Arguments D, list
#! @Returns an object
DeclareOperation( "ObjectConstructor", [ IsSparseProductOfCategoryOfPermutations, IsList ] );
fi;

if false then
#! @Description
#!  The input is a direct product
#!  <A>D</A><C> := SparseOfProductOfCategoryOfPermutations(</C> $n, P$ <C>)</C>,
#!  a source object <A>S</A>,
#!  a triple consisting of
#!    * a positive integer $i \leq n$,
#!    * a list $l_1$ of strictly increasing integers with $\texttt{Length}(l_1) = i$,
#!    * a list $l_2$ of morphisms in $P$ with $\texttt{Length}(l_2) = i$,
#!  and a target object <A>T</A>.
#! @Arguments D, S, list, T
#! @Returns an morphism
DeclareOperation( "MorphismConstructor", [ IsSparseProductOfCategoryOfPermutations, IsList ] );
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
DeclareAttribute( "UnderlyingCategoryOfPermutations", IsSparseProductOfCategoryOfPermutations );

CapJitAddTypeSignature( "UnderlyingCategoryOfPermutations", [ IsSparseProductOfCategoryOfPermutations ],
  function( input_types )
    
    return CapJitDataTypeOfCategory( UnderlyingCategoryOfPermutations( input_types[1].category ) );
    
end );

#! @Description
#!  Return the number of factors $n$ of $\prod_{i=1}^n P$.
#! @Arguments category
#! @Returns an integer
DeclareAttribute( "NrFactors", IsSparseProductOfCategoryOfPermutations );

CapJitAddTypeSignature( "NrFactors", [ IsSparseProductOfCategoryOfPermutations ], IsBigInt );

#! @Description
#!  Return a triple of the form
#!  * a positive integer $i \leq n$,
#!  * a list of strictly increasing integers with $\texttt{Length}(l_1) = i$,
#!  * a list of objects in $A$ with $\texttt{Length}(l_2) = i$.
#! @Arguments object
#! @Returns a list
DeclareAttribute( "TripleOfNrSupportListOfSupportListOfObjects", IsObjectInSparseProductOfCategoryOfPermutations );

CapJitAddTypeSignature( "TripleOfNrSupportListOfSupportListOfObjects", [ IsObjectInSparseProductOfCategoryOfPermutations ],
  function( input_types )
    local A;
    
    Assert( 0, IsSparseProductOfCategoryOfPermutations( input_types[1].category ) );
    
    A := UnderlyingCategoryOfPermutations( input_types[1].category );
    
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
DeclareAttribute( "TripleOfNrSupportListOfSupportListOfMorphisms", IsMorphismInSparseProductOfCategoryOfPermutations );

CapJitAddTypeSignature( "TripleOfNrSupportListOfSupportListOfMorphisms", [ IsMorphismInSparseProductOfCategoryOfPermutations ],
  function( input_types )
    local A;
    
    Assert( 0, IsSparseProductOfCategoryOfPermutations( input_types[1].category ) );
    
    A := UnderlyingCategoryOfPermutations( input_types[1].category );
    
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
DeclareAttribute( "NrSupport", IsObjectInSparseProductOfCategoryOfPermutations );

CapJitAddTypeSignature( "NrSupport", [ IsObjectInSparseProductOfCategoryOfPermutations ], IsBigInt );

#! @Description
#!  Given a morphism in <A>D</A> $\coloneqq \prod_{i=1}^n P$ with
#!  datum $[ n, l_1, l_2 ]$,
#!  return the integer $n$.
#! @Arguments morphism
#! @Returns an integer
DeclareAttribute( "NrSupport", IsMorphismInSparseProductOfCategoryOfPermutations );

CapJitAddTypeSignature( "NrSupport", [ IsMorphismInSparseProductOfCategoryOfPermutations ], IsBigInt );

#! @Description
#!  For an object with datum $[ n, l_1, l_2 ]$,
#!  return the list of integers $l_1$.
#! @Arguments object
#! @Returns a list of integers
DeclareAttribute( "Support", IsObjectInSparseProductOfCategoryOfPermutations );

CapJitAddTypeSignature( "Support", [ IsObjectInSparseProductOfCategoryOfPermutations ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfPermutations( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

#! @Description
#!  For a morphism with datum $[ n, l_1, l_2 ]$,
#!  return the list of integers $l_1$.
#! @Arguments morphism
#! @Returns a list of integers
DeclareAttribute( "Support", IsMorphismInSparseProductOfCategoryOfPermutations );

CapJitAddTypeSignature( "Support", [ IsMorphismInSparseProductOfCategoryOfPermutations ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfPermutations( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

#! @Description
#!  Given an object in <A>D</A> $\coloneqq \prod_{i=1}^n P$ with
#!  datum $[ n, l_1, l_2 ]$,
#!  return the list of objects $l_2$.
#! @Arguments object
#! @Returns a list of objects in the underlying additive category.
DeclareAttribute( "Components", IsObjectInSparseProductOfCategoryOfPermutations );

CapJitAddTypeSignature( "Components", [ IsObjectInSparseProductOfCategoryOfPermutations ],
  function ( input_types )
    local A;
    
    Assert( 0, IsSparseProductOfCategoryOfPermutations( input_types[1].category ) );
    
    A := UnderlyingCategoryOfPermutations( input_types[1].category );
    
    return CapJitDataTypeOfListOf( CapJitDataTypeOfObjectOfCategory( A ) );
    
end );

#! @Description
#!  Given a morphism in <A>D</A> $\coloneqq \prod_{i=1}^n P$ with
#!  datum $[ n, l_1, l_2 ]$,
#!  return the list of morphisms $l_2$.
#! @Arguments morphism
#! @Returns a list of morphisms in the underlying additive category.
DeclareAttribute( "Components", IsMorphismInSparseProductOfCategoryOfPermutations );

CapJitAddTypeSignature( "Components", [ IsMorphismInSparseProductOfCategoryOfPermutations ],
  function ( input_types )
    local A;
    
    Assert( 0, IsSparseProductOfCategoryOfPermutations( input_types[1].category ) );
    
    A := UnderlyingCategoryOfPermutations( input_types[1].category );
    
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
DeclareOperation( "Component", [ IsObjectInSparseProductOfCategoryOfPermutations, IsBigInt ] );

CapJitAddTypeSignature( "Component", [ IsObjectInSparseProductOfCategoryOfPermutations, IsBigInt ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfPermutations( input_types[1].category ) );
    
    return CapJitDataTypeOfObjectOfCategory( UnderlyingCategoryOfPermutations( input_types[1].category ) );
    
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
DeclareOperation( "Component", [ IsMorphismInSparseProductOfCategoryOfPermutations, IsBigInt ] );

CapJitAddTypeSignature( "Component", [ IsMorphismInSparseProductOfCategoryOfPermutations, IsBigInt ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfPermutations( input_types[1].category ) );
    
    return CapJitDataTypeOfMorphismOfCategory( UnderlyingCategoryOfPermutations( input_types[1].category ) );
    
end );

#! @Description
#!  Delegates to <Ref Oper="Component" Label="for IsObjectInSparseProductOfCategoryOfPermutations, IsBigInt" />.
#! @Arguments object, integer
#! @Returns an object
DeclareOperation( "[]", [ IsObjectInSparseProductOfCategoryOfPermutations, IsInt ] );

CapJitAddTypeSignature( "[]", [ IsObjectInSparseProductOfCategoryOfPermutations, IsInt ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfPermutations( input_types[1].category ) );
    
    return CapJitDataTypeOfObjectOfCategory( UnderlyingCategoryOfPermutations( input_types[1].category ) );
    
end );

#! @Description
#!  Delegates to <Ref Oper="Component" Label="for IsMorphismInSparseProductOfCategoryOfPermutations, IsBigInt" />.
#! @Arguments morphism, integer
#! @Returns a morphism
DeclareOperation( "[]", [ IsMorphismInSparseProductOfCategoryOfPermutations, IsInt ] );

CapJitAddTypeSignature( "[]", [ IsMorphismInSparseProductOfCategoryOfPermutations, IsInt ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCategoryOfPermutations( input_types[1].category ) );
    
    return CapJitDataTypeOfMorphismOfCategory( UnderlyingCategoryOfPermutations( input_types[1].category ) );
    
end );

####################################
##
#! @Section Global functions
##
####################################

DeclareGlobalFunction( "INSTALL_FUNCTIONS_FOR_SPARSE_DIRECT_PRODUCT_OF_CATEGORY_OF_PERMUTATIONS" );

