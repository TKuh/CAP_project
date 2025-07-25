# SPDX-License-Identifier: GPL-2.0-or-later
# GroupRepresentationsForCAP: Skeletal category of group representations for CAP
#
# Declarations
#
#! @Chapter Direct products of an additive category

#! @BeginChunk SparseProductOfCartesianCategoryIntroduction

#! Let $A$ be an additive category.
#! 
#! An object datum of the direct product $\prod_{i=1}^n A$
#! is given by a triple of the form
#! * a positive integer $i \leq n$,
#! * a list $l_1$ of strictly increasing integers with $\texttt{Length}(l_1) = i$,
#! * a list $l_2$ of objects in $A$ with $\texttt{Length}(l_2) = i$.
#! The list $l_1$ is the support, i.e., in which factor of $\prod_{i=1}^n A$
#! the objects of $l_2$ lie. The support of an object in $l_2$ can be identified via its position.
#! Example: Let $[ 3, [2,4,5], [o2,o4,o5] ]$ be an object in $\prod_{i=1}^n A$.
#! Then the support of $o4$ is 4, since:
#! * the position of $o4$ in [o2,o4,o5] is 2,
#! * and at position 2 of [2,4,5] lies 4.
#! 
#! A morphism datum of the direct product $\prod_{i=1}^n A$
#! is given by a triple of the form
#! * a positive integer $i \leq n$,
#! * a list $l_1$ of strictly increasing integers with $\texttt{Length}(l_1) = i$,
#! * a list $l_2$ of morphisms in $A$ with $\texttt{Length}(l_2) = i$.
#! The list $l_1$ is the support, i.e., in which factor of $\prod_{i=1}^n A$
#! the morphisms of $l_2$ lie. The support of a morphism in $l_2$ can be identified via its position.
#! Example: Let $[ 3, [2,4,5], [m2,m4,m5] ]$ be an morphism in $\prod_{i=1}^n A$.
#! Then the support of $m4$ is 4, since:
#! * the position of $m4$ in [m2,m4,m5] is 2,
#! * and at position 2 of [2,4,5] lies 4.
#! 
#! This is a sparse datastructure in the sense that, zero objects and morphisms with
#! underlying 0x0 matrix need not necessarily be saved.
#! If there is no supporting integer $k$ in $l_1$
#! then at the factor $k$ of $\prod_{i=1}^n A$
#! the datastructure assumes a zero object.
#! Example: The object $[ 3, [2,4,5], [o2,o4,o5] ]$
#! has a zero object at support 1 and 3,
#! since 1,3 ∉ [2,4,5].
#! 
#! The same is true for morphisms, where the datastructure assumes
#! a morphism with underlying 0x0 matrix.

#! @EndChunk

####################################
##
#! @Section GAP Categories
##
####################################

#! @Description
#!  The &GAP; category of n-fold direct products of an additive category.
#! @Arguments category
#! @Returns true or false
DeclareCategory( "IsSparseProductOfCartesianCategory",
                 IsCapCategory );

#! @Description
#!  The &GAP; category of objects in n-fold direct products of an additive category.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsObjectInSparseProductOfCartesianCategory",
                 IsCapCategoryObject );

#! @Description
#!  The &GAP; category of morphisms in n-fold direct products of an additive category.
#! @Arguments morphism
#! @Returns true or false
DeclareCategory( "IsMorphismInSparseProductOfCartesianCategory",
                 IsCapCategoryMorphism );

####################################
##
#! @Section Constructors
##
####################################

#! @Description
#!  Construct an n-fold direct product $\prod_{i=1}^n A$.
#! @Arguments n, A
#! @Returns a category
DeclareOperation( "SparseProductOfCartesianCategory",
                  [ IsBigInt, IsCapCategory ] );

if false then
#! @Description
#!  The input is a coproduct
#!  <A>D</A><C> := SparseProductOfCartesianCategory(</C> $A, n$ <C>)</C>
#!  and a triple consisting of
#!  * an integer $0 \leq i \leq n$,
#!  * a list $l_1$ of strictly increasing integers with $\texttt{Length}(l_1) = i$,
#!  * a list $l_2$ of objects in $A$ with $\texttt{Length}(l_2) = i$.
#! @Arguments D, list
#! @Returns an object
DeclareOperation( "ObjectConstructor", [ IsSparseProductOfCartesianCategory, IsList ] );
fi;

if false then
#! @Description
#!  The input is a coproduct
#!  <A>D</A><C> := SparseProductOfCartesianCategory(</C> $n, A$ <C>)</C>,
#!  a source object <A>S</A>,
#!  a triple consisting of
#!    * a positive integer $i \leq n$,
#!    * a list $l_1$ of strictly increasing integers with $\texttt{Length}(l_1) = i$,
#!    * a list $l_2$ of morphisms in $A$ with $\texttt{Length}(l_2) = i$,
#!  and a target object <A>T</A>.
#! @Arguments D, S, list, T
#! @Returns an morphism
DeclareOperation( "MorphismConstructor", [ IsSparseProductOfCartesianCategory, IsList ] );
fi;

####################################
#
#! @Section Attributes
#
####################################

#! @Description
#!  Return the underlying additive category of $\prod_{i=1}^n A$.
#! @Arguments category
#! @Returns a category
DeclareAttribute( "UnderlyingCartesianCategory", IsSparseProductOfCartesianCategory );

CapJitAddTypeSignature( "UnderlyingCartesianCategory", [ IsSparseProductOfCartesianCategory ],
  function( input_types )
    
    return CapJitDataTypeOfCategory( UnderlyingCartesianCategory( input_types[1].category ) );
    
end );

#! @Description
#!  Return the number of factors $n$ of $\prod_{i=1}^n A$.
#! @Arguments category
#! @Returns an integer
DeclareAttribute( "NrFactors", IsSparseProductOfCartesianCategory );

CapJitAddTypeSignature( "NrFactors", [ IsSparseProductOfCartesianCategory ], IsBigInt );

#! @Description
#!  Return a triple of the form
#!  * a positive integer $i \leq n$,
#!  * a list of strictly increasing integers with $\texttt{Length}(l_1) = i$,
#!  * a list of objects in $A$ with $\texttt{Length}(l_2) = i$.
#! @Arguments object
#! @Returns a list
DeclareAttribute( "TripleOfNrSupportListOfSupportListOfObjects", IsObjectInSparseProductOfCartesianCategory );

CapJitAddTypeSignature( "TripleOfNrSupportListOfSupportListOfObjects", [ IsObjectInSparseProductOfCartesianCategory ],
  function( input_types )
    local A;
    
    Assert( 0, IsSparseProductOfCartesianCategory( input_types[1].category ) );
    
    A := UnderlyingCartesianCategory( input_types[1].category );
    
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
DeclareAttribute( "TripleOfNrSupportListOfSupportListOfMorphisms", IsMorphismInSparseProductOfCartesianCategory );

CapJitAddTypeSignature( "TripleOfNrSupportListOfSupportListOfMorphisms", [ IsMorphismInSparseProductOfCartesianCategory ],
  function( input_types )
    local A;
    
    Assert( 0, IsSparseProductOfCartesianCategory( input_types[1].category ) );
    
    A := UnderlyingCartesianCategory( input_types[1].category );
    
    return CapJitDataTypeOfNTupleOf( 3,
                IsBigInt,
                CapJitDataTypeOfListOf( IsBigInt ),
                CapJitDataTypeOfListOf( CapJitDataTypeOfMorphismOfCategory( A ) ) );
    
end );

#! @Description
#!  Given an object in <A>D</A> $\coloneqq \prod_{i=1}^n A$ with
#!  datum $[ n, l_1, l_2 ]$,
#!  return the integer $n$.
#! @Arguments object
#! @Returns an integer
DeclareAttribute( "NrSupport", IsObjectInSparseProductOfCartesianCategory );

CapJitAddTypeSignature( "NrSupport", [ IsObjectInSparseProductOfCartesianCategory ], IsBigInt );

#! @Description
#!  Given a morphism in <A>D</A> $\coloneqq \prod_{i=1}^n A$ with
#!  datum $[ n, l_1, l_2 ]$,
#!  return the integer $n$.
#! @Arguments morphism
#! @Returns an integer
DeclareAttribute( "NrSupport", IsMorphismInSparseProductOfCartesianCategory );

CapJitAddTypeSignature( "NrSupport", [ IsMorphismInSparseProductOfCartesianCategory ], IsBigInt );

#! @Description
#!  For an object with datum $[ n, l_1, l_2 ]$,
#!  return the list of integers $l_1$.
#! @Arguments object
#! @Returns a list of integers
DeclareAttribute( "Support", IsObjectInSparseProductOfCartesianCategory );

CapJitAddTypeSignature( "Support", [ IsObjectInSparseProductOfCartesianCategory ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCartesianCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

#! @Description
#!  For a morphism with datum $[ n, l_1, l_2 ]$,
#!  return the list of integers $l_1$.
#! @Arguments morphism
#! @Returns a list of integers
DeclareAttribute( "Support", IsMorphismInSparseProductOfCartesianCategory );

CapJitAddTypeSignature( "Support", [ IsMorphismInSparseProductOfCartesianCategory ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCartesianCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

#! @Description
#!  Given an object in <A>D</A> $\coloneqq \prod_{i=1}^n A$ with
#!  datum $[ n, l_1, l_2 ]$,
#!  return the list of objects $l_2$.
#! @Arguments object
#! @Returns a list of objects in the underlying additive category.
DeclareAttribute( "Components", IsObjectInSparseProductOfCartesianCategory );

CapJitAddTypeSignature( "Components", [ IsObjectInSparseProductOfCartesianCategory ],
  function ( input_types )
    local A;
    
    Assert( 0, IsSparseProductOfCartesianCategory( input_types[1].category ) );
    
    A := UnderlyingCartesianCategory( input_types[1].category );
    
    return CapJitDataTypeOfListOf( CapJitDataTypeOfObjectOfCategory( A ) );
    
end );

#! @Description
#!  Given a morphism in <A>D</A> $\coloneqq \prod_{i=1}^n A$ with
#!  datum $[ n, l_1, l_2 ]$,
#!  return the list of morphisms $l_2$.
#! @Arguments morphism
#! @Returns a list of morphisms in the underlying additive category.
DeclareAttribute( "Components", IsMorphismInSparseProductOfCartesianCategory );

CapJitAddTypeSignature( "Components", [ IsMorphismInSparseProductOfCartesianCategory ],
  function ( input_types )
    local A;
    
    Assert( 0, IsSparseProductOfCartesianCategory( input_types[1].category ) );
    
    A := UnderlyingCartesianCategory( input_types[1].category );
    
    return CapJitDataTypeOfListOf( CapJitDataTypeOfMorphismOfCategory( A ) );
    
end );

####################################
##
#! @Section Operations
##
####################################

#! @Description
#!  Given an object in <A>D</A> $\coloneqq \prod_{i=1}^n A$ with
#!  datum $[ n, l_1, l_2 ]$ and an integer $1 \leq k \leq n$,
#!  If $k$ is a supporting factor, i.e., $k \in l_1$,
#!  return the object of $l_2$ at position $\texttt{Pos}(l_2, k)$.
#!  If $k$ is not a supporting factor return <C>ZeroObject</C>( $A$ ).
#! @Arguments object, integer
#! @Returns an object
DeclareOperation( "Component", [ IsObjectInSparseProductOfCartesianCategory, IsBigInt ] );

CapJitAddTypeSignature( "Component", [ IsObjectInSparseProductOfCartesianCategory, IsBigInt ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCartesianCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfObjectOfCategory( UnderlyingCartesianCategory( input_types[1].category ) );
    
end );

#! @Description
#!  Given a morphism $m$ in <A>D</A> $\coloneqq \prod_{i=1}^n A$ with
#!  datum $[ n, l_1, l_2 ]$ and an integer $1 \leq k \leq n$,
#!  If $k$ is a supporting factor, i.e., $k \in l_1$,
#!  return the morphism of $l_2$ at position $\texttt{Pos}(l_2, k)$.
#!  If $k$ is not a supporting factor return
#!  <C>ZeroMorphism</C>( $A$, <C>Component( Source</C>( $m$ ), $k$ ), <C>Component( Target</C>( $m$ ), $k$ ) ).
#! @Arguments morphism, integer
#! @Returns a morphism
DeclareOperation( "Component", [ IsMorphismInSparseProductOfCartesianCategory, IsBigInt ] );

CapJitAddTypeSignature( "Component", [ IsMorphismInSparseProductOfCartesianCategory, IsBigInt ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCartesianCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfMorphismOfCategory( UnderlyingCartesianCategory( input_types[1].category ) );
    
end );

#! @Description
#!  Delegates to <Ref Oper="Component" Label="for IsObjectInSparseProductOfCartesianCategory, IsBigInt" />.
#! @Arguments object, integer
#! @Returns an object
DeclareOperation( "[]", [ IsObjectInSparseProductOfCartesianCategory, IsInt ] );

CapJitAddTypeSignature( "[]", [ IsObjectInSparseProductOfCartesianCategory, IsInt ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCartesianCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfObjectOfCategory( UnderlyingCartesianCategory( input_types[1].category ) );
    
end );

#! @Description
#!  Delegates to <Ref Oper="Component" Label="for IsMorphismInSparseProductOfCartesianCategory, IsBigInt" />.
#! @Arguments morphism, integer
#! @Returns a morphism
DeclareOperation( "[]", [ IsMorphismInSparseProductOfCartesianCategory, IsInt ] );

CapJitAddTypeSignature( "[]", [ IsMorphismInSparseProductOfCartesianCategory, IsInt ],
  function ( input_types )
    
    Assert( 0, IsSparseProductOfCartesianCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfMorphismOfCategory( UnderlyingCartesianCategory( input_types[1].category ) );
    
end );

####################################
##
#! @Section Global functions
##
####################################

DeclareGlobalFunction( "INSTALL_FUNCTIONS_FOR_SPARSE_DIRECT_PRODUCT_OF_CARTESIAN_CATEGORY" );

