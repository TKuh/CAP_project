# SPDX-License-Identifier: GPL-2.0-or-later
# LinearClosuresForCAP: Linear closures
#
# Declarations
#
#! @Chapter Coproducts of CategoryOfRows with sparse datastructure

#! @BeginChunk CoproductOfCategoryOfRowsWithSparseDatastructureIntroduction

#! Let $R$ be a Homalg ring and $\mathrm{Rows}_R$ a category of rows over $R$.
#! 
#! The objects of the coproduct category $\bigoplus_{i=1}^n \mathrm{Rows}_R$
#! are given by a list of pairs of the form $[ [ r_i, i ], \dots, [ r_j, j ] ] ]$ where
#! * $r_k$ is an object in $\mathrm{Rows}_R$ and
#! * $k$ is the index of the summand of $\bigoplus_{i=1}^n \mathrm{Rows}_R$ in which $r_k$ lives.
#! The indices $i, \dots, j$ have to be strictly increasing with no index occuring twice.
#! 
#! The morphisms are given by a list of pairs of the form $[ [ m_i, i ], \dots, [ m_j, j ] ] ]$ where
#! * $m_k$ is a morphism in $\mathrm{Rows}_R$ and
#! * $k$ is the index of the summand of $\bigoplus_{i=1}^n \mathrm{Rows}_R$ in which $m_k$ lives.
#! The indices $i, \dots, j$ again have to be strictly increasing with no index occuring twice.
#! 
#! This sparse datastructure has the advantage, that zero objects and morphisms with
#! underlying 0x0 matrix need not necessarily be saved.
#! If for an object $o \in \bigoplus_{i=1}^n \mathrm{Rows}_R$ and an index $k$ there is no component
#! $[ r_k, k ]$ in the list of pairs of $o$, then at index $k$ the datastructure
#! assumes a zero object. The same is true for morphisms, where the datastructure assumes
#! a morphism with underlying 0x0 matrix.

#! @EndChunk

####################################
##
#! @Section GAP Categories
##
####################################

#! @Description
#!  The &GAP; category of n-fold coproducts of categories of rows.
#! @Arguments Homalg ring
#! @Returns true or false
DeclareCategory( "IsCoproductOfCategoryOfRowsWithSparseDatastructure",
                 IsCapCategory );

#! @Description
#!  The &GAP; category of objects in n-fold coproducts of categories of rows.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsObjectInCoproductOfCategoryOfRowsWithSparseDatastructure",
                 IsCapCategoryObject );

#! @Description
#!  The &GAP; category of morphisms in n-fold coproducts of categories of rows.
#! @Arguments morphism
#! @Returns true or false
DeclareCategory( "IsMorphismInCoproductOfCategoryOfRowsWithSparseDatastructure",
                 IsCapCategoryMorphism );

####################################
##
#! @Section Constructors
##
####################################

#! @Description
#!  Construct an n-fold coproduct $\bigoplus_{i=1}^n \mathrm{Rows}_R$ over a ring $R$.
#! @Arguments R, n
#! @Returns a &CAP; category
DeclareOperation( "CoproductOfCategoryOfRowsWithSparseDatastructure",
                  [ IsCapCategory, IsBigInt ] );

#! @Description
#!  Same as <Ref Attr="CoproductOfCategoryOfRowsWithSparseDatastructure" Label="for IsCapCategory, IsBigInt" />, but as an operation instead of an attribute.
#! @Arguments C
#! @Returns a &CAP; category
# DeclareOperationWithCache( "COPRODUCT_OF_CATEGORY_OF_ROWS_WITH_SPARSE_DATASTRUCTURE",
                  # [ IsCategoryOfRows, IsBigInt ] );

if false then
#! @Description
#!  The input is a coproduct
#!  <A>C</A><C> := CoproductOfCategoryOfRowsWithSparseDatastructure(</C> $\mathrm{Rows}_R, n$ <C>)</C>
#!  and a list of pairs of the form $[ [ r_i, i ], \dots, [ r_j, j ] ] ]$ where
#!  * $r_k$ is an object in <C>UnderlyingCategoryOfRows(</C> <A>C</A> <C>)</C> and
#!  * $k$ is the index of the summand of $\bigoplus_{i=1}^n \mathrm{Rows}_R$ in which $r_k$ lives.
#!  The indices $i, \dots, j$ have to be strictly increasing with no index occuring twice.
#! @Arguments C, list
#! @Returns an object
DeclareOperation( "ObjectConstructor", [ IsCoproductOfCategoryOfRowsWithSparseDatastructure, IsList ] );
fi;

if false then
#! @Description
#!  The input is a coproduct
#!  <A>C</A><C> := CoproductOfCategoryOfRowsWithSparseDatastructure(</C> $R, n$ <C>)</C>
#!  and a list of pairs of the form $[ [ m_i, i ], \dots, [ m_j, j ] ] ]$ where
#!  * $m_k$ is a morphism in <C>UnderlyingCategoryOfRows(</C> <A>C</A> <C>)</C> and
#!  * $k$ is the index of the summand of $\bigoplus_{i=1}^n \mathrm{Rows}_R$ in which $m_k$ lives.
#!  The indices $i, \dots, j$ have to be strictly increasing with no index occuring twice.
#! @Arguments C, list
#! @Returns an morphism
DeclareOperation( "MorphismConstructor", [ IsCoproductOfCategoryOfRowsWithSparseDatastructure, IsList ] );
fi;

####################################
#
#! @Section Attributes
#
####################################

#! @Description
#!  Return the underlying Homalg ring $R$ of $\bigoplus_{i=1}^n \mathrm{Rows}_R$.
#! @Arguments a CAP category
#! @Returns a Homalg ring
DeclareAttribute( "UnderlyingRing", IsCoproductOfCategoryOfRowsWithSparseDatastructure );

CapJitAddTypeSignature( "UnderlyingRing", [ IsCoproductOfCategoryOfRowsWithSparseDatastructure ],
  function( input_types )
    
    return CapJitDataTypeOfRing( UnderlyingRing( input_types[1].category ) );
    
end );

#! @Description
#!  Return the underlying category of rows of $\bigoplus_{i=1}^n \mathrm{Rows}_R$.
#! @Arguments a CAP category
#! @Returns a CAP category
DeclareAttribute( "UnderlyingCategoryOfRows", IsCoproductOfCategoryOfRowsWithSparseDatastructure );

CapJitAddTypeSignature( "UnderlyingCategoryOfRows", [ IsCoproductOfCategoryOfRowsWithSparseDatastructure ],
  function( input_types )
    
    return CapJitDataTypeOfCategory( UnderlyingCategoryOfRows( input_types[1].category ) );
    
end );

#! @Description
#!  Return the number of summands $n$ of $\bigoplus_{i=1}^n \mathrm{Rows}_R$.
#! @Arguments a CAP category
#! @Returns an integer
DeclareAttribute( "NrOfSummandsOfCoproduct", IsCoproductOfCategoryOfRowsWithSparseDatastructure );

CapJitAddTypeSignature( "NrOfSummandsOfCoproduct", [ IsCoproductOfCategoryOfRowsWithSparseDatastructure ], IsBigInt );

#! @Description
#!  Return a list of pairs of the form $[ [ r_i, i ], \dots, [ r_j, j ] ] ]$ where
#!  * $r_k$ is an object in <C>UnderlyingCategoryOfRows(</C> <A>C</A> <C>)</C> and
#!  * $k$ is the index of the summand of $\bigoplus_{i=1}^n \mathrm{Rows}_R$ in which $r_k$ lives.
#!  The indices $i, \dots, j$ are strictly increasing with no index occuring twice.
#! @Arguments object
#! @Returns a list
DeclareAttribute( "ListOfPairsOfObjectAndIndex", IsObjectInCoproductOfCategoryOfRowsWithSparseDatastructure );

CapJitAddTypeSignature( "ListOfPairsOfObjectAndIndex", [ IsObjectInCoproductOfCategoryOfRowsWithSparseDatastructure ],
  function( input_types )
    
    Assert( 0, IsCoproductOfCategoryOfRowsWithSparseDatastructure( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf(
                CapJitDataTypeOfNTupleOf( 2,
                    CapJitDataTypeOfObjectOfCategory( UnderlyingCategoryOfRows( input_types[1].category ) ),
                    IsBigInt ) );
    
end );

#! @Description
#!  Returns a list of pairs of the form $[ [ m_i, i ], \dots, [ m_j, j ] ] ]$ where
#!  * $m_k$ is a morphism in <C>UnderlyingCategoryOfRows(</C> <A>C</A> <C>)</C> and
#!  * $k$ is the index of the summand of $\bigoplus_{i=1}^n \mathrm{Rows}_R$ in which $m_k$ lives.
#!  The indices $i, \dots, j$ are strictly increasing with no index occuring twice.
#! @Arguments morphism
#! @Returns a list
DeclareAttribute( "ListOfPairsOfMorphismAndIndex", IsMorphismInCoproductOfCategoryOfRowsWithSparseDatastructure );

CapJitAddTypeSignature( "ListOfPairsOfMorphismAndIndex", [ IsMorphismInCoproductOfCategoryOfRowsWithSparseDatastructure ],
  function( input_types )
    
    Assert( 0, IsCoproductOfCategoryOfRowsWithSparseDatastructure( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf(
                CapJitDataTypeOfNTupleOf( 2,
                    CapJitDataTypeOfMorphismOfCategory( UnderlyingCategoryOfRows( input_types[1].category ) ),
                    IsBigInt ) );
    
end );

#! @Description
#!  For an object with datum $[ [ r_i, i ], \dots, [ r_j, j ] ]$
#!  return the integer indices $[ i, \dots, j ]$.
#! @Arguments object
#! @Returns a list of integers
DeclareAttribute( "Support", IsObjectInCoproductOfCategoryOfRowsWithSparseDatastructure );

CapJitAddTypeSignature( "Support", [ IsObjectInCoproductOfCategoryOfRowsWithSparseDatastructure ],
  function ( input_types )
    
    Assert( 0, IsCoproductOfCategoryOfRowsWithSparseDatastructure( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

#! @Description
#!  For a morphism with datum $[ [ m_i, i ], \dots, [ m_j, j ] ]$
#!  return the integer indices $[ i, \dots, j ]$.
#! @Arguments morphism
#! @Returns a list of integers
DeclareAttribute( "Support", IsMorphismInCoproductOfCategoryOfRowsWithSparseDatastructure );

CapJitAddTypeSignature( "Support", [ IsMorphismInCoproductOfCategoryOfRowsWithSparseDatastructure ],
  function ( input_types )
    
    Assert( 0, IsCoproductOfCategoryOfRowsWithSparseDatastructure( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

####################################
##
#! @Section Operations
##
####################################

#! @Description
#!  Given an object in <A>C</A> $\coloneqq \bigoplus_{i=1}^n \mathrm{Rows}_R$ with
#!  datum $[ [ r_i, i ], \dots, [ r_j, j ] ]$ and an integer $1 \leq k \leq n$,
#!  return the component $r_k$.
#!  If this component is not part of the datum, return
#!  <C>ZeroObject</C>( $\mathrm{Rows}_R$ ).
#! @Arguments object, integer
#! @Returns an object
DeclareOperation( "Component", [ IsObjectInCoproductOfCategoryOfRowsWithSparseDatastructure, IsBigInt ] );

CapJitAddTypeSignature( "Component", [ IsObjectInCoproductOfCategoryOfRowsWithSparseDatastructure, IsBigInt ],
  function ( input_types )
    
    Assert( 0, IsCoproductOfCategoryOfRowsWithSparseDatastructure( input_types[1].category ) );
    
    return CapJitDataTypeOfObjectOfCategory( UnderlyingCategoryOfRows( input_types[1].category ) );
    
end );

#! @Description
#!  Given a morphism $m$ in <A>C</A> $\coloneqq \bigoplus_{i=1}^n \mathrm{Rows}_R$ with
#!  datum $[ [ m_i, i ], \dots, [ m_j, j ] ]$ and an integer $1 \leq k \leq n$,
#!  return the component $m_k$.
#!  If this component is not part of the datum, return
#!  <C>ZeroMorphism</C>( $\mathrm{Rows}_R$, <C>Source</C>( $m$ )[$k$], <C>Target</C>( $m$ )[$k$] ).
#! @Arguments morphism, integer
#! @Returns a morphism
DeclareOperation( "Component", [ IsMorphismInCoproductOfCategoryOfRowsWithSparseDatastructure, IsBigInt ] );

CapJitAddTypeSignature( "Component", [ IsMorphismInCoproductOfCategoryOfRowsWithSparseDatastructure, IsBigInt ],
  function ( input_types )
    
    Assert( 0, IsCoproductOfCategoryOfRowsWithSparseDatastructure( input_types[1].category ) );
    
    return CapJitDataTypeOfMorphismOfCategory( UnderlyingCategoryOfRows( input_types[1].category ) );
    
end );

#! @Description
#!  Delegates to <Ref Oper="Component" Label="for IsObjectInCoproductOfCategoryOfRowsWithSparseDatastructure, IsBigInt" />.
#! @Arguments object, integer
#! @Returns an object
DeclareOperation( "[]", [ IsObjectInCoproductOfCategoryOfRowsWithSparseDatastructure, IsInt ] );

CapJitAddTypeSignature( "[]", [ IsObjectInCoproductOfCategoryOfRowsWithSparseDatastructure, IsInt ],
  function ( input_types )
    
    Assert( 0, IsCoproductOfCategoryOfRowsWithSparseDatastructure( input_types[1].category ) );
    
    return CapJitDataTypeOfObjectOfCategory( UnderlyingCategoryOfRows( input_types[1].category ) );
    
end );

#! @Description
#!  Delegates to <Ref Oper="Component" Label="for IsMorphismInCoproductOfCategoryOfRowsWithSparseDatastructure, IsBigInt" />.
#! @Arguments morphism, integer
#! @Returns a morphism
DeclareOperation( "[]", [ IsMorphismInCoproductOfCategoryOfRowsWithSparseDatastructure, IsInt ] );

CapJitAddTypeSignature( "[]", [ IsMorphismInCoproductOfCategoryOfRowsWithSparseDatastructure, IsInt ],
  function ( input_types )
    
    Assert( 0, IsCoproductOfCategoryOfRowsWithSparseDatastructure( input_types[1].category ) );
    
    return CapJitDataTypeOfMorphismOfCategory( UnderlyingCategoryOfRows( input_types[1].category ) );
    
end );

#! @Description
#! The input is either
#! * a list $l$ of non-negative integers with Length($l$) = NrOfSummandsOfCoproduct( C );
#! * a list of pairs $[ [ r_i, i ], \dots, [ r_j, j ] ]$ as required by <Ref Oper="ObjectConstructor" Label="for IsCoproductOfCategoryOfRowsWithSparseDatastructure, IsList" />;
#! * a list $l$ of Homalg matrices with Length($l$) = NrOfSummandsOfCoproduct( C );
#! * a list of pairs $[ [ m_i, i ], \dots, [ m_j, j ] ]$ as required by <Ref Oper="MorphismConstructor" Label="for IsCoproductOfCategoryOfRowsWithSparseDatastructure, IsList" />;
#! This operation then constructs either an object or a morphism in <C>CoproductOfCategoryOfRowsWithSparseDatastructure</C>.
#! @Arguments list
#! @Returns an object or a morphism
DeclareOperation( "/",
                  [ IsList, IsCoproductOfCategoryOfRowsWithSparseDatastructure ] );

####################################
##
#! @Section Global functions
##
####################################

#! @Description
#!  Turn a list of pairs into a dense list of integer multiplicities.
DeclareGlobalFunction( "COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList" );

CapJitAddTypeSignature( "COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseObjectListToDenseList",
                        [ IsCoproductOfCategoryOfRowsWithSparseDatastructure, IsList, IsList],
  function ( input_types )
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

#! @Description
#!  Turn a list of pairs into a dense list of matrices as listlist's.
DeclareGlobalFunction( "COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList" );

CapJitAddTypeSignature( "COMPILATION_HELPER_CoproductOfCategoryOfRows_SparseMatricesListToDenseList",
                        [ IsCoproductOfCategoryOfRowsWithSparseDatastructure, IsList, IsList ],
  function ( input_types )
    local LC;
    
    LC := UnderlyingCategory( ModelingCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf(
                CapJitDataTypeOfListOf(
                    CapJitDataTypeOfListOf(
                        CapJitDataTypeOfMorphismOfCategory( LC ) ) ) );
    
end );

#! @Description
#!  Turn a dense list of integer multiplicities into a sparse list of pairs of objects in the
#!  underlying category of rows and an integer index.
DeclareGlobalFunction( "COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseObjectListToSparseList" );

CapJitAddTypeSignature( "COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseObjectListToSparseList",
                        [ IsCoproductOfCategoryOfRowsWithSparseDatastructure, IsList ],
  function ( input_types )
    local Rows;
    
    Rows := UnderlyingCategoryOfRows( input_types[1].category );
    
    return CapJitDataTypeOfListOf(
                CapJitDataTypeOfNTupleOf( 2,
                        CapJitDataTypeOfObjectOfCategory( Rows ),
                        IsBigInt ) );
    
end );

#! @Description
#!  Turn a dense list of matrices as listlist's with entries in the underlying linear closure of
#!  the modeling additive closure into a sparse list of pairs of a matrix as a listlist and an integer index.
DeclareGlobalFunction( "COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList" );

CapJitAddTypeSignature( "COMPILATION_HELPER_CoproductOfCategoryOfRows_DenseMatricesListToSparseList",
                        [ IsCoproductOfCategoryOfRowsWithSparseDatastructure, IsList, IsList, IsList, ],
  function ( input_types )
    local LinearClosure;
    
    LinearClosure := UnderlyingCategory( ModelingCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf(
                CapJitDataTypeOfNTupleOf( 2,
                    CapJitDataTypeOfListOf( CapJitDataTypeOfListOf( CapJitDataTypeOfMorphismOfCategory( LinearClosure ) ) ),
                    IsBigInt ) );
    
end );

