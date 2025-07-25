# SPDX-License-Identifier: GPL-2.0-or-later
# LinearClosuresForCAP: Linear closures
#
# Declarations
#
#! @Chapter Coproducts of CategoryOfRows

####################################
##
#! @Section GAP Categories
##
####################################

#! @Description
#!  The &GAP; category of n-fold coproducts of categories of rows.
#! @Arguments Homalg ring
#! @Returns true or false
DeclareCategory( "IsCoproductOfCategoryOfRows",
                 IsCapCategory );

#! @Description
#!  The &GAP; category of objects in n-fold coproducts of categories of rows.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsObjectInCoproductOfCategoryOfRows",
                 IsCapCategoryObject );

#! @Description
#!  The &GAP; category of morphisms in n-fold coproducts of categories of rows.
#! @Arguments morphism
#! @Returns true or false
DeclareCategory( "IsMorphismInCoproductOfCategoryOfRows",
                 IsCapCategoryMorphism );

####################################
##
#! @Section Constructors
##
####################################

#! @Description
#!  Construct an n-fold coproduct of a category of rows
#!  $\bigoplus_{i=1}^n \mathrm{Rows}_R$ over a ring $R$.
#! @Arguments R, n
#! @Returns a CAP category
DeclareOperation( "CoproductOfCategoryOfRows",
                  [ IsCategoryOfRows, IsInt ] );

if false then
#! @Description
#!  The input is a coproduct of a category of rows <A>C</A><C> := CoproductOfCategoryOfRows(</C> $R, n$ <C>)</C>
#!  and a list of objects $[ r_1, ..., r_n ]$ in
#!  <C>UnderlyingCategoryOfRows(</C> <A>C</A> <C>)</C> representing
#!  the object $r_1 \oplus \dots \oplus r_n$ in <A>C</A> where
#! @Arguments C, list
#! @Returns an object
DeclareOperation( "ObjectConstructor", [ IsObjectInCoproductOfCategoryOfRows, IsList ] );
fi;

if false then
#! @Description
#! The input is a coproduct of a category of rows <A>C</A><C> := CoproductOfCategoryOfRows(</C> $R, n$ <C>)</C>,
#!  * <A>s</A> is the source object,
#!  * <A>matrix</A> is a list of Homalg matrices with entries in $k$,
#!  * <A>t</A> is the target object.
#!  See also <Ref Attr="ListOfMorphisms" Label="for IsMorphismInCoproductOfCategoryOfRows" />.
#! @Arguments C, s, matrix, t
#! @Returns a morphism
DeclareOperation( "MorphismConstructor", [ IsMorphismInCoproductOfCategoryOfRows, ] );
fi;

####################################
#
#! @Section Attributes
#
####################################

#! @Description
#!  Return the underlying Homalg ring.
#! @Arguments a CAP category
#! @Returns a Homalg ring
DeclareAttribute( "UnderlyingRing", IsCoproductOfCategoryOfRows );

CapJitAddTypeSignature( "UnderlyingRing", [ IsCoproductOfCategoryOfRows ],
  function( input_types )
    
    return IsHomalgRing;
    
end );

#! @Description
#!  Return the number of copies of a category of rows in a coproduct of a category of rows.
#! @Arguments a CAP category
#! @Returns an integer
DeclareAttribute( "NrOfSummandsOfCoproduct", IsCoproductOfCategoryOfRows );

CapJitAddTypeSignature( "NrOfSummandsOfCoproduct", [ IsCoproductOfCategoryOfRows ],
  function( input_types )
    
    return IsBigInt;
    
end );

#! @Description
#!  Return the Homalg ring underlying the coproduct a category of rows.
#! @Arguments a CAP category
DeclareAttribute( "UnderlyingCategoryOfRows", IsCoproductOfCategoryOfRows );

CapJitAddTypeSignature( "UnderlyingCategoryOfRows", [ IsCoproductOfCategoryOfRows ],
  function( input_types )
    
    return IsCategoryOfRows;
    
end );

#! @Description
#!  TODO:
#!  The argument is an object in the disconnected additive closure of an object finite pre-additive category.
#!  It returns a list of the format $[ s, [ m_1, ..., m_n ] ]$ representing a
#!  direct sum $m_1 \oplus \dots \oplus m_n$ where
#!  * $m_1, \dots, m_n$ are non-negative integers and
#!  * $s$ is the sum of integers $m_1 + \dots + m_n$.
#! @Arguments object
#! @Returns a list consisting of an integer and a list of integers.
DeclareAttribute( "ListOfObjects", IsObjectInCoproductOfCategoryOfRows );

CapJitAddTypeSignature( "ListOfObjects", [ IsObjectInCoproductOfCategoryOfRows ],
 function( input_types )
    
    Assert( 0, IsCoproductOfCategoryOfRows( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( CategoryOfRowsObject );
    
end );

#! @Description
#!  The argument is a morphism in a coproduct of a category of rows.
#!  It returns a the underlying list of morphism in the underlying category of rows.
#! @Arguments morphism
#! @Returns a list of Homalg matrices.
DeclareAttribute( "ListOfMorphisms", IsMorphismInCoproductOfCategoryOfRows );

CapJitAddTypeSignature( "ListOfMorphisms", [ IsMorphismInCoproductOfCategoryOfRows ],
 function( input_types )
    
    Assert( 0, IsCoproductOfCategoryOfRows( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( CategoryOfRowsMorphism );
    
end );

####################################
##
#! @Section Operations
##
####################################

#! @Description
#!  TODO:
#!  The argument is an object $O$ in the additive closure $C^\oplus$ of an object finite pre-additive category $C$.
#!  It returns the list of multiplicties $[ m_1, \dots, m_n ]$ of $A$.
#! @Arguments A
#! @Returns a list of integers.
DeclareOperation( "Ranks", [ IsObjectInCoproductOfCategoryOfRows ] );

CapJitAddTypeSignature( "Ranks", [ IsObjectInCoproductOfCategoryOfRows ],
  function( input_types )
    
    Assert( 0, IsCoproductOfCategoryOfRows( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

#! @Description
#!  TODO:
#!  The arguments are an object $O$ in a coproduct of categories of rows and an integer $i$.
#!  The output is the rank of the $i$'th summand of $O$.
#! @Arguments O, i
#! @Returns integer
DeclareOperation( "[]", [ IsObjectInCoproductOfCategoryOfRows, IsInt ] );

CapJitAddTypeSignature( "[]", [ IsObjectInCoproductOfCategoryOfRows, IsInt ], function ( input_types )
    
    Assert( 0, IsCoproductOfCategoryOfRows( input_types[1].category ) );
    
    return IsBigInt;
    
end );

#! @Description
#!  TODO:
#!  The arguments are a morphism $\alpha \colon A \to B$ in a disconnected additive closure $C^\oplus$  of an object finite
#!  pre-additive category $C$ and two integers $i,j$.
#!  The output is the $i$'th morphism matrix in <C>ListOfMorphisms</C>($\alpha$), i.e.,
#!  the morphism matrix for the $i$'th object of the underlying category.
#! @Arguments alpha, i, j
#! @Returns a morphism $C$
DeclareOperation( "[]", [ IsMorphismInCoproductOfCategoryOfRows, IsInt ] );

CapJitAddTypeSignature( "[]", [ IsMorphismInCoproductOfCategoryOfRows, IsInt ], function ( input_types )
    
    Assert( 0, IsCoproductOfCategoryOfRows( input_types[1].category ) );
    
    return IsHomalgMatrix;
    
end );
