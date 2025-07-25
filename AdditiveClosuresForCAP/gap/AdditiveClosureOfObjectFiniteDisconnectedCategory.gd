# SPDX-License-Identifier: GPL-2.0-or-later
# FiniteCocompletions: Finite (co)product/(co)limit (co)completions
#
# Declarations
#

#! @Chapter Additive closure of an object finite disconnected category

#! @BeginChunk AddClosureDisconnectedIntroduction

#! Let $C$ be a pre-additive category with finitely many objects.
#! Assume, that for any two non-isomorphic objects $S_1, S_2 \in C$ we have
#! $\mathrm{Hom}_C( S_1, S_2 ) = \{ 0_{ S_1, S_2 } \}$, i.e.,
#! the only morphism between $S_1$ and $S_2$ is the zero morphism.
#! 
#! The objects of the additive closure of this disconnected category
#! are the same as those of
#! <C>AdditiveClosureOfObjectFiniteCategory</C>, see
#! Chapter <Ref Chap="Chapter_AdditiveClosureObjectFinite" />.
#! 
#! Recall, that the morphisms in the (general) additive closure $C^\oplus$ are given by
#! matrices whose entries are morphisms in $C$ and whose dimensions are given
#! by the number of objects in the source and range lists.
#! Then, after reordering the rows and columns of the matrix of morphisms as in
#! Chapter <Ref Chap="Chapter_AdditiveClosureObjectFinite" /> and removing the
#! zero rows and columns, we get a block-diagonal matrix.
#! So we only need to remember the blocks on the diagonal.
#! 
#! For example, assume all the objects of $C$ are $\{ S_1, S_2, S_3, S_4 \}$ satisfying
#! $\mathrm{Hom}_C(S_i,S_j) = \{ 0_{ij} \}$ for $i \neq j$.
#! A morphism
#! @BeginLatexOnly
#! \begin{center}
#!      $S_1 \oplus S_2 \oplus S_1 \oplus S_3 \rightarrow S_3 \oplus S_1 \oplus S_3$
#! \end{center}
#! @EndLatexOnly
#! in the general additive closure $C^\oplus$ is given by the below left matrix.
#! This will be reordered into the below middle matrix for the corresponding morphism
#! @BeginLatexOnly
#! \begin{center}
#!      $[ 4, [ 2, 1, 1, 0 ] ] \rightarrow [ 3, [ 1, 0, 2, 0 ] ]$.
#! \end{center}
#! @EndLatexOnly
#! The additive closure of a disconnected category then extracts the blocks for the below right
#! list of matrices.
#! @BeginLatexOnly
#! \begin{center}
#!    \[
#!      \begin{array}{c|ccc}
#!                 & S_3    & S_1    & S_3    \\
#!          \hline
#!          S_1    & 0_{13} & m_{11} & 0_{13} \\
#!          S_2    & 0_{23} & 0_{21} & 0_{23} \\
#!          S_1    & 0_{13} & m_{11} & 0_{13} \\
#!          S_3    & m_{33} & 0_{31} & m_{33}
#!      \end{array}
#!      \qquad
#!      \begin{array}{c|ccc}
#!                 & S_1    & S_3    & S_3    \\
#!          \hline
#!          S_1    & \cellcolor{lightgray!25} m_{11} & 0_{13} & 0_{13} \\
#!          S_1    & \cellcolor{lightgray!25} m_{11} & 0_{13} & 0_{13} \\
#!          \textcolor{lightgray}{S_2} & \textcolor{lightgray}{0_{21}} & \textcolor{lightgray}{0_{23}} & \textcolor{lightgray}{0_{23}} \\
#!          S_3    & 0_{31} & \cellcolor{lightgray!25} m_{33} & \cellcolor{lightgray!25} m_{33}
#!      \end{array}
#!      \qquad
#!      \Biggl[
#!          \begin{pmatrix}
#!              m_{11} \\
#!              m_{11}
#!          \end{pmatrix},
#!          \;
#!          \begin{pmatrix}{}
#!          \end{pmatrix},
#!          \;
#!          \begin{pmatrix}
#!              m_{33} & m_{33}
#!          \end{pmatrix}
#!          \;
#!          \begin{pmatrix}{}
#!          \end{pmatrix},
#!      \Biggr]
#!    \]
#! \end{center}
#! @EndLatexOnly
#! The second matrix is a zero matrix of dimensions $1 \times 0$ and
#! the fourth matrix is a zero matrix of dimensions $0 \times 0$.
#! 
#! If $C$ is skeletal, then the additive closure of a disconnected category is also skeletal.

#! @EndChunk

####################################
##
#! @Section &GAP; Categories
##
####################################

#! @Description
#!  The &GAP; category of additive closures of disconnected object finite Ab-categories.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsAdditiveClosureOfObjectFiniteDisconnectedCategory",
                 IsCapCategory );

#! @Description
#!  The &GAP; category of objects in additive closures of disconnected object finite Ab-categories.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory",
                 IsCapCategoryObject );

#! @Description
#!  The &GAP; category of morphisms in additive closures of disconnected object finite Ab-categories.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategory",
                 IsCapCategoryMorphism );

####################################
##
#! @Section Constructors
##
####################################

#! @Description
#!  The argument is a disconnected object finite pre-additive category $C$. The output is its additive closure $C^\oplus$.
#! @Arguments C
#! @Returns the category $C^{\oplus}$
DeclareAttribute( "AdditiveClosureOfObjectFiniteDisconnectedCategory",
                  IsCapCategory );

#! @Description
#!  Same as <Ref Attr="AdditiveClosureOfObjectFiniteDisconnectedCategory" Label="for IsCapCategory" />, but as an operation instead of an attribute.
#! @Arguments C
#! @Returns the category $C^\oplus$
DeclareOperation( "ADDITIVE_CLOSURE_OF_OBJECT_FINITE_DISCONNECTED_CATEGORY",
                  [ IsCapCategory ] );

if false then
#! @Description
#! The input is an additive closure <A>AC</A><C> := AdditiveClosureOfObjectFiniteDisconnectedCategory(</C> $A$ <C>)</C>
#! of a disconnected object finite pre-additive category <A>A</A> and a list of the format
#! $[ s, [ m_1, ..., m_n ] ]$ representing a direct sum $S_1^{m_1} \oplus \dots \oplus S_n^{m_n}$ where
#! * $S_1, \dots, S_n$ are all of the objects in the underlying category;
#! * $m_1, ..., m_n$ are integers representing the multiplicties;
#! * $s$ is the sum of integers $m_1 + \dots + m_n$.
#! See also <Ref Attr="NrSummandsAndMultiplicities" Label="for IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory" />.
#! @Arguments ACD, l
#! @Returns a &CAP; category object
DeclareOperation( "ObjectConstructor", [ IsAdditiveClosureOfObjectFiniteDisconnectedCategory, IsList ] );

#! @Description
#! The input is an additive closure <A>AC</A><C> := AdditiveClosureOfObjectFiniteDisconnectedCategory(</C> $A$ <C>)</C>
#! of a disconnected object finite pre-additive category <A>A</A>,
#! * <A>s</A> is the source object,
#! * <A>list_of_matrices</A> is a list of lists of lists of morphisms in A,
#! * <A>t</A> is the target object.
#! See also <Ref Attr="ListOfMatrices" Label="for IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategory" />.
#! @Arguments ACD, s, list_of_matrices, t
#! @Returns a &CAP; category morphism
DeclareOperation( "MorphismConstructor", [ IsAdditiveClosureOfObjectFiniteDisconnectedCategory, IsList ] );
fi;

####################################
#
#! @Section Attributes
#
####################################

#! @Description
#!  Return the category $A$ underlying the additive closure
#!  <A>AC</A><C> := AdditiveClosureOfObjectFiniteDisconnectedCategory(</C> $A$ <C>)</C>.
#! @Arguments ACD
DeclareAttribute( "UnderlyingCategory",
        IsAdditiveClosureOfObjectFiniteDisconnectedCategory );

CapJitAddTypeSignature( "UnderlyingCategory", [ IsAdditiveClosureOfObjectFiniteDisconnectedCategory ],
  function ( input_types )
    
    return CapJitDataTypeOfCategory( UnderlyingCategory( input_types[1].category ) );
    
end );

#! @Description
#!  Return the number of objects in the category $A$ underlying the additive closure
#!  <A>AC</A><C> := AdditiveClosureOfObjectFiniteDisconnectedCategory(</C> $A$ <C>)</C>.
#! @Arguments AC
DeclareAttribute( "NumberOfObjectsOfUnderlyingCategory",
        IsAdditiveClosureOfObjectFiniteDisconnectedCategory );

CapJitAddTypeSignature( "NumberOfObjectsOfUnderlyingCategory", [ IsAdditiveClosureOfObjectFiniteDisconnectedCategory ], IsBigInt );

#! @Description
#!  Return the list of objects in the category $A$ underlying the additive closure
#!  <A>AC</A><C> := AdditiveClosureOfObjectFiniteDisconnectedCategory(</C> $A$ <C>)</C>.
#! @Arguments AC
DeclareAttribute( "ListOfObjectsOfUnderlyingCategory",
        IsAdditiveClosureOfObjectFiniteDisconnectedCategory );

CapJitAddTypeSignature( "ListOfObjectsOfUnderlyingCategory", [ IsAdditiveClosureOfObjectFiniteDisconnectedCategory ],
  function ( input_types )
    
    return CapJitDataTypeOfListOf( CapJitDataTypeOfObjectOfCategory( UnderlyingCategory( input_types[1].category ) ) );
    
end );

#! @Description
#!  The argument is an object in the additive closure of a disconnected object finite pre-additive category.
#!  It returns a list of the format $[ s, [ m_1, ..., m_n ] ]$ representing a
#!  direct sum $S_1^{m_1} \oplus \dots \oplus S_n^{m_n}$ where
#!  * $S_1, \dots, S_n$ are all of the objects in the underlying category;
#!  * $m_1, \dots, m_n$ are integers representing the multiplicties;
#!  * $s$ is the sum of integers $m_1 + \dots + m_n$.
#! @Arguments object
#! @Returns a list consisting of an integer and a list of integers.
DeclareAttribute( "NrSummandsAndMultiplicities",
        IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory );

CapJitAddTypeSignature( "NrSummandsAndMultiplicities", [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory ],
 function ( input_types )
    
    Assert( 0, IsAdditiveClosureOfObjectFiniteDisconnectedCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfNTupleOf( 2,
                   IsBigInt,
                   CapJitDataTypeOfListOf( IsBigInt ) );
    
end );

#! @Description
#! The argument is an object $O$ in an additive closure $C^\oplus$ of a disconnected object finite pre-additive category $C$.
#! It returns a list of objects of $C$ in the format
#! $[ \underbrace{S_1, \dots, S_1}_{m_1}, \dots, \underbrace{S_n, \dots, S_n}_{m_n} ]$
#! corresponding to the list of multiplicties $[ s, [ m_1, ..., m_n ] ]$ of $A$.
#! @Arguments A
#! @Returns a list of objects of the underlying category.
DeclareAttribute( "UnderlyingObjectList", IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory );

CapJitAddTypeSignature( "UnderlyingObjectList", [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory ],
  function ( input_types )
    
    Assert( 0, IsAdditiveClosureOfObjectFiniteDisconnectedCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( CapJitDataTypeOfObjectOfCategory( UnderlyingCategory( input_types[1].category ) ) );
    
end );

#! @Description
#!  The argument is a morphism in the additive closure of a disconnected object finite pre-additive category.
#!  It returns a list of matrices of morphisms of the underlying category.
#! @Arguments morphism
#! @Returns a list of matrices of morphisms of the underlying category.
DeclareAttribute( "ListOfMatrices",
        IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategory );

CapJitAddTypeSignature( "ListOfMatrices", [ IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategory ],
 function ( input_types )
    
    Assert( 0, IsAdditiveClosureOfObjectFiniteDisconnectedCategory( input_types[1].category ) );
    
    return
        CapJitDataTypeOfListOf(
            CapJitDataTypeOfListOf(
                CapJitDataTypeOfListOf(
                    CapJitDataTypeOfMorphismOfCategory( UnderlyingCategory( input_types[1].category ) ) ) ) );
    
end );

####################################
##
#! @Section Operations
##
####################################

#! @Description
#! The argument is an object $O$ in the additive closure $C^\oplus$ of a disconnected object finite pre-additive category $C$.
#! It returns the number $s$ of summands of $A$ corresponding to the list of multiplicties
#! $[ s, [ m_1, ..., m_n ] ]$ of $A$.
#! @Arguments A
#! @Returns an integer
DeclareOperation( "NrOfSummands", [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory ] );

CapJitAddTypeSignature( "NrOfSummands", [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory ],
  function ( input_types )

    Assert( 0, IsAdditiveClosureOfObjectFiniteDisconnectedCategory( input_types[1].category ) );

    return IsBigInt;

end );

#! @Description
#! The argument is an object $O$ in the additive closure $C^\oplus$ of an object finite pre-additive category $C$.
#! It returns the list of multiplicties $[ m_1, \dots, m_n ]$ of $A$.
#! @Arguments A
#! @Returns a list of integers.
DeclareOperation( "Multiplicities", [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory ] );

CapJitAddTypeSignature( "Multiplicities", [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory ],
  function ( input_types )
    
    Assert( 0, IsAdditiveClosureOfObjectFiniteDisconnectedCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( IsBigInt );
    
end );

####################################
##
#! @Section Operators
##
####################################

#! @Description
#! The arguments are an object $S$ in an additive closure $C^\oplus$ of a disconnected object finite category $C$
#! and an integer $i$.
#! The output is the $i$'th entry in <C>UnderlyingObjectList</C>($A$).
#! @Arguments S, i
#! @Returns an object in $C$
DeclareOperation( "[]", [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory, IsBigInt ] );

CapJitAddTypeSignature( "[]", [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategory, IsBigInt ], function ( input_types )
    
    Assert( 0, IsAdditiveClosureOfObjectFiniteDisconnectedCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfObjectOfCategory( UnderlyingCategory( input_types[1].category ) );
    
end );

#! @Description
#! The arguments are a morphism $\alpha \colon A \to B$ in an additive closure $C^\oplus$  of a disconnected object finite
#! pre-additive category $C$ and two integers $i,j$.
#! The output is the $i$'th morphism matrix in <C>ListOfMatrices</C>($\alpha$), i.e.,
#! the morphism matrix for the $i$'th object of the underlying category.
#! @Arguments alpha, i, j
#! @Returns a morphism $C$
DeclareOperation( "[]", [ IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategory, IsBigInt ] );

CapJitAddTypeSignature( "[]", [ IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategory, IsBigInt ], function ( input_types )
    
    Assert( 0, IsAdditiveClosureOfObjectFiniteDisconnectedCategory( input_types[1].category ) );
    
    return
        CapJitDataTypeOfListOf(
            CapJitDataTypeOfListOf(
                CapJitDataTypeOfMorphismOfCategory( UnderlyingCategory( input_types[1].category ) ) ) );
    
end );

#! @Description
#! The input is either
#! * a list of objects or
#! * a list of matrices of morphisms
#! in the underlying category.
#! This operation then constructs either an object or a morphism in <C>AdditiveClosureOfObjectFiniteDisconnectedCategory</C>.
#! For a list of objects, the list will be automatically sorted and the underlying
#! order on the objects need not be respected.
#! 
#! WARNING: Morphism matrices of dimensions $0 \times n$ for $n \geq 1$ are not supported.
#! @Arguments list, ACD
DeclareOperation( "/",
                  [ IsList, IsAdditiveClosureOfObjectFiniteDisconnectedCategory ] );

#! @Description
#! This is a convenience method for
#! <C>ObjectConstructor</C> and <C>MorphismConstructor</C>.
#! @Arguments object or morphism, ACD
#! @Returns an object or morphism in ACD.
DeclareOperation( "/",
                  [ IsCapCategoryCell, IsAdditiveClosureOfObjectFiniteDisconnectedCategory ] );

####################################
##
#! @Section Global functions
##
####################################

#! @Description
#!  The arguments are an additive closure $C^\oplus$ of a disconnected
#!  object finite pre-additive category $C$, a source object $s$ in $C$,
#!  a list $l$ of matrices (i.e. a listlist) of morphisms in the underlying category of $C$
#!  and a target object $t$ in $C$.
#!  It returns a block diagonal matrix (as a list of lists) whose blocks are the given
#!  matrices of $l$.
#! @Arguments ACD, s, list, t
#! @Returns block diagonal matrix
DeclareGlobalFunction( "COMPILATION_HELPER_AdditiveClosureOfObjectFiniteDisconnectedCategory_BlockDiagonalMatrix" );

CapJitAddTypeSignature( "COMPILATION_HELPER_AdditiveClosureOfObjectFiniteDisconnectedCategory_BlockDiagonalMatrix",
                        [ IsAdditiveClosureOfObjectFiniteDisconnectedCategory,
                          IsBigInt,
                          IsList,
                          IsList,
                          IsList ],
  function ( input_types )
    
    return
        CapJitDataTypeOfListOf(
            CapJitDataTypeOfListOf(
                CapJitDataTypeOfMorphismOfCategory( UnderlyingCategory( input_types[1].category ) ) ) );
    
end );

#! @Description
#!  The arguments are an additive closure $C^\oplus$ of a disconnected
#!  object finite pre-additive category $C$, a source object $s$ in $C$,
#!  a list $l$ of matrices (i.e. a listlist) of morphisms in the underlying category of $C$
#!  and a target object $t$ in $C$.
#!  It returns a block diagonal matrix (as a list of lists) whose blocks are the given
#!  matrices of $l$.
#! @Arguments ACD, s, list, t
#! @Returns list of matrices
DeclareGlobalFunction( "COMPILATION_HELPER_AdditiveClosureOfObjectFiniteDisconnectedCategory_ExtractBlocksOfBlockDiagonalMatrix" );

CapJitAddTypeSignature( "COMPILATION_HELPER_AdditiveClosureOfObjectFiniteDisconnectedCategory_ExtractBlocksOfBlockDiagonalMatrix",
                        [ IsAdditiveClosureOfObjectFiniteDisconnectedCategory,
                          IsMorphismInAdditiveClosureOfObjectFiniteCategory ],
  function ( input_types )
    
    return
        CapJitDataTypeOfListOf(
            CapJitDataTypeOfListOf(
                CapJitDataTypeOfListOf(
                    CapJitDataTypeOfMorphismOfCategory( UnderlyingCategory( input_types[1].category ) ) ) ) );
    
end );

