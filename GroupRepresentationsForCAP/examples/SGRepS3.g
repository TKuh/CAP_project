#! @Chapter Skeletal Category of group represenations
#! @Section Examples and Tests

#! @Example
LoadPackage( "GroupRepresentationsForCAP", false );
#! true

QQ := HomalgFieldOfRationalsInSingular();;
S4 := SymmetricGroup( 4 );;
SGReps := SkeletalCategoryOfGroupRepresentations( S4, QQ );
#! SkeletalGroupRepresentations( SymmetricGroup( [ 1 .. 4 ] ), Q )
coproduct := UnderlyingCoproductOfCategoryOfRows( SGReps );;
rows := UnderlyingCategoryOfRows( coproduct );;

Display( SGReps );
#! A CAP category with name SkeletalGroupRepresentations( SymmetricGroup( [ 1 .. 4 ] ), Q ):
#! 
#! 31 primitive operations were used to derive 237 operations for this category which algorithmi\
#! cally
#! * IsLinearCategoryOverCommutativeRing
#! * IsAbelianCategory
#! and furthermore mathematically
#! * IsSkeletalCategory

chars := UnderlyingIrreducibleCharacters( SGReps );;

C := ModelingCategory( SGReps );;
A := ModelingCategory( C );;
L := UnderlyingCategory( A );;
D := UnderlyingCategory( L );;

x_1 := chars[1];;
x_2 := chars[2];;
x_3 := chars[3];;
x_4 := chars[4];;
x_5 := chars[5];;
chars := [ x_1, x_2, x_3, x_4, x_5 ];

#########################################
# Reinterpretation of objects
#########################################

source := ObjectConstructor( SGReps, [ [ 1, 1 ], [ 5, 3 ] ] );;
IsWellDefinedForObjects( source );
#! true
Display( source );
#! 1χ₁⊕ 5χ₃

source_model := ModelingObject( SGReps, source );;
IsWellDefinedForObjects( source_model );
#! true

source = ReinterpretationOfObject( SGReps, source_model );
#! true

source_model := ModelingTowerObjectConstructor( SGReps, [ [ 1, 1 ], [ 5, 3 ] ] );;
IsWellDefinedForObjects( source_model );
#! true

source := ReinterpretationOfObject( SGReps, source_model );;
IsWellDefinedForObjects( source );
#! true

source_model = ModelingObject( SGReps, source );
#! true

#########################################
# Reinterpretation of Morphisms
#########################################

# Reinterpretation -> Model -> Reinterpretation

source := ObjectConstructor( SGReps, [           [ 2, 2 ], [ 1, 3 ], [ 1, 5 ] ] );;
target := ObjectConstructor( SGReps, [ [ 3, 1 ], [ 1, 2 ], [ 2, 3 ]           ] );;

matrix_1 := HomalgMatrix( [ ], 0, 3, QQ );;
matrix_2 := HomalgMatrix( [ [ 4 ], [ 1 ] ], 2, 1, QQ );;
matrix_3 := HomalgMatrix( [ [ 5, 6 ] ], 1, 2, QQ );;
matrix_4 := HomalgMatrix( [ ], 0, 0, QQ );;
matrix_5 := HomalgMatrix( [ ], 1, 0, QQ );;
matrices_pairs := [ [ matrix_1, 1 ],
                    [ matrix_2, 2 ],
                    [ matrix_3, 3 ],
                    [ matrix_5, 5 ] ];;

mor := MorphismConstructor( SGReps, source, matrices_pairs, target );;
IsWellDefinedForMorphisms( mor );
#! true

mor_model := ModelingMorphism( SGReps, mor );;
mor_reiterp := ReinterpretationOfMorphism( SGReps, source, mor_model, target );;
IsWellDefinedForMorphisms( mor_model );
#! true
IsWellDefinedForMorphisms( mor_reiterp );
#! true
mor = mor_reiterp;
#! true

# Model -> Reinterpretation -> Model

source_model := ModelingTowerObjectConstructor( SGReps, [ [ 2, 2 ], [ 1, 3 ], [ 1, 5 ] ] );;
target_model := ModelingTowerObjectConstructor( SGReps, [ [ 3, 1 ], [ 1, 2 ], [ 2, 3 ] ] );;
IsWellDefinedForObjects( ModelingCategory( SGReps ), source_model );
#! true
IsWellDefinedForObjects( ModelingCategory( SGReps ), target_model );
#! true

mor_model := ModelingTowerMorphismConstructor( SGReps, source_model, matrices_pairs, target_model );;
mor_reinterp := ReinterpretationOfMorphism( SGReps, source, mor_model, target );;
IsWellDefinedForMorphisms( mor_reinterp );
#! true
IsWellDefinedForMorphisms( mor_model );
#! true
mor_model = ModelingMorphism( SGReps, mor_reinterp );
#! true

#########################################
# Operations
#########################################

source[2];
#! 2
mor[2];
#! <A 2 x 1 matrix over an internal ring>
o := ObjectConstructor( SGReps, [  ] );;
Display( o );
#! 0
o := ObjectConstructor( SGReps, [ [ 1, 1 ] ] );;
Display( o );
#! 1χ₁

tp := TensorProductOnObjects( SGReps, source, source );
Display( tp );
tm := TensorProductOnMorphisms( SGReps, mor, mor );
Display( tm );

#! @EndExample
