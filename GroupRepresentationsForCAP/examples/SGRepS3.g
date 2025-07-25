#! @Chapter Skeletal Category of group represenations
#! @Section Examples and Tests

#! @Example
LoadPackage( "GroupRepresentationsForCAP", false );
#! true

QQ := HomalgFieldOfRationals();;
S4 := SymmetricGroup( 4 );;
SGReps := SkeletalCategoryOfGroupRepresentations( S4, QQ );
#! SkeletalGroupRepresentations( SymmetricGroup( [ 1 .. 4 ] ), Q )

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

#########################################
# Reinterpretation of objects
#########################################

source := ObjectConstructor( SGReps, [ [ 1, x_1 ], [ 5, x_3 ] ] );;
IsWellDefinedForObjects( source );
#! true
Display( source );
#! 1χ₁⊕ 5χ₃

source_model := ModelingObject( SGReps, source );;
IsWellDefinedForObjects( source_model );
#! true

source = ReinterpretationOfObject( SGReps, source_model );
#! true

source_model := ModelingTowerObjectConstructor( SGReps, [ [ 1, x_1 ], [ 5, x_3 ] ] );;
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

source := ObjectConstructor( SGReps, [ [ 2, x_2 ], [ 1, x_3 ], [ 1, x_5 ] ] );;
target := ObjectConstructor( SGReps, [ [ 3, x_1 ], [ 1, x_2 ], [ 2, x_3 ] ] );;

matrix_1 := HomalgMatrix( [ ], 0, 3, QQ );;
matrix_2 := HomalgMatrix( [ [ 4 ], [ 1 ] ], 2, 1, QQ );;
matrix_3 := HomalgMatrix( [ [ 5, 6 ] ], 1, 2, QQ );;
matrix_4 := HomalgMatrix( [ ], 0, 0, QQ );;
matrix_5 := HomalgMatrix( [ ], 1, 0, QQ );;
matrices := [ matrix_1,  matrix_2,  matrix_3,  matrix_4,  matrix_5 ];;

mor := MorphismConstructor( SGReps, source, matrices, target );;
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

source_model := ModelingTowerObjectConstructor( SGReps, [ [ 2, x_2 ], [ 1, x_3 ], [ 1, x_5 ] ] );;
target_model := ModelingTowerObjectConstructor( SGReps, [ [ 3, x_1 ], [ 1, x_2 ], [ 2, x_3 ] ] );;
IsWellDefinedForObjects( ModelingCategory( SGReps ), source_model );
#! true
IsWellDefinedForObjects( ModelingCategory( SGReps ), target_model );
#! true

mor_model := ModelingTowerMorphismConstructor( SGReps, source_model, matrices, target_model );;
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
Display( mor );
#! <matrix object of dimensions 0x3 over Q>
#! <matrix object of dimensions 2x1 over Q>
#! <matrix object of dimensions 1x2 over Q>
#! <matrix object of dimensions 0x0 over Q>
#! <matrix object of dimensions 1x0 over Q>
View( mor );
#! <An unevaluated 0 x 3 zero matrix over an internal ring>
#! <A 2 x 1 matrix over an internal ring>
#! <A 1 x 2 matrix over an internal ring>
#! <An unevaluated 0 x 0 identity matrix over an internal ring>
#! <An unevaluated 1 x 0 zero matrix over an internal ring>

#! @EndExample
