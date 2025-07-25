#! @Chapter Skeletal Category of group representations
#! @Section Examples and Tests

#! @Example
LoadPackage( "GroupRepresentationsForCAP", false );
#! true

S4 := SymmetricGroup( 4 );;
character_table := CharacterTable( S4 );
irreducible_characters := Irr( character_table );

Reinterp := SparseProductOfCategoryOfPermutationsAsSubcategoryOfSkeletalGroupRepresentations( irreducible_characters : no_precompiled_code := true );;
Modeling := ModelingCategory( Reinterp );
cat_of_perms := UnderlyingCategoryOfPermutations( Modeling );

Q := HomalgFieldOfRationals();
rows := CategoryOfRows( Q );

F := Functorins_matToCategoryOfRows( cat_of_perms, rows );

Display( Reinterp );
#! A CAP category with name 𝚷( 5, CategoryOfInsertionMatrices ):
#! 
#! 18 primitive operations were used to derive 52 operations for this categor\
#! y which mathematically
#! * IsSkeletalCategory

terminal := ObjectConstructor( Reinterp, [ 0, [ ], [ ] ] );;
Display( terminal );
#! [ 0, [  ], [  ] ]

one := ObjectConstructor( Reinterp, [ 1, [ 1 ], [ 1 ] ] );;
Display( one );
#! [ 1, [ 1 ], [ 1 ] ]

#########################################
# Reinterpretation of objects
#########################################

source := ObjectConstructor( Reinterp, [ 2, [ 1, 3 ], [ 1, 5 ] ] );;
IsWellDefinedForObjects( source );
#! true
Display( source );
#! [ 2, [ 1, 3 ], [ 1, 5 ] ]

source_model := ModelingObject( Reinterp, source );;
IsWellDefinedForObjects( source_model );
#! true

source = ReinterpretationOfObject( Reinterp, source_model );
#! true

source_model := ModelingTowerObjectConstructor( Reinterp, [ 2, [ 1, 3 ], [ 1, 5 ] ] );;
IsWellDefinedForObjects( source_model );
#! true
s
source := ReinterpretationOfObject( Reinterp, source_model );;
IsWellDefinedForObjects( source );
#! true

source_model = ModelingObject( Reinterp, source );
#! true

#########################################
# Reinterpretation of Morphisms
#########################################

# Reinterpretation -> Model -> Reinterpretation

object := ObjectConstructor( Reinterp, [ 4, [ 1, 2, 3, 5 ], [ 1, 4, 2, 1 ] ] );;

morphism_1 := ();;
morphism_2 := (4,2,1,3);;
morphism_3 := (2,1);;
morphism_4 := ();;
morphism_5 := ();;
triple := [ 4, [ 1, 2, 3, 5 ], [ morphism_1, morphism_2, morphism_3, morphism_5 ] ];;

mor := MorphismConstructor( Reinterp, object, triple, object );;
IsWellDefinedForMorphisms( mor );
#! true

mor_model := ModelingMorphism( Reinterp, mor );;
mor_reiterp := ReinterpretationOfMorphism( Reinterp, object, mor_model, object );;
IsWellDefinedForMorphisms( mor_model );
#! true
IsWellDefinedForMorphisms( mor_reiterp );
#! true
mor = mor_reiterp;
#! true

# Model -> Reinterpretation -> Model

o1 := ObjectConstructor( cat_of_perms, 1 );;
o2 := ObjectConstructor( cat_of_perms, 2 );;
o3 := ObjectConstructor( cat_of_perms, 3 );;
o4 := ObjectConstructor( cat_of_perms, 4 );;
o5 := ObjectConstructor( cat_of_perms, 5 );;

object_model := ModelingTowerObjectConstructor( Reinterp, [ 4, [ 1, 2, 3, 5 ], [ 1, 4, 2, 1 ] ] );;

IsWellDefinedForObjects( ModelingCategory( Reinterp ), object_model );
#! true

mor_model := ModelingTowerMorphismConstructor( Reinterp, object_model, triple, object_model );;
mor_reinterp := ReinterpretationOfMorphism( Reinterp, object, mor_model, object );;
IsWellDefinedForMorphisms( mor_reinterp );
#! true
IsWellDefinedForMorphisms( mor_model );
#! true
mor_model = ModelingMorphism( Reinterp, mor_reinterp );
#! true

#! @EndExample
