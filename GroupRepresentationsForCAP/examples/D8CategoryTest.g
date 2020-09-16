LoadPackage( "GroupRepresentationsForCAP" );

RepG := RepresentationCategory( 8, 3 );

G := UnderlyingGroupForRepresentationCategory( RepG );

irr := Irr( G );

v1 := RepresentationCategoryObject( irr[1], RepG );

v2 := RepresentationCategoryObject( irr[2], RepG );

v3 := RepresentationCategoryObject( irr[3], RepG );

v4 := RepresentationCategoryObject( irr[4], RepG );

v4 := RepresentationCategoryObject( irr[4], RepG );

v5 := RepresentationCategoryObject( irr[5], RepG );

L := [ v1, v2, v3, v4, v5 ];
