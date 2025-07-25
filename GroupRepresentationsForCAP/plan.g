# AdditiveClosureOfObjectFiniteCategory
# AdditiveClosureOfObjectFiniteDisconnectedCategory

DiscreteObjectFiniteCategory :=
  function( list )
    
    D := CreateCapCategoryWithDataType( ...
                 rec( category := false, filter := IsObject ),
                 );
    
    SetUnderlyingListOfGapObjects( D, list );
    
    AddSetOfObjectsOfCategory( D,
      function( D )

        return List( UnderlyingListOfGapObjects, obj -> ObjectConstructor( D, obj ) );
        
    end );

    Finalize( D );
    
    return D;
    
end );

##
CoproductOfCategoryOfRows :=
  function( k, c )
    
    if c = 1 then
        
        return CategoryOfRows( k );
        
    fi;
    
    discrete_category := DiscreteObjectFiniteCategory( [ 1 .. c ] );
  
    ## k^c
    L := LinearClosure( k, discrete_category );
    
    addL := AdditiveClosureOfObjectFiniteDisconnectedCategory( L );
    
    ## ObjectDatum remains a list of multiplicities
    ## MorphismDatum is now a list of homalg matrices
    rows := ReinterpretationCategory( addL );
    
    return rows;
    
end );

## the new RepresentationCategory
SkeletalCategoryOfGroupRepresentations :=
  function( k, G )
    
    Assert( 0, HasCharacteristic( k ) and Characteristic( k ) = 0 );
    
    ct := CharacterTable( G );
    irr := Irr( ct );
    c := Length( irr );
    
    rows := CoproductOfCategoryOfRows( k, c : Finalize := false );
    
    ## --> add the monoidal structure given by G here, then
    
    Finalize( rows );
    
    ## ObjectDatum becomes that of Sepp
    ## MorphismDatum remains a list of homalg matrices
    Greps := ReinterpretationCategory( rows );

    return Greps;
    
end );
