# SPDX-License-Identifier: GPL-2.0-or-later
# MonoidalCategories: Monoidal and monoidal (co)closed categories
#
# Implementations
#

##
AddDerivationToCAP( LeftDistributivityExpanding,
  
  function( cat, object, summands_list )
    local source_and_range;
    
    source_and_range := TensorProductOnObjects( cat, object, DirectSum( cat, summands_list ) );
    
    return LeftDistributivityExpandingWithGivenObjects( cat,
             source_and_range,
             object, summands_list,
             source_and_range
           );
    
end : CategoryFilter := IsSkeletalCategory,
      Description := "calling the WithGiven operation in a skeletal setting" );

##
AddDerivationToCAP( LeftDistributivityExpandingWithGivenObjects,
  
  function( cat, factored_object, object, summands, expanded_object )
    local nr_summands, projection_list, id, diagram;
    
    nr_summands := Length( summands );
    
    id := IdentityMorphism( cat, object );
    
    projection_list := List( [ 1 .. nr_summands ], i -> ProjectionInFactorOfDirectSum( cat, summands, i ) );
    
    projection_list := List( projection_list, mor -> TensorProductOnMorphisms( cat, id, mor ) );
    
    diagram := List( summands, summand -> TensorProductOnObjects( cat, object, summand ) );
    
    return UniversalMorphismIntoDirectSum( cat, diagram, factored_object, projection_list );
    
end : CategoryFilter := IsMonoidalCategory and IsAdditiveCategory,
      Description := "LeftDistributivityExpandingWithGivenObjects using the universal property of the direct sum" );

##
AddDerivationToCAP( LeftDistributivityFactoring,
  
  function( cat, object, summands_list )
    local source_and_range;
    
    source_and_range := TensorProductOnObjects( cat, object, DirectSum( cat, summands_list ) );
    
    return LeftDistributivityFactoringWithGivenObjects( cat,
             source_and_range,
             object, summands_list,
             source_and_range
           );
    
end : CategoryFilter := IsSkeletalCategory,
      Description := "calling the WithGiven operation in a skeletal setting" );

##
AddDerivationToCAP( LeftDistributivityFactoringWithGivenObjects,
  
  function( cat, expanded_object, object, summands, factored_object )
    local nr_summands, injection_list, id, diagram;
    
    nr_summands := Length( summands );
    
    id := IdentityMorphism( cat, object );
    
    injection_list := List( [ 1 .. nr_summands ], i -> InjectionOfCofactorOfDirectSum( cat, summands, i ) );
    
    injection_list := List( injection_list, mor -> TensorProductOnMorphisms( cat, id, mor ) );
    
    diagram := List( summands, summand -> TensorProductOnObjects( cat, object, summand ) );
    
    return UniversalMorphismFromDirectSum( cat, diagram, factored_object, injection_list );
    
end : CategoryFilter := IsMonoidalCategory and IsAdditiveCategory,
      Description := "LeftDistributivityFactoringWithGivenObjects using the universal property of the direct sum" );

##
AddDerivationToCAP( RightDistributivityExpanding,
  
  function( cat, summands_list, object )
    local source_and_range;
    
    source_and_range := TensorProductOnObjects( cat, DirectSum( cat, summands_list ), object );
    
    return RightDistributivityExpandingWithGivenObjects( cat,
             source_and_range,
             summands_list, object,
             source_and_range
           );
    
end : CategoryFilter := IsSkeletalCategory,
      Description := "calling the WithGiven operation in a skeletal setting" );

##
AddDerivationToCAP( RightDistributivityExpandingWithGivenObjects,
  
  function( cat, factored_object, summands, object, expanded_object )
    local nr_summands, projection_list, id, diagram;
    
    nr_summands := Length( summands );
    
    id := IdentityMorphism( cat, object );
    
    projection_list := List( [ 1 .. nr_summands ], i -> ProjectionInFactorOfDirectSum( cat, summands, i ) );
    
    projection_list := List( projection_list, mor -> TensorProductOnMorphisms( cat, mor, id ) );
    
    diagram := List( summands, summand -> TensorProductOnObjects( cat, summand, object ) );
    
    return UniversalMorphismIntoDirectSum( cat, diagram, factored_object, projection_list );
    
end : CategoryFilter := IsMonoidalCategory and IsAdditiveCategory,
      Description := "RightDistributivityExpandingWithGivenObjects using the universal property of the direct sum" );


##
AddDerivationToCAP( RightDistributivityFactoring,

  function( cat, summands_list, object )
    local source_and_range;
    
    source_and_range := TensorProductOnObjects( cat, DirectSum( cat, summands_list ), object );
    
    return RightDistributivityFactoringWithGivenObjects( cat,
             source_and_range,
             summands_list, object,
             source_and_range
           );
    
end : CategoryFilter := IsSkeletalCategory,
      Description := "calling the WithGiven operation in a skeletal setting" );

##
AddDerivationToCAP( RightDistributivityFactoringWithGivenObjects,
  
  function( cat, expanded_object, summands, object, factored_object )
    local nr_summands, injection_list, id, diagram;
    
    nr_summands := Length( summands );
    
    id := IdentityMorphism( cat, object );
    
    injection_list := List( [ 1 .. nr_summands ], i -> InjectionOfCofactorOfDirectSum( cat, summands, i ) );
    
    injection_list := List( injection_list, mor -> TensorProductOnMorphisms( cat, mor, id ) );
    
    diagram := List( summands, summand -> TensorProductOnObjects( cat, summand, object ) );
    
    return UniversalMorphismFromDirectSum( cat, diagram, factored_object, injection_list );
    
end : CategoryFilter := IsMonoidalCategory and IsAdditiveCategory,
      Description := "RightDistributivityFactoringWithGivenObjects using the universal property of the direct sum" );
