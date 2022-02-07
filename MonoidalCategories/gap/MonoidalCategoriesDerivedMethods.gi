# SPDX-License-Identifier: GPL-2.0-or-later
# MonoidalCategories: Monoidal and monoidal (co)closed categories
#
# Implementations
#

##
AddDerivationToCAP( AssociatorLeftToRightWithGivenTensorProducts,
  
  function( cat, left_associated_object, object_1, object_2, object_3, right_associated_object )
    
    return InverseForMorphisms( cat, AssociatorRightToLeftWithGivenTensorProducts( cat,
                      right_associated_object,
                      object_1, object_2, object_3,
                      left_associated_object )
                  );
    
end : Description := "AssociatorLeftToRightWithGivenTensorProducts as the inverse of AssociatorRightToLeftWithGivenTensorProducts" );

##
AddDerivationToCAP( AssociatorRightToLeftWithGivenTensorProducts,
  
  function( cat, right_associated_object, object_1, object_2, object_3, left_associated_object )
    
    return InverseForMorphisms( cat, AssociatorLeftToRightWithGivenTensorProducts( cat,
                      left_associated_object,
                      object_1, object_2, object_3,
                      right_associated_object )
                  );
    
end : Description := "AssociatorRightToLeftWithGivenTensorProducts as the inverse of AssociatorLeftToRightWithGivenTensorProducts" );

##
AddDerivationToCAP( LeftUnitorWithGivenTensorProduct,
  
  function( cat, object, unit_tensored_object )
    
    return InverseForMorphisms( cat, LeftUnitorInverseWithGivenTensorProduct( cat, object, unit_tensored_object ) );
    
end : Description := "LeftUnitorWithGivenTensorProduct as the inverse of LeftUnitorInverseWithGivenTensorProduct" );

##
AddDerivationToCAP( LeftUnitorInverseWithGivenTensorProduct,
  
  function( cat, object, unit_tensored_object )
    
    return InverseForMorphisms( cat, LeftUnitorWithGivenTensorProduct( cat, object, unit_tensored_object ) );
    
end : Description := "LeftUnitorInverseWithGivenTensorProduct as the inverse of LeftUnitorWithGivenTensorProduct" );

##
AddDerivationToCAP( RightUnitorWithGivenTensorProduct,
  
  function( cat, object, object_tensored_unit )
    
    return InverseForMorphisms( cat, RightUnitorInverseWithGivenTensorProduct( cat, object, object_tensored_unit ) );
    
end : Description := "RightUnitorWithGivenTensorProduct as the inverse of RightUnitorInverseWithGivenTensorProduct" );

##
AddDerivationToCAP( RightUnitorInverseWithGivenTensorProduct,
  
  function( cat, object, object_tensored_unit )
    
    return InverseForMorphisms( cat, RightUnitorWithGivenTensorProduct( cat, object, object_tensored_unit ) );
    
end : Description := "RightUnitorInverseWithGivenTensorProduct as the inverse of RightUnitorWithGivenTensorProduct" );

##
AddDerivationToCAP( AssociatorLeftToRightWithGivenTensorProducts,
  
  function( cat, left_associated_object, object_1, object_2, object_3, right_associated_object )
    
    return IdentityMorphism( cat, left_associated_object );
    
end : CategoryFilter := IsStrictMonoidalCategory,
      Description := "AssociatorLeftToRightWithGivenTensorProducts as the identity morphism" );

##
AddDerivationToCAP( AssociatorRightToLeftWithGivenTensorProducts,
  
  function( cat, right_associated_object, object_1, object_2, object_3, left_associated_object )
    
    return IdentityMorphism( cat, right_associated_object );
    
end : CategoryFilter := IsStrictMonoidalCategory,
      Description := "AssociatorRightToLeft as the identity morphism" );

##
AddDerivationToCAP( LeftUnitorWithGivenTensorProduct,
  
  function( cat, object, unit_tensored_object )
    
    return IdentityMorphism( cat, object );
      
end : CategoryFilter := IsStrictMonoidalCategory,
      Description := "LeftUnitorWithGivenTensorProduct as the identity morphism" );

##
AddDerivationToCAP( LeftUnitorInverseWithGivenTensorProduct,
  
  function( cat, object, unit_tensored_object )
    
    return IdentityMorphism( cat, object );
    
end : CategoryFilter := IsStrictMonoidalCategory,
      Description := "LeftUnitorInverseWithGivenTensorProduct as the identity morphism" );

##
AddDerivationToCAP( RightUnitorWithGivenTensorProduct,
  
  function( cat, object, object_tensored_unit )
    
    return IdentityMorphism( cat, object );
    
end : CategoryFilter := IsStrictMonoidalCategory,
      Description := "RightUnitorWithGivenTensorProduct as the identity morphism" );

##
AddDerivationToCAP( RightUnitorInverseWithGivenTensorProduct,
  
  function( cat, object, object_tensored_unit )
    
    return IdentityMorphism( cat, object );
    
end : CategoryFilter := IsStrictMonoidalCategory,
      Description := "RightUnitorInverseWithGivenTensorProduct as the identity morphism" );

##
AddDerivationToCAP( AssociatorRightToLeft,
  
function( cat, object_1, object_2, object_3 )
  local source_and_range;
  
  source_and_range := TensorProductOnObjects( cat, object_1, TensorProductOnObjects( cat, object_2, object_3 ) );
  
  return AssociatorRightToLeftWithGivenTensorProducts( cat,
           source_and_range,
           object_1, object_2, object_3,
           source_and_range
         );
  
end : CategoryFilter := IsSkeletalCategory,
    Description := "calling the WithGiven operation in a skeletal setting" );

##
AddDerivationToCAP( AssociatorLeftToRight,

function( cat, object_1, object_2, object_3 )
  local source_and_range;
  
  source_and_range := TensorProductOnObjects( cat, object_1, TensorProductOnObjects( cat, object_2, object_3 ) );
  
  return AssociatorLeftToRightWithGivenTensorProducts( cat,
           source_and_range,
           object_1, object_2, object_3,
           source_and_range
         );
  
end : CategoryFilter := IsSkeletalCategory,
    Description := "calling the WithGiven operation in a skeletal setting" );

##
AddDerivationToCAP( LeftUnitor,

function( cat, object )
  
  return LeftUnitorWithGivenTensorProduct( cat, object, object );
  
end : CategoryFilter := IsSkeletalCategory,
    Description := "calling the WithGiven operation in a skeletal setting" );

##
AddDerivationToCAP( LeftUnitorInverse,

function( cat, object )
  
  return LeftUnitorInverseWithGivenTensorProduct( cat, object, object );
  
end : CategoryFilter := IsSkeletalCategory,
    Description := "calling the WithGiven operation in a skeletal setting" );

##
AddDerivationToCAP( RightUnitor,

function( cat, object )
  
  return RightUnitorWithGivenTensorProduct( cat, object, object );
  
end : CategoryFilter := IsSkeletalCategory,
    Description := "calling the WithGiven operation in a skeletal setting" );

##
AddDerivationToCAP( RightUnitorInverse,

function( cat, object )
  
  return RightUnitorInverseWithGivenTensorProduct( cat, object, object );
  
end : CategoryFilter := IsSkeletalCategory,
    Description := "calling the WithGiven operation in a skeletal setting" );
