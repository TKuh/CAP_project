# SPDX-License-Identifier: GPL-2.0-or-later
# MonoidalCategories: Monoidal and monoidal (co)closed categories
#
# Implementations
#

##
AddDerivationToCAP( Braiding,
  
  function( cat, object_1, object_2 )
    local source_and_range;
    
    source_and_range := TensorProductOnObjects( cat, object_1, object_2 );
    
    return BraidingWithGivenTensorProducts( cat, source_and_range, object_1, object_2, source_and_range );
    
end : CategoryFilter := IsSkeletalCategory,
      Description := "calling the WithGiven operation in a skeletal setting" );

##
AddDerivationToCAP( BraidingInverse,
  
  function( cat, object_1, object_2 )
    local source_and_range;
    
    source_and_range := TensorProductOnObjects( cat, object_1, object_2 );
    
    return BraidingInverseWithGivenTensorProducts( cat, source_and_range, object_1, object_2, source_and_range );
    
end : CategoryFilter := IsSkeletalCategory,
      Description := "calling the WithGiven operation in a skeletal setting" );

##
AddDerivationToCAP( BraidingInverseWithGivenTensorProducts,
  
  function( cat, object_2_tensored_object_1, object_1, object_2, object_1_tensored_object_2 )
    ##TODO: Use BraidingWithGiven
    return InverseForMorphisms( cat, Braiding( cat, object_1, object_2 ) );
    
end : CategoryFilter := IsBraidedMonoidalCategory,
      Description := "BraidingInverseWithGivenTensorProducts as the inverse of the braiding" );

##
AddDerivationToCAP( BraidingWithGivenTensorProducts,
  
  function( cat, object_1_tensored_object_2, object_1, object_2, object_2_tensored_object_1 )
    ##TODO: Use BraidingInverseWithGiven
    return InverseForMorphisms( cat, BraidingInverse( cat, object_1, object_2 ) );
    
end : CategoryFilter := IsBraidedMonoidalCategory,
      Description := "BraidingWithGivenTensorProducts as the inverse of BraidingInverse" );
