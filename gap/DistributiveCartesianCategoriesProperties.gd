# SPDX-License-Identifier: GPL-2.0-or-later
# CartesianCategories: Cartesian and cocartesian categories and various subdoctrines
#
# Declarations
#

AddCategoricalProperty( [ "IsDistributiveCartesianCategory", "IsCodistributiveCocartesianCategory" ] );

InstallTrueMethod( IsCocartesianCategory, IsDistributiveCartesianCategory );

CAP_INTERNAL_CONSTRUCTIVE_CATEGORIES_RECORD.IsDistributiveCartesianCategory  := Concatenation( [
"LeftCartesianDistributivityExpandingWithGivenObjects",
"RightCartesianDistributivityExpandingWithGivenObjects",
],
CAP_INTERNAL_CONSTRUCTIVE_CATEGORIES_RECORD.IsCartesianCategory,
CAP_INTERNAL_CONSTRUCTIVE_CATEGORIES_RECORD.IsCocartesianCategory );
