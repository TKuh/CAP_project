# SPDX-License-Identifier: GPL-2.0-or-later
# CartesianCategories: Cartesian and cocartesian categories and various subdoctrines
#
# Declarations
#

AddCategoricalProperty( [ "IsCodistributiveCocartesianCategory", "IsDistributiveCartesianCategory" ] );

InstallTrueMethod( IsCartesianCategory, IsCodistributiveCocartesianCategory );

CAP_INTERNAL_CONSTRUCTIVE_CATEGORIES_RECORD.IsCodistributiveCocartesianCategory  := Concatenation( [
"LeftCocartesianCodistributivityFactoringWithGivenObjects",
"RightCocartesianCodistributivityFactoringWithGivenObjects",
],
CAP_INTERNAL_CONSTRUCTIVE_CATEGORIES_RECORD.IsCocartesianCategory,
CAP_INTERNAL_CONSTRUCTIVE_CATEGORIES_RECORD.IsCartesianCategory );
