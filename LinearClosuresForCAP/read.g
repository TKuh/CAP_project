# SPDX-License-Identifier: GPL-2.0-or-later
# LinearClosuresForCAP: Linear closures
#
# Reading the implementation part of the package.
#

ReadPackage( "LinearClosuresForCAP", "gap/LinearClosure.gi" );

ReadPackage( "LinearClosuresForCAP", "gap/LinearClosureForFiniteSkeletalDiscreteCategory.gi" );

ReadPackage( "LinearClosuresForCAP", "gap/TwistedLinearClosure.gi" );

#= comment for Julia (Groups are not available in Julia)
ReadPackage( "LinearClosuresForCAP", "gap/LinearClosureForGroupAsCategory.gi" );
# =#

# In GAP, `gap/HomomorphismStructure.gi` is loaded only if `FinSetsForCAP` is marked for loading (see PackageInfo.g).
# In Julia, `FinSetsForCAP` is always a dependency, so we can include this file unconditionally.
#% G2J:julia-only ReadPackage( "LinearClosuresForCAP", "gap/HomomorphismStructure.gi" );

ReadPackage( "LinearClosuresForCAP", "gap/AdditiveClosureOfLinearClosureOfFiniteSkeletalDiscreteCategory.gi" );

# ReadPackage( "LinearClosuresForCAP", "gap/CoproductOfCategoryOfRows.gi" );

# ReadPackage( "LinearClosuresForCAP", "gap/CoproductOfCategoryOfRowsWithSparseDatastructure.gi" );

