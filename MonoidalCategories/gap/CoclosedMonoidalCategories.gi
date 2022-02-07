# SPDX-License-Identifier: GPL-2.0-or-later
# MonoidalCategories: Monoidal and monoidal (co)closed categories
#
# Implementations
#

####################################
# Convenience Methods
####################################

##
InstallMethod( InternalCoHom,
        [ IsCapCategoryObject, IsCapCategoryObject ],
        
  InternalCoHomOnObjects );

##
InstallMethod( InternalCoHom,
        [ IsCapCategoryMorphism, IsCapCategoryMorphism ],
        
  InternalCoHomOnMorphisms );

##
InstallMethod( InternalCoHom,
        [ IsCapCategoryObject, IsCapCategoryMorphism ],
        
  function( a, beta )
    
    return InternalCoHomOnMorphisms( IdentityMorphism( a ), beta );
    
end );

##
InstallMethod( InternalCoHom,
        [ IsCapCategoryMorphism, IsCapCategoryObject ],
        
  function( alpha, b )
    
    return InternalCoHomOnMorphisms( alpha, IdentityMorphism( b ) );
    
end );
