InstallValue( MONOIDAL_CATEGORIES_BASIC_METHOD_NAME_RECORD, rec(

TensorProductOnObjects := rec(
  filter_list := [ "category", "object", "object" ],
  return_type := "object" ),

TensorUnit := rec(
  filter_list := [ "category" ],
  return_type := "object" ),

) );

CAP_INTERNAL_ENHANCE_NAME_RECORD( MONOIDAL_CATEGORIES_BASIC_METHOD_NAME_RECORD );

CAP_INTERNAL_REGISTER_METHOD_NAME_RECORD_OF_PACKAGE( MONOIDAL_CATEGORIES_BASIC_METHOD_NAME_RECORD, "MonoidalCategories" );

CAP_INTERNAL_INSTALL_ADDS_FROM_RECORD( MONOIDAL_CATEGORIES_BASIC_METHOD_NAME_RECORD );
