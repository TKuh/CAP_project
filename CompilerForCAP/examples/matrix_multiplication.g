LoadPackage( "FreydCategoriesForCAP" );

ReadPackage( "FreydCategoriesForCAP",
    "gap/CategoryOfRowsAsAdditiveClosureOfRingAsCategory_CompilerLogic.gi");


CapJitAddLogicTemplate(
    rec(
        variable_names := [ "matrix", "func", "row", "col" ],
        src_template := "List( EntriesOfHomalgMatrixAsListList( matrix ), x -> List( x, func ) )[row][col]",
        dst_template := "func( matrix[row, col] )",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list_list", "nr_rows", "nr_cols", "ring", "row_index", "col_index" ],
        src_template := "HomalgMatrixListList( list_list, nr_rows, nr_cols, ring )[row_index, col_index]",
        dst_template := "list_list[row_index][col_index]",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list", "func", "row", "col" ],
        src_template := "List( list, func )[row][col]",
        dst_template := "func( list[row] )[col]",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list_list", "nr_rows", "nr_cols", "ring" ],
        src_template := "NumberRows( HomalgMatrixListList( list_list, nr_rows, nr_cols, ring ) )",
        dst_template := "nr_rows",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list_list", "nr_rows", "nr_cols", "ring" ],
        src_template := "NumberColumns( HomalgMatrixListList( list_list, nr_rows, nr_cols, ring ) )",
        dst_template := "nr_cols",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "morphism" ],
        src_template := "NrRows( UnderlyingMatrix( morphism ) )",
        dst_template := "RankOfObject( Source( morphism ) )",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "morphism" ],
        src_template := "NrCols( UnderlyingMatrix( morphism ) )",
        dst_template := "RankOfObject( Range( morphism ) )",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list", "func", "index" ],
        src_template := "List( list, func )[index]",
        dst_template := "func( list[index] )",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "value", "list" ],
        src_template := "value * Iterated( list, { x, y } -> x + y )",
        dst_template := "Iterated( List( list, x -> value * x ), { x, y } -> x + y )",
        new_funcs := [ [ "x" ] ],
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "value", "list" ],
        src_template := "Iterated( list, { x, y } -> x + y ) * value",
        dst_template := "Iterated( List( list, x -> x * value ), { x, y } -> x + y )",
        new_funcs := [ [ "x" ] ],
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "value1", "value2", "value3" ],
        src_template := "value1 * (value2 * value3)",
        dst_template := "(value1 * value2) * value3",
        debug := true,
    )
);


QQ := HomalgFieldOfRationals( );

cat := CategoryOfRowsAsAdditiveClosureOfRingAsCategory( QQ );

left_assoc := function ( cat, alpha, beta, gamma )
    
    return UnderlyingMatrix( PreCompose( cat, PreCompose( cat, alpha, beta ), gamma ) );
    
end;


right_assoc := function ( cat, alpha, beta, gamma )
    
    return UnderlyingMatrix( PreCompose( cat, alpha, PreCompose( cat, beta, gamma ) ) );
    
end;

compiled_left_assoc := CapJitCompiledFunction( left_assoc, cat );
compiled_right_assoc := CapJitCompiledFunction( right_assoc, cat );

obj2 := ObjectifyObjectForCAPWithAttributes( rec( ), cat, RankOfObject, 2 );
obj3 := ObjectifyObjectForCAPWithAttributes( rec( ), cat, RankOfObject, 3 );

alpha := ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes( rec( ), cat, obj2, obj2, UnderlyingMatrix, HomalgMatrix( [ 0, 1, 2, 3 ], 2, 2, QQ ) );
beta  := ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes( rec( ), cat, obj2, obj2, UnderlyingMatrix, HomalgMatrix( [ 4, 5, 6, 7 ], 2, 2, QQ ) );
gamma := ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes( rec( ), cat, obj2, obj3, UnderlyingMatrix, HomalgMatrix( [ 8, 9, 0, 1, 2, 3 ], 2, 3, QQ ) );

Display( compiled_left_assoc );
Display( compiled_right_assoc );

Display( left_assoc( cat, alpha, beta, gamma ) );
Display( right_assoc( cat, alpha, beta, gamma ) );

Display( compiled_left_assoc( cat, alpha, beta, gamma ) );
Display( compiled_right_assoc( cat, alpha, beta, gamma ) );
