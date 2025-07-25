
# BlockDiagonalMatrix( ListOfMatrices( mor ) ) -> ListOfMatrices( mor )
CapJitAddLogicTemplate(
    rec(
        variable_filters := [ IsAdditiveClosureOfObjectFiniteDisconnectedCategory, IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategory, IsBigInt ],
        variable_names := [ "DAC", "beta", "nr_objects" ],
        src_template := "COMPILATION_HELPER_AdditiveClosureOfObjectFiniteDisconnectedCategory_BlockDiagonalMatrix( DAC, nr_objects, NrSummandsAndMultiplicities( Source( beta ) )[2], NrSummandsAndMultiplicities( Range( beta ) )[2], ListOfMatrices( beta ) )",
        dst_template := "ListOfMatrices( beta )",
        # new_funcs := [ [ "list" ], [ "new_row" ] ],
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_filters := [ IsList ],
        variable_names := [ "list_of_matrices" ],
        src_template := "List( list_of_matrices, matrix -> List( matrix, SupportMorphisms ) )",
        dst_template := "List( list_of_matrices, matrix -> List( matrix, row -> List( row, element -> SupportMorphisms( element ) ) ) )",
        new_funcs := [ [ "matrix" ], [ "row" ], [ "element" ] ],
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_filters := [ IsList ],
        variable_names := [ "list_of_matrices" ],
        src_template := "List( list_of_matrices, matrix -> List( matrix, CoefficientsList ) )",
        dst_template := "List( list_of_matrices, matrix -> List( matrix, row -> List( row, element -> CoefficientsList( element ) ) ) )",
        new_funcs := [ [ "matrix" ], [ "row" ], [ "element" ] ],
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_filters := [ IsList ],
        variable_names := [ "list_of_matrices" ],
        src_template := "List( list_of_matrices, matrix -> List( matrix, Source ) )",
        dst_template := "List( list_of_matrices, matrix -> List( matrix, row -> List( row, element -> Source( element ) ) ) )",
        new_funcs := [ [ "matrix" ], [ "row" ], [ "element" ] ],
    )
);

# CapJitAddLogicTemplate(
#     rec(
#         variable_filters := [ IsList ],
#         variable_names := [ "list_of_matrices" ],
#         src_template := "List( list_of_matrices, matrix -> List( matrix, Target ) )",
#         dst_template := "List( list_of_matrices, matrix -> List( matrix, row -> List( row, element -> Target( element ) ) ) )",
#         new_funcs := [ [ "matrix" ], [ "row" ], [ "element" ] ],
#     )
# );

