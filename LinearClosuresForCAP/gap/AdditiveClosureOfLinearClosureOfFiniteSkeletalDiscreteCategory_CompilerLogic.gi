# SPDX-License-Identifier: GPL-2.0-or-later
# LinearClosuresForCAP: Linear closures
#
# Declarations
#

# UnionOfRowsListList
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "nr_cols", "listlist", "func" ],
        src_template := "List( UnionOfRowsListList( nr_cols, listlist ), row -> List( row, func ) )",
        dst_template := "UnionOfRowsListList( nr_cols, List( listlist, list -> List( list, new_row -> List( new_row, func ) ) ) )",
        new_funcs := [ [ "list" ], [ "new_row" ] ],
    )
);

# UnionOfColumnsListList
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "nr_rows", "listlist", "func" ],
        src_template := "List( UnionOfColumnsListList( nr_rows, listlist ), row -> List( row, func ) )",
        dst_template := "UnionOfColumnsListList( nr_rows, List( listlist, list -> List( list, new_row -> List( new_row, func ) ) ) )",
        new_funcs := [ [ "list" ], [ "new_row" ] ],
    )
);

# List( list, x -> const ) => ListWithIdenticalEntries
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list", "const" ],
        src_template := "List( list, x -> const )",
        dst_template := "ListWithIdenticalEntries( Length( list ), const )",
    )
);
