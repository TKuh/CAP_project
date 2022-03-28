LoadPackage( "FreydCategoriesForCAP" );

CapJitEnableProofAssistantMode( );

# additive_closure_morphism[i, j] => MorphismMatrix( additive_closure_morphism )[i, j]
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "source", "range", "morphism_matrix", "row", "column" ],
        # TODO
        #variable_filters := [ IsAdditiveClosureMorphism, IsInt, IsInt ],
        src_template := "ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes( rec( ), cat, source, range, MorphismMatrix, morphism_matrix )[row, column]",
        dst_template := "morphism_matrix[row, column]",
    )
);

# very specific
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "end1", "end2", "func", "row", "col" ],
        src_template := "List( [ 1 .. end1 ], x -> List( [ 1 .. end2 ], func ) )[row, col]",
        dst_template := "( x -> func( col ) )( row )",
    )
);

# NumberRows( additive_closure_morphism ) => Length( ObjectList( Source( additive_closure_morphism ) ) )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "source", "range", "morphism_matrix" ],
        # TODO
        #variable_filters := [ IsAdditiveClosureMorphism ],
        src_template := "NumberRows( ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes( rec( ), cat, source, range, MorphismMatrix, morphism_matrix ) )",
        dst_template := "Length( ObjectList( source ) )",
    )
);

# NumberColumns( additive_closure_morphism ) => Length( ObjectList( Range( additive_closure_morphism ) ) )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "source", "range", "morphism_matrix" ],
        # TODO
        #variable_filters := [ IsAdditiveClosureMorphism ],
        src_template := "NumberColumns( ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes( rec( ), cat, source, range, MorphismMatrix, morphism_matrix ) )",
        dst_template := "Length( ObjectList( range ) )",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "additive_closure_morphism" ],
        variable_filters := [ IsAdditiveClosureMorphism ],
        src_template := "NumberColumns( additive_closure_morphism )",
        dst_template := "Length( ObjectList( Range( additive_closure_morphism ) ) )",
    )
);

# PreCompose is linear in the second component
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "value", "list" ],
        src_template := "PreCompose( cat, value, SumOfMorphisms( cat, list ) )",
        dst_template := "SumOfMorphisms( cat, List( list, x -> PreCompose( cat, value, x ) ) )",
        new_funcs := [ [ "x" ] ],
    )
);

# PreCompose is linear in the first component
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "value", "list" ],
        src_template := "PreCompose( cat, SumOfMorphisms( cat, list ), value )",
        dst_template := "SumOfMorphisms( cat, List( list, x -> PreCompose( cat, x, value ) ) )",
        new_funcs := [ [ "x" ] ],
    )
);

# make nested PreCompose left-balanced
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "value1", "value2", "value3" ],
        variable_filters := [ IsDummyCategory, IsDummyCategoryMorphism, IsDummyCategoryMorphism, IsDummyCategoryMorphism ],
        src_template := "PreCompose( cat, value1, PreCompose( cat, value2, value3 ) )",
        dst_template := "PreCompose( cat, PreCompose( cat, value1, value2 ), value3 )",
        #debug := true,
    )
);

# finite sums can be interchanged
# FIXME: this rule is wrong
# cannot yet detect if value1 = value2
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "list1", "list2", "value1", "value2" ],
        src_template := "IsCongruentForMorphisms( cat, SumOfMorphisms( cat, List( list1, x -> SumOfMorphisms( cat, List( list2, y -> value1 ) ) ) ), SumOfMorphisms( cat, List( list2, y -> SumOfMorphisms( cat, List( list1, x -> value2 ) ) ) ) )",
        dst_template := "true",
    )
);

# expr <> expr => false
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "expr" ],
        src_template := "expr <> expr",
        dst_template := "false",
    )
);

# ForAll( list, l -> true ) => true
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list" ],
        src_template := "ForAll( list, l -> true )",
        dst_template := "true",
    )
);

CapJitAddTypeSignature( "IsCongruentForMorphisms", [ IsCapCategory, IsCapCategoryMorphism, IsCapCategoryMorphism ], IsBool );

CapJitAddTypeSignature( "PreCompose", [ IsCapCategory, IsCapCategoryMorphism, IsCapCategoryMorphism ], function ( input_types )
    
    return input_types[2];
    
end );

CapJitAddTypeSignature( "AdditionForMorphisms", [ IsCapCategory, IsCapCategoryMorphism, IsCapCategoryMorphism ], function ( input_types )
    
    return input_types[2];
    
end );

dummy := DummyCategory( rec(
    list_of_operations_to_install := [
        "IsCongruentForMorphisms",
        "PreCompose",
        "AdditionForMorphisms",
    ],
    properties := [
        "IsAbCategory",
    ],
) );

StopCompilationAtPrimitivelyInstalledOperationsOfCategory( dummy );


proposition := function ( cat, alpha, beta, gamma )
    
    return IsCongruentForMorphisms( cat,
        PreCompose( cat, PreCompose( cat, alpha, beta ), gamma ),
        PreCompose( cat, alpha, PreCompose( cat, beta, gamma ) )
    );
    
end;

Display( CapJitCompiledFunction( proposition, AdditiveClosure( dummy ), [ "category", "morphism", "morphism", "morphism" ], "bool" ) );
