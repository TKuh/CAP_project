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
        src_template := "NumberRows( additive_closure_morphism )",
        dst_template := "Length( ObjectList( Source( additive_closure_morphism ) ) )",
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

# PreCompose( alpha, KroneckerDelta( ... ) )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "alpha", "index1", "index2", "value_if_equal", "value_if_not_equal" ],
        src_template := "PreCompose( cat, alpha, KroneckerDelta( index1, index2, value_if_equal, value_if_not_equal ) )",
        dst_template := "KroneckerDelta( index1, index2, PreCompose( cat, alpha, value_if_equal ), PreCompose( cat, alpha, value_if_not_equal ) )",
    )
);

# PreCompose( KroneckerDelta( ... ), alpha )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "alpha", "index1", "index2", "value_if_equal", "value_if_not_equal" ],
        src_template := "PreCompose( cat, KroneckerDelta( index1, index2, value_if_equal, value_if_not_equal ), alpha )",
        dst_template := "KroneckerDelta( index1, index2, PreCompose( cat, value_if_equal, alpha ), PreCompose( cat, value_if_not_equal, alpha ) )",
    )
);

# PreCompose( alpha, IdentityMorphism( ... ) )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "alpha", "object" ],
        variable_filters := [ IsDummyCategory, IsDummyCategoryMorphism, IsDummyCategoryObject ],
        src_template := "PreCompose( cat, alpha, IdentityMorphism( cat, object ) )",
        dst_template := "alpha",
    )
);

# PreCompose( IdentityMorphism( ... ), alpha )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "alpha", "object" ],
        variable_filters := [ IsDummyCategory, IsDummyCategoryMorphism, IsDummyCategoryObject ],
        src_template := "PreCompose( cat, IdentityMorphism( cat, object ), alpha )",
        dst_template := "alpha",
    )
);

# PreCompose( alpha, ZeroMorphism( ... ) )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "alpha", "object1", "object2" ],
        variable_filters := [ IsDummyCategory, IsDummyCategoryMorphism, IsDummyCategoryObject, IsDummyCategoryObject ],
        src_template := "PreCompose( cat, alpha, ZeroMorphism( cat, object1, object2 ) )",
        dst_template := "ZeroMorphism( cat, Source( alpha ), object2 )",
    )
);

# PreCompose( ZeroMorphism( ... ), alpha )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "alpha", "object1", "object2" ],
        variable_filters := [ IsDummyCategory, IsDummyCategoryMorphism, IsDummyCategoryObject, IsDummyCategoryObject ],
        src_template := "PreCompose( cat, ZeroMorphism( cat, object1, object2 ), alpha )",
        dst_template := "ZeroMorphism( cat, object1, Range( alpha ) )",
    )
);

# SumOfMorphisms( List( ... , KroneckerDelta( ..., ..., value, 0 ) ) ) => value
# FIXME: this is only true if `i` and `other_index` loop over the same range
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "list", "other_index", "value", "object1", "object2" ],
        variable_filters := [ IsDummyCategory, IsList, IsInt, IsDummyCategoryMorphism, IsDummyCategoryObject, IsDummyCategoryObject ],
        src_template := "SumOfMorphisms( cat, List( list, i -> KroneckerDelta( i, other_index, value, ZeroMorphism( cat, object1, object2 ) ) ) )",
        dst_template := "(i -> value)(other_index)",
    )
);

# SumOfMorphisms( List( ... , KroneckerDelta( ..., ..., value, 0 ) ) ) => value
# FIXME: this is only true if `i` and `other_index` loop over the same range
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "list", "other_index", "value", "object1", "object2" ],
        variable_filters := [ IsDummyCategory, IsList, IsInt, IsDummyCategoryMorphism, IsDummyCategoryObject, IsDummyCategoryObject ],
        src_template := "SumOfMorphisms( cat, List( list, i -> KroneckerDelta( other_index, i, value, ZeroMorphism( cat, object1, object2 ) ) ) )",
        dst_template := "(i -> value)(other_index)",
    )
);

# alpha ~ alpha => true
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "mor" ],
        src_template := "mor ∼ mor",
        dst_template := "true",
        enhanced_syntax := true,
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

dummy := DummyCategory( rec(
    list_of_operations_to_install := [
        "IsCongruentForMorphisms",
        "PreCompose",
        "AdditionForMorphisms",
        "IdentityMorphism",
        "ZeroMorphism",
        "IsZeroForMorphisms",
    ],
    properties := [
        "IsAbCategory",
    ],
) );

StopCompilationAtCategory( dummy );
#StopCompilationAtPrimitivelyInstalledOperationsOfCategory( dummy );


proposition := function ( cat, alpha )
    
    return IsCongruentForMorphisms( cat,
        PreCompose( cat, alpha, IdentityMorphism( cat, Range( alpha ) ) ),
        alpha
    );
    
end;

Display( CapJitCompiledFunction( proposition, AdditiveClosure( dummy ), [ "category", "morphism" ], "bool" ) );

proposition := function ( cat, alpha )
    
    return IsCongruentForMorphisms( cat,
        PreCompose( cat, IdentityMorphism( cat, Source( alpha ) ), alpha ),
        alpha
    );
    
end;

Display( CapJitCompiledFunction( proposition, AdditiveClosure( dummy ), [ "category", "morphism" ], "bool" ) );
