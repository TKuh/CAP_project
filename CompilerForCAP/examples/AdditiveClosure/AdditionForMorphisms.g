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

# IsZeroForMorphisms( ZeroMorphism ) => true
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "object1", "object2" ],
        variable_filters := [ IsDummyCategory, IsDummyCategoryObject, IsDummyCategoryObject ],
        src_template := "IsZeroForMorphisms( cat, ZeroMorphism( cat, object1, object2 ) )",
        dst_template := "true",
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

proposition := function ( cat, object1, object2 )
    
    return IsZeroForMorphisms( cat, ZeroMorphism( cat, object1, object2 ) );
    
end;

Display( CapJitCompiledFunction( proposition, AdditiveClosure( dummy ), [ "category", "object", "object" ], "bool" ) );

# make AdditionForMorphisms left-balanced
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "alpha", "beta", "gamma" ],
        variable_filters := [ IsDummyCategory, IsDummyCategoryMorphism, IsDummyCategoryMorphism, IsDummyCategoryMorphism ],
        src_template := "AdditionForMorphisms( cat, alpha, AdditionForMorphisms( cat, beta, gamma ) )",
        dst_template := "AdditionForMorphisms( cat, AdditionForMorphisms( cat, alpha, beta ), gamma )",
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

proposition := function ( cat, alpha, beta, gamma )
    
    return IsCongruentForMorphisms( cat,
        AdditionForMorphisms( cat, AdditionForMorphisms( cat, alpha, beta ), gamma ),
        AdditionForMorphisms( cat, alpha, AdditionForMorphisms( cat, beta, gamma ) )
    );
    
end;

Display( CapJitCompiledFunction( proposition, AdditiveClosure( dummy ), [ "category", "morphism", "morphism", "morphism" ], "bool" ) );

# alpha + 0 ~ alpha
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "alpha", "object1", "object2" ],
        variable_filters := [ IsDummyCategory, IsDummyCategoryMorphism, IsDummyCategoryObject, IsDummyCategoryObject ],
        src_template := "AdditionForMorphisms( cat, alpha, ZeroMorphism( cat, object1, object2 ) )",
        dst_template := "alpha",
    )
);

proposition := function ( cat, alpha )
    
    return IsCongruentForMorphisms( cat,
        AdditionForMorphisms( cat, alpha, ZeroMorphism( cat, Source( alpha ), Range( alpha ) ) ),
        alpha
    );
    
end;

Display( CapJitCompiledFunction( proposition, AdditiveClosure( dummy ), [ "category", "morphism" ], "bool" ) );

# 0 + alpha ~ alpha
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "alpha", "object1", "object2" ],
        variable_filters := [ IsDummyCategory, IsDummyCategoryMorphism, IsDummyCategoryObject, IsDummyCategoryObject ],
        src_template := "AdditionForMorphisms( cat, ZeroMorphism( cat, object1, object2 ), alpha )",
        dst_template := "alpha",
    )
);

proposition := function ( cat, alpha )
    
    return IsCongruentForMorphisms( cat,
        AdditionForMorphisms( cat, ZeroMorphism( cat, Source( alpha ), Range( alpha ) ), alpha ),
        alpha
    );
    
end;

Display( CapJitCompiledFunction( proposition, AdditiveClosure( dummy ), [ "category", "morphism" ], "bool" ) );

# alpha + (-alpha) ~ 0
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "alpha" ],
        variable_filters := [ IsDummyCategory, IsDummyCategoryMorphism ],
        src_template := "AdditionForMorphisms( cat, alpha, AdditiveInverseForMorphisms( cat, alpha ) )",
        dst_template := "ZeroMorphism( cat, Source( alpha ), Range( alpha ) )",
    )
);

# Source( alpha[i, j] )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "alpha", "row", "col" ],
        variable_filters := [ IsAdditiveClosureMorphism, IsInt, IsInt ],
        src_template := "Source( alpha[row, col] )",
        dst_template := "ObjectList( Source( alpha ) )[row]",
    )
);

# Range( alpha[i, j] )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "alpha", "row", "col" ],
        variable_filters := [ IsAdditiveClosureMorphism, IsInt, IsInt ],
        src_template := "Range( alpha[row, col] )",
        dst_template := "ObjectList( Range( alpha ) )[col]",
    )
);

proposition := function ( cat, alpha )
    
    return IsCongruentForMorphisms( cat,
        AdditionForMorphisms( cat, alpha, AdditiveInverseForMorphisms( cat, alpha ) ),
        ZeroMorphism( cat, Source( alpha ), Range( alpha ) )
    );
    
end;

Display( CapJitCompiledFunction( proposition, AdditiveClosure( dummy ), [ "category", "morphism" ], "bool" ) );

# (-alpha) + alpha ~ 0
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "alpha" ],
        variable_filters := [ IsDummyCategory, IsDummyCategoryMorphism ],
        src_template := "AdditionForMorphisms( cat, AdditiveInverseForMorphisms( cat, alpha ), alpha )",
        dst_template := "ZeroMorphism( cat, Source( alpha ), Range( alpha ) )",
    )
);

proposition := function ( cat, alpha )
    
    return IsCongruentForMorphisms( cat,
        AdditionForMorphisms( cat, AdditiveInverseForMorphisms( cat, alpha ), alpha ),
        ZeroMorphism( cat, Source( alpha ), Range( alpha ) )
    );
    
end;

Display( CapJitCompiledFunction( proposition, AdditiveClosure( dummy ), [ "category", "morphism" ], "bool" ) );

# (-alpha) + alpha ~ 0
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "alpha", "beta" ],
        variable_filters := [ IsDummyCategory, IsDummyCategoryMorphism, IsDummyCategoryMorphism ],
        src_template := "IsCongruentForMorphisms( cat, AdditionForMorphisms( cat, alpha, beta ), AdditionForMorphisms( cat, beta, alpha ) )",
        dst_template := "true",
    )
);

# we have to teach CompilerForCAP that Source( alpha ) = Source( beta ) and Range( alpha ) = Range( beta ) (w.r.t. IsEqualForObjects)
proposition := function ( cat, alpha, beta )
    
    return IsCongruentForMorphisms( cat,
        AdditionForMorphisms( cat, alpha, beta ),
        AdditionForMorphisms( cat, beta, alpha )
    );
    
end;

Display( CapJitCompiledFunction( proposition, AdditiveClosure( dummy ), [ "category", "morphism", "morphism" ], "bool" ) );
