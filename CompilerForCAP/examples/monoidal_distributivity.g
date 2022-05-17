LoadPackage( "CompilerForCAP" );
LoadPackage( "MonoidalCategories" );

CapJitDisableDataTypeInference( );
CapJitEnableProofAssistantMode( );

# A ---> B_1 ⊕ ... B_n ---> C => Sum( ... )
# separate proof: write UniversalMorphismFromDirect as a sum involving the projections
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "diagram", "source", "range", "components1", "components2" ],
        src_template := "PreCompose( cat, UniversalMorphismIntoDirectSum( cat, diagram, source, components1 ), UniversalMorphismFromDirectSum( cat, diagram, range, components2 ) )",
        dst_template := "Sum( ListN( components1, components2, { x, y } -> PreCompose( cat, x, y ) ) )",
        new_funcs := [ [ "x", "y" ] ],
    )
);

# functoriality of tensor product
#CapJitAddLogicTemplate(
#    rec(
#        variable_names := [ "cat", "obj1", "obj2" ],
#        src_template := "TensorProductOnMorphisms( cat, IdentityMorphism( cat, obj1 ), IdentityMorphism( cat, obj2 ) )",
#        dst_template := "IdentityMorphism( cat, TensorProductOnObjects( cat, obj1, obj2 ) )",
#    )
#);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "obj1", "obj2" ],
        src_template := "id_{obj1} ⊗_1 id_{obj2}",
        dst_template := "id_{obj1 ⊗_0 obj2}",
        enhanced_syntax := true,
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "alpha", "beta", "gamma", "delta" ],
        src_template := "{alpha ⊗_1 beta} ⋅ {gamma ⊗_1 delta}",
        dst_template := "{alpha ⋅ gamma} ⊗_1 {beta ⋅ delta}",
        enhanced_syntax := true,
    )
);

# WARNING: only in IsAbMonoidalCategory: tensor product commutes with sums of morphisms
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list", "cat", "constant", "dependent_on_x" ],
        src_template := "Sum( List( list, x -> {constant ⊗_1 dependent_on_x} ) )",
        dst_template := "constant ⊗_1 Sum( List( list, x -> dependent_on_x ) )",
        enhanced_syntax := true,
    )
);

# id * id => id
#CapJitAddLogicTemplate(
#    rec(
#        variable_names := [ "cat", "obj" ],
#        src_template := "PreCompose( cat, IdentityMorphism( cat, obj ), IdentityMorphism( cat, obj ) )",
#        dst_template := "IdentityMorphism( cat, obj )",
#    )
#);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "obj" ],
        src_template := "id_{obj} ⋅ id_{obj}",
        dst_template := "id_{obj}",
        enhanced_syntax := true,
    )
);

# Sum( pi_i * iota_i ) => id
# separate proof: precompose with injections and postcompose with projections
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "list" ],
        src_template := "Sum( List( [ 1 .. Length( list ) ], x -> {ProjectionInFactorOfDirectSum( cat, list, x ) ⋅ InjectionOfCofactorOfDirectSum( cat, list, x )} ) )",
        dst_template := "id_{DirectSum( cat, list )}",
        enhanced_syntax := true,
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

dummy := DummyCategory( rec(
    list_of_operations_to_install := [
        "IsCongruentForMorphisms",
        "PreCompose",
        "IdentityMorphism",
        "DirectSum",
        "ProjectionInFactorOfDirectSum",
        "InjectionOfCofactorOfDirectSum",
        "UniversalMorphismIntoDirectSum",
        "UniversalMorphismFromDirectSum",
        "TensorProductOnObjects",
        "TensorProductOnMorphisms",
    ],
    properties := [
        "IsAdditiveCategory",
        "IsMonoidalCategory",
    ],
) );

StopCompilationAtPrimitivelyInstalledOperationsOfCategory( dummy );

# LeftDistributivityExpanding * LeftDistributivityFactoring
func := function ( cat, a, list )
    
    return IsCongruentForMorphisms( cat,
        PreCompose( cat, LeftDistributivityExpanding( cat, a, list ), LeftDistributivityFactoring( cat, a, list ) ),
        IdentityMorphism( cat, TensorProductOnObjects( cat, a, DirectSum( cat, list ) ) )
    );
    
end;

Display( CapJitCompiledFunction( func, dummy ) );
# function ( cat_1, a_1, list_1 )
#     return true;
# end






# PreComposeList for literal lists => PreCompose
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "mor1", "mor2", "mor3" ],
        src_template := "PreComposeList( cat, [ mor1, mor2, mor3 ] )",
        dst_template := "PreCompose( cat, PreCompose( cat, mor1, mor2 ), mor3 )",
    )
);

# PreCompose( mor, id ) => mor
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "mor", "obj" ],
        src_template := "mor ⋅ id_{obj}",
        dst_template := "mor",
        enhanced_syntax := true,
    )
);

# check equality of two morphisms from and into direct sum componentwise
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "mor", "list" ],
        src_template := "mor ∼ id_{DirectSum( cat, list )}",
        dst_template := "ForAll( [ 1 .. Length( list ) ], i -> ForAll( [ 1 .. Length( list ) ], j -> {PreComposeList( cat, [ InjectionOfCofactorOfDirectSum( cat, list, i ), mor, ProjectionInFactorOfDirectSum( cat, list, j ) ] ) ∼ PreComposeList( cat, [ InjectionOfCofactorOfDirectSum( cat, list, i ), id_{DirectSum( cat, list )}, ProjectionInFactorOfDirectSum( cat, list, j ) ] ) } ) )",
        new_funcs := [ [ "i" ], [ "j" ] ],
        enhanced_syntax := true,
    )
);

# injection * universal morphism from => component
# HACK: we have to detect this in a nested PreCompose
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "diagram", "index", "test_object", "components", "mor" ],
        src_template := "InjectionOfCofactorOfDirectSum( cat, diagram, index ) ⋅ {UniversalMorphismFromDirectSum( cat, diagram, test_object, components ) ⋅ mor}",
        dst_template := "components[index] ⋅ mor",
        enhanced_syntax := true,
    )
);

# universal morphism into * projection => component
# HACK: we have to detect this in a nested PreCompose
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "mor", "diagram", "test_object", "components", "index" ],
        src_template := "{mor ⋅ UniversalMorphismIntoDirectSum( cat, diagram, test_object, components )} ⋅ ProjectionInFactorOfDirectSum( cat, diagram, index )",
        dst_template := "mor ⋅ components[index]",
        enhanced_syntax := true,
    )
);

# HACK: resolve literal_list[index] in a special case
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "list1", "func1", "index1", "list2", "func2", "index2" ],
        src_template := "List( list1, func1 )[index1] ⋅ List( list2, func2 )[index2]",
        dst_template := "func1( list1[index1] ) ⋅ func2( list2[index2] )",
        enhanced_syntax := true,
    )
);

KroneckerDelta := function ( i, j, value_if_equal, value_if_not_equal )
    
    if i = j then
        
        return value_if_equal;
        
    else
        
        return value_if_not_equal;
        
    fi;
    
end;

# injection * projection = id or zero
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "diagram", "index_1", "index_2" ],
        src_template := "InjectionOfCofactorOfDirectSum( cat, diagram, index_1 ) ⋅ ProjectionInFactorOfDirectSum( cat, diagram, index_2 )",
        dst_template := "KroneckerDelta( index_1, index_2, id_{diagram[index_1]}, ZeroMorphism( cat, diagram[index_1], diagram[index_2] ) )",
        enhanced_syntax := true,
    )
);

# WARNING: only in IsAbMonoidalCategory: TensorProduct( id, id ) = id, TensorProduct( id, 0 ) = 0
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "obj", "diagram", "index_1", "index_2" ],
        src_template := "id_{obj} ⊗_1 KroneckerDelta( index_1, index_2, IdentityMorphism( cat, diagram[index_1] ), ZeroMorphism( cat, diagram[index_1], diagram[index_2] ) )",
        dst_template := "KroneckerDelta( index_1, index_2, id_{obj ⊗_0 diagram[index_1]}, ZeroMorphism( cat, {obj ⊗_0 diagram[index_1]}, {obj ⊗_0 diagram[index_2]} ) )",
        enhanced_syntax := true,
    )
);

# HACK: push TensorProductOnObjects down
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "obj", "list", "index" ],
        src_template := "obj ⊗_0 list[index]",
        dst_template := "List( list, l -> {obj ⊗_0 l} )[index]",
        new_funcs := [ [ "l" ] ],
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

# LeftDistributivityFactoring * LeftDistributivityExpanding
func := function ( cat, a, list )
    
    return IsCongruentForMorphisms( cat,
        PreCompose( cat, LeftDistributivityFactoring( cat, a, list ), LeftDistributivityExpanding( cat, a, list ) ),
        IdentityMorphism( cat, DirectSum( cat, List( list, l -> TensorProductOnObjects( cat, a, l ) ) ) )
    );
    
end;

Display( CapJitCompiledFunction( func, dummy ) );
# function ( cat_1, a_1, list_1 )
#     return true;
# end
