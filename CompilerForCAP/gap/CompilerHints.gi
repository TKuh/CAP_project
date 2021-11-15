# SPDX-License-Identifier: GPL-2.0-or-later
# CompilerForCAP: Speed up computations in CAP categories
#
# Implementations
#

InstallGlobalFunction( CapJitAppliedCompilerHints, function ( tree, category )
    
    tree := CapJitReplacedSourceAndRangeAttributes( tree, category );
    
    # call this at the end because previous functions might want to access the global variables
    tree := CapJitReplacedGlobalVariablesByCategoryAttributes( tree, category );
    
    return tree;
    
end );

InstallGlobalFunction( CapJitReplacedSourceAndRangeAttributes, function ( tree, category )
  local pre_func, additional_arguments_func;
    
    # functions will be modified in-place
    tree := StructuralCopy( tree );
    
    pre_func := function ( tree, func_stack )
      local func, args, category, object_attribute_name, morphism_attribute_name, source_attribute_getter_name, range_attribute_getter_name, morphism_attribute_position, morphism_attribute_value, id, new_variable_name, source_args, source_attribute_position, range_args, range_attribute_position;
        
        func := Last( func_stack );
        
        if CapJitIsCallToGlobalFunction( tree, "ObjectifyMorphismWithSourceAndRangeForCAPWithAttributes" ) then
            
            args := tree.args;
            
            if args.2.type = "EXPR_REF_GVAR" then
                
                category := ValueGlobal( args.2.gvar );
                
                Assert( 0, IsCapCategory( category ) );
                
                if IsBound( category!.compiler_hints ) and IsBound( category!.compiler_hints.source_and_range_attributes_from_morphism_attribute ) then
                    
                    object_attribute_name := category!.compiler_hints.source_and_range_attributes_from_morphism_attribute.object_attribute_name;
                    morphism_attribute_name := category!.compiler_hints.source_and_range_attributes_from_morphism_attribute.morphism_attribute_name;
                    source_attribute_getter_name := category!.compiler_hints.source_and_range_attributes_from_morphism_attribute.source_attribute_getter_name;
                    range_attribute_getter_name := category!.compiler_hints.source_and_range_attributes_from_morphism_attribute.range_attribute_getter_name;
                    
                    # check if either Source or Range are constructed inplace
                    if CapJitIsCallToGlobalFunction( args.3, "ObjectifyObjectForCAPWithAttributes" ) or CapJitIsCallToGlobalFunction( args.4, "ObjectifyObjectForCAPWithAttributes" ) then
                        
                        morphism_attribute_position := PositionProperty( args, x -> x.type = "EXPR_REF_GVAR" and x.gvar = morphism_attribute_name );
                        
                        if morphism_attribute_position = fail then
                            
                            # COVERAGE_IGNORE_NEXT_LINE
                            Error( "cannot find morphism attribute" );
                            
                        fi;
                        
                        Assert( 0, IsOddInt( morphism_attribute_position ) and morphism_attribute_position > 4 and morphism_attribute_position < args.length );
                        
                        morphism_attribute_value := args.(morphism_attribute_position + 1);
                        
                        # search for an unused id
                        id := 1;
                        while ForAny( func.nams, name -> EndsWith( name, Concatenation( "_", String( id ) ) ) ) do
                            
                            id := id + 1;
                            
                        od;
                        
                        new_variable_name := Concatenation( "morphism_attr_", String( id ) );
                        
                        func.nams := Concatenation( func.nams, [ new_variable_name ] );
                        
                        Assert( 0, IsDuplicateFreeList( func.nams ) );
                        
                        CapJitAddBinding( func.bindings, new_variable_name, morphism_attribute_value );
                        
                        args.(morphism_attribute_position + 1) := rec(
                            type := "EXPR_REF_FVAR",
                            func_id := func.id,
                            name := new_variable_name,
                        );
                        
                        if CapJitIsCallToGlobalFunction( args.3, "ObjectifyObjectForCAPWithAttributes" ) then
                            
                            source_args := args.3.args;
                            
                            source_attribute_position := PositionProperty( source_args, x -> x.type = "EXPR_REF_GVAR" and x.gvar = object_attribute_name );
                            
                            if source_attribute_position = fail then
                                
                                # COVERAGE_IGNORE_NEXT_LINE
                                Error( "cannot find source attribute" );
                                
                            fi;
                            
                            Assert( 0, IsOddInt( source_attribute_position ) and source_attribute_position > 2 and source_attribute_position < source_args.length );
                            
                            # ignore simple expression, e.g. integers
                            if not source_args.(source_attribute_position + 1).type in [ "EXPR_INT", "EXPR_STRING", "EXPR_CHAR", "EXPR_TRUE", "EXPR_FALSE", "EXPR_REF_GVAR" ] then
                                
                                source_args.(source_attribute_position + 1) := rec(
                                    type := "EXPR_FUNCCALL",
                                    funcref := rec(
                                        type := "EXPR_REF_GVAR",
                                        gvar := source_attribute_getter_name,
                                    ),
                                    args := AsSyntaxTreeList( [
                                        rec(
                                            type := "EXPR_REF_FVAR",
                                            func_id := func.id,
                                            name := new_variable_name,
                                        ),
                                    ] ),
                                );
                                
                            fi;
                            
                        fi;
                        
                        if CapJitIsCallToGlobalFunction( args.4, "ObjectifyObjectForCAPWithAttributes" ) then
                            
                            range_args := args.4.args;
                            
                            range_attribute_position := PositionProperty( range_args, x -> x.type = "EXPR_REF_GVAR" and x.gvar = object_attribute_name );
                            
                            if range_attribute_position = fail then
                                
                                # COVERAGE_IGNORE_NEXT_LINE
                                Error( "cannot find range attribute" );
                                
                            fi;
                            
                            Assert( 0, IsOddInt( range_attribute_position ) and range_attribute_position > 2 and range_attribute_position < range_args.length );
                            
                            # ignore simple expression, e.g. integers
                            if not range_args.(range_attribute_position + 1).type in [ "EXPR_INT", "EXPR_STRING", "EXPR_CHAR", "EXPR_TRUE", "EXPR_FALSE", "EXPR_REF_GVAR" ] then
                                
                                range_args.(range_attribute_position + 1) := rec(
                                    type := "EXPR_FUNCCALL",
                                    funcref := rec(
                                        type := "EXPR_REF_GVAR",
                                        gvar := range_attribute_getter_name,
                                    ),
                                    args := AsSyntaxTreeList( [
                                        rec(
                                            type := "EXPR_REF_FVAR",
                                            func_id := func.id,
                                            name := new_variable_name,
                                        ),
                                    ] ),
                                );
                                
                            fi;
                            
                        fi;
                        
                    fi;
                    
                fi;
                
            fi;
            
        fi;
        
        return tree;
        
    end;
    
    additional_arguments_func := function ( tree, key, func_stack )
        
        if tree.type = "EXPR_DECLARATIVE_FUNC" then
            
            return Concatenation( func_stack, [ tree ] );
            
        else
            
            return func_stack;
            
        fi;
        
    end;
    
    return CapJitIterateOverTree( tree, pre_func, CapJitResultFuncCombineChildren, additional_arguments_func, [ ] );
    
end );

InstallGlobalFunction( CapJitReplacedGlobalVariablesByCategoryAttributes, function ( tree, category )
  local categories_in_tower, categories_in_tower_getters, category_attribute_values, category_attribute_values_getters, i, cat, cat_getter, attribute_names, value, pre_func, name;
    
    categories_in_tower := [ category ];
    categories_in_tower_getters := [
        rec(
            type := "EXPR_REF_FVAR",
            func_id := tree.id,
            name := tree.nams[1],
        )
    ];
    
    category_attribute_values := [ ];
    category_attribute_values_getters := [ ];
    
    i := 1;
    
    while i <= Length( categories_in_tower ) do
        
        cat := categories_in_tower[i];
        cat_getter := categories_in_tower_getters[i];
        
        if IsBound( cat!.compiler_hints ) and IsBound( cat!.compiler_hints.category_attribute_names ) then
            
            attribute_names := ShallowCopy( cat!.compiler_hints.category_attribute_names );
            
        else
            
            attribute_names := [ ];
            
        fi;
        
        # add some attributes by default
        
        if HasObjectType( category ) then
            
            Add( attribute_names, "ObjectType" );
            
        fi;
        
        if HasMorphismType( category ) then
            
            Add( attribute_names, "MorphismType" );
            
        fi;
        
        if HasRangeCategoryOfHomomorphismStructure( category ) then
            
            Add( attribute_names, "RangeCategoryOfHomomorphismStructure" );
            
        fi;
        
        for name in attribute_names do
            
            value := ValueGlobal( name )( cat );
            
            if IsCapCategory( value ) and not ForAny( categories_in_tower, c -> IsIdenticalObj( c, value ) ) then
                
                Add( categories_in_tower, value );
                Add( categories_in_tower_getters,
                    rec(
                        type := "EXPR_FUNCCALL",
                        funcref := rec(
                            type := "EXPR_REF_GVAR",
                            gvar := name,
                        ),
                        args := AsSyntaxTreeList( [
                            cat_getter
                        ] ),
                    )
                );
                
            else
                
                Add( category_attribute_values, value );
                Add( category_attribute_values_getters,
                    rec(
                        type := "EXPR_FUNCCALL",
                        funcref := rec(
                            type := "EXPR_REF_GVAR",
                            gvar := name,
                        ),
                        args := AsSyntaxTreeList( [
                            cat_getter
                        ] ),
                    )
                );
                
            fi;
            
        od;
        
        i := i + 1;
        
    od;
    
    pre_func := function ( tree, additional_arguments )
      local pos;
        
        if tree.type = "EXPR_REF_GVAR" then
            
            # try to find the value of the global variable in categories_in_tower
            pos := PositionProperty( categories_in_tower, c -> IsIdenticalObj( c, ValueGlobal( tree.gvar ) ) );
            
            if pos <> fail then
                
                return categories_in_tower_getters[pos];
                
            fi;
            
            # try to find the value of the global variable in category_attribute_values
            pos := PositionProperty( category_attribute_values, v -> IsIdenticalObj( v, ValueGlobal( tree.gvar ) ) );
            
            if pos <> fail then
                
                return category_attribute_values_getters[pos];
                
            fi;
            
        fi;
        
        return tree;
        
    end;
    
    return CapJitIterateOverTree( tree, pre_func, CapJitResultFuncCombineChildren, ReturnTrue, true );
    
end );
