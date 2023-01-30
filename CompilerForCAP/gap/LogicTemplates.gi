# SPDX-License-Identifier: GPL-2.0-or-later
# CompilerForCAP: Speed up computations in CAP categories
#
# Implementations
#
BindGlobal( "CAP_JIT_LOGIC_TEMPLATES", [ ] );
InstallGlobalFunction( CapJitAddLogicTemplate, function ( template )
    
    # the logic template will later be enhanced in-place -> make a copy
    template := StructuralCopy( template );
    
    Add( CAP_JIT_LOGIC_TEMPLATES, template );
    
end );

CapJitAddLogicTemplateAndReturnLaTeXString := function ( template, cat, input_filters, connecting_symbol, args... )
  local suffix, src_template, dst_template, src_func, dst_func, src_string, dst_string, latex_string, name;
    
    if IsEmpty( args ) then
        
        suffix := "";
        
    elif Length( args ) = 1 then
        
        suffix := args[1];
        
    else
        
        Error( "CapJitAddLogicTemplateAndReturnLaTeXString must be called with at most two arguments" );
        
    fi;
    
    CapJitAddLogicTemplate( template );
    
    src_template := template.src_template;
    dst_template := template.dst_template;
    
    if IsBound( template.sublist_variable_names ) then
        
        # remove sublist variables
        for name in template.sublist_variable_names do
            
            src_template := ReplacedString( src_template, Concatenation( name, "...," ), "" );
            src_template := ReplacedString( src_template, Concatenation( name, "..." ), "" );
            dst_template := ReplacedString( dst_template, Concatenation( name, "...," ), "" );
            dst_template := ReplacedString( dst_template, Concatenation( name, "..." ), "" );
            
        od;
        
    fi;
    
    src_func := EvalString( Concatenation( "{ ", JoinStringsWithSeparator( template.variable_names, ", " ), " } -> ", src_template ) );
    dst_func := EvalString( Concatenation( "{ ", JoinStringsWithSeparator( template.variable_names, ", " ), " } -> ", dst_template ) );
    
    src_string := FunctionAsMathString( src_func, cat, input_filters : raw );
    
    if dst_template = "true" then
        
        latex_string := src_string;
        
    else
        
        dst_string := FunctionAsMathString( dst_func, cat, input_filters : raw );
        
        latex_string := Concatenation( src_string, " ", connecting_symbol, " ", dst_string );
        
    fi;
    
    latex_string := Concatenation( "\\text{(rule)}\\quad ", latex_string );
    
    #latex_string := Concatenation( "\\framebox[\\textwidth]{\\resizebox{\\ifdim\\width>\\hsize\\hsize\\else\\width\\fi}{!}{$", latex_string, suffix, "$}}\n" );
    latex_string := Concatenation( "\\resizebox{\\ifdim\\width>\\hsize\\hsize\\else\\width\\fi}{!}{$", latex_string, suffix, "$}\n" );
    
    return Concatenation( "\\[", latex_string, "\\]\n" );
    
end;

operations := rec( );
operations.(" ⊗_0 ") := "TensorProductOnObjects";
operations.(" ⊗_1 ") := "TensorProductOnMorphisms";
operations.(" ⋅ ") := "PreCompose";
operations.(" ∼ ") := "IsCongruentForMorphisms";

parse := function ( string )
  local pointer, consume_char, consume_chars, all_chars_consumed, current_char, starts_with, inner_parse;
    
    pointer := 1;
    
    consume_char := function ( )
        
        pointer := pointer + 1;
        
    end;
    
    consume_chars := function ( n )
        
        pointer := pointer + n;
        
    end;
    
    all_chars_consumed := function ( )
        
        return pointer > Length( string );
        
    end;
    
    current_char := function ( )
        
        return string[pointer];
        
    end;
    
    starts_with := function ( prefix )
        
        return Length( string ) >= pointer + Length( prefix ) - 1 and ForAll( [ 1 .. Length( prefix ) ], i -> prefix[i] = string[pointer + i - 1] );
        
    end;
    
    inner_parse := function ( delimiter )
      local output_string, undelimited_operation, post_process, first, operation_names, operation_name, second;
        
        #Display( "search until" );
        #Display( delimiter );
        
        output_string := "";
        
        undelimited_operation := false;
        
        post_process := function ( )
        
            if undelimited_operation then
                
                second := output_string;
                
                output_string := "";
                
                Append( output_string, operations.(operation_name) );
                Append( output_string, "( cat, " );
                Append( output_string, first );
                Append( output_string, ", " );
                Append( output_string, second );
                Append( output_string, " )" );
                
            fi;
            
        end;
        
        repeat
            
            if starts_with( "id_{" ) then
                
                consume_chars(4);
                
                Append( output_string, "IdentityMorphism( cat, " );
                Append( output_string, inner_parse( "}" ) );
                Append( output_string, " )" );
                
            elif delimiter = "}" and starts_with( "}" ) then
                
                consume_char( );
                
                post_process( );
                
                return output_string;
                
            elif starts_with( "{" ) then
                
                consume_char( );
                
                Append( output_string, inner_parse( "}" ) );
                
            elif ForAny( RecNames( operations ), name -> starts_with( name ) ) then
                
                if undelimited_operation then
                    
                    Error( "nested undelimited operations are not supported" );
                    
                fi;
                
                # operation without { }
                
                undelimited_operation := true;
                
                first := ShallowCopy( output_string );
                
                output_string := "";
                
                operation_names := Filtered( RecNames( operations ), name -> starts_with( name ) );
                
                Assert( 0, Length( operation_names ) = 1 );
                
                operation_name := operation_names[1];
                
                consume_chars( Length( operation_name ) );
                
            elif starts_with( "}" ) then
                
                Error( "Unexpected }" );
                
            else
                
                Add( output_string, current_char( ) );
                
                consume_char( );
                
            fi;
            
        until all_chars_consumed( );
        
        if delimiter <> fail then
            
            Error( "Expected ", delimiter );
            
        fi;
        
        post_process( );
        
        return output_string;
        
    end;
    
    return inner_parse( fail );
    
end;

InstallGlobalFunction( CAP_JIT_INTERNAL_ENHANCE_LOGIC_TEMPLATE, function ( template )
  local diff, unbound_global_variable_names, pre_func_identify_syntax_tree_variables, additional_arguments_func_identify_syntax_tree_variables, src_template, dst_template, name, variable_names, tmp_tree, pre_func, additional_arguments_func, i;
    
    # Caution: this function must only be called once the needed packages of the template are loaded!
    
    if IsBound( template.is_fully_enhanced ) and template.is_fully_enhanced = true then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "the logic template is already fully enhanced" );
        
    fi;
    
    # some basic sanity checks
    if not IsRecord( template ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "a logic template must be a record" );
        
    fi;
    
    if not IsSubset( RecNames( template ), [ "variable_names", "src_template", "dst_template" ] ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "a logic template must have the following required record entries: variable_names, src_template, dst_template" );
        
    fi;
    
    diff := Difference( RecNames( template ), [ "variable_names", "variable_filters", "sublist_variable_names", "src_template", "src_template_tree", "dst_template", "dst_template_tree", "new_funcs", "number_of_applications", "needed_packages", "debug", "debug_path", "enhanced_syntax" ] );
    
    if not IsEmpty( diff ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "a logic template has unknown components: ", diff );
        
    fi;
    
    if IsBound( template.variable_filters ) and Length( template.variable_names ) <> Length( template.variable_filters ) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "the length of the record entries variable_names and variable_filters of a logic template must be equal" );
        
    fi;
    
    if Last( NormalizedWhitespace( template.src_template ) ) = ';' then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "src_template ends with a semicolon. This is not supported." );
        
    fi;
    
    if Last( NormalizedWhitespace( template.dst_template ) ) = ';' then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "dst_template ends with a semicolon. This is not supported." );
        
    fi;
    
    if IsBound( template.needed_packages ) and (not IsList( template.needed_packages ) or ForAny( template.needed_packages, p -> not IsList( p ) or Length( p ) <> 2 )) then
        
        # COVERAGE_IGNORE_NEXT_LINE
        Error( "the record entry needed_packages of a logic template must be a list of pairs" );
        
    fi;
    
    if IsBound( template.variable_filters ) then
        
        # replace strings with actual filters
        template.variable_filters := List( template.variable_filters, function ( f )
            
            if IsString( f ) then
                
                return ValueGlobal( f );
                
            else
                
                return f;
                
            fi;
            
        end );
        
    else
        
        # default variable filters: IsObject
        template.variable_filters := ListWithIdenticalEntries( Length( template.variable_names ), IsObject );
        
    fi;
    
    # default sublist variables: none
    if not IsBound( template.sublist_variable_names ) then
        
        template.sublist_variable_names := [ ];
        
    fi;
    
    # default new funcs: none
    if not IsBound( template.new_funcs ) then
        
        template.new_funcs := [ ];
        
    fi;
    
    # default number of applications: infinity
    if not IsBound( template.number_of_applications ) then
        
        template.number_of_applications := infinity;
        
    fi;
    
    # parse enhanced syntax
    if IsBound( template.enhanced_syntax ) and template.enhanced_syntax = true then
        Error("not supported anymore");
        template.src_template := parse( template.src_template );
        template.dst_template := parse( template.dst_template );
        
        Display( template.src_template );
        Display( template.dst_template );
        
    fi;
    
    pre_func_identify_syntax_tree_variables := function ( tree, outer_func_id )
        
        # `IsBoundGlobal` calls `CheckGlobalName`, which warns about names containing characters not in `IdentifierLetters`.
        # This is expected for operations in CAP_JIT_INTERNAL_OPERATION_TO_SYNTAX_TREE_TRANSLATIONS, so we avoid IsBoundGlobal in this case.
        if tree.type = "EXPR_REF_GVAR" and not IsBound( CAP_JIT_INTERNAL_OPERATION_TO_SYNTAX_TREE_TRANSLATIONS.(tree.gvar) ) and not IsBoundGlobal( tree.gvar ) then
            
            # for debugging only
            # COVERAGE_IGNORE_NEXT_LINE
            Add( unbound_global_variable_names, tree.gvar );
            
        fi;
        
        if tree.type = "EXPR_REF_FVAR" and tree.func_id = outer_func_id then
            
            if tree.name in template.variable_names then
                
                return rec(
                    type := "SYNTAX_TREE_VARIABLE",
                    id := SafeUniquePosition( template.variable_names, tree.name ),
                );
                
            elif tree.name in template.sublist_variable_names then
                
                return rec(
                    type := "SYNTAX_TREE_SUBLIST_VARIABLE",
                    id := SafeUniquePosition( template.sublist_variable_names, tree.name ),
                );
                
            else
                
                Error( "this should never happen" );
                
            fi;
            
        fi;
        
        return tree;
        
    end;
    
    additional_arguments_func_identify_syntax_tree_variables := function ( tree, key, outer_func_id )
        
        return outer_func_id;
        
    end;
    
    src_template := template.src_template;
    dst_template := template.dst_template;
    
    # replace "..." following sublist variables
    for name in template.sublist_variable_names do
        
        src_template := ReplacedString( src_template, Concatenation( name, "..." ), name );
        dst_template := ReplacedString( dst_template, Concatenation( name, "..." ), name );
        
    od;
    
    variable_names := Concatenation( template.variable_names, template.sublist_variable_names );
    
    for name in variable_names do
        
        if name in GAPInfo.Keywords then
            
            # COVERAGE_IGNORE_NEXT_LINE
            Error( "\"", name, "\" (contained in variable_names) is a keyword. This is not supported." );
            
        fi;
        
        if PositionSublist( src_template, name ) = fail then
            
            # COVERAGE_IGNORE_NEXT_LINE
            Error( "Variable name \"", name, "\" does not appear in src_template. This is not supported." );
            
        fi;
        
    od;
    
    # get src_template_tree from src_template
    if not IsBound( template.src_template_tree ) then
        
        # to get a syntax tree we have to wrap the template in a function
        tmp_tree := ENHANCED_SYNTAX_TREE( EvalStringStrict( Concatenation( "{ ", JoinStringsWithSeparator( variable_names, ", " ), " } -> ", src_template ) ) );
        
        Assert( 0, tmp_tree.bindings.names = [ "RETURN_VALUE" ] );
        
        unbound_global_variable_names := [ ];
        
        template.src_template_tree := CapJitIterateOverTree( CapJitValueOfBinding( tmp_tree.bindings, "RETURN_VALUE" ), pre_func_identify_syntax_tree_variables, CapJitResultFuncCombineChildren, additional_arguments_func_identify_syntax_tree_variables, tmp_tree.id );
        
        if not IsEmpty( unbound_global_variable_names ) then
            
            # COVERAGE_IGNORE_NEXT_LINE
            Error( "found the following unbound global variables in src_template, they should probably be listed in variable_names: ", unbound_global_variable_names );
            
        fi;
        
    fi;
    
    # get dst_template_tree from dst_template
    if not IsBound( template.dst_template_tree ) then
        
        # to get a syntax tree we have to wrap the template in a function
        tmp_tree := ENHANCED_SYNTAX_TREE( EvalStringStrict( Concatenation( "{ ", JoinStringsWithSeparator( variable_names, ", " ), " } -> ", dst_template ) ) );
        
        Assert( 0, tmp_tree.bindings.names = [ "RETURN_VALUE" ] );
        
        unbound_global_variable_names := [ ];
        
        template.dst_template_tree := CapJitIterateOverTree( CapJitValueOfBinding( tmp_tree.bindings, "RETURN_VALUE" ), pre_func_identify_syntax_tree_variables, CapJitResultFuncCombineChildren, additional_arguments_func_identify_syntax_tree_variables, tmp_tree.id );
        
        if not IsEmpty( unbound_global_variable_names ) then
            
            # COVERAGE_IGNORE_NEXT_LINE
            Error( "found the following unbound global variables in dst_template, there probably is a typo: ", unbound_global_variable_names );
            
        fi;
        
    fi;
    
    # Match functions in dst_template_tree to those in src_template_tree and set function IDs accordingly.
    # Functions from src_template_tree can appear multiple times in dst_template_tree, so in dst_template_tree the same function ID can occur multiple times.
    # However, we do not allow the same ID to occur multiple times in a single function stack, as this would cause ambiguities.
    
    template.new_funcs_corresponding_src_funcs := [ ];
    
    pre_func := function ( tree, func_id_stack )
      local dst_func, pos, condition_func, src_template_paths, src_func, pre_func;
        
        if tree.type = "EXPR_DECLARATIVE_FUNC" then
            
            dst_func := tree;
            
            pos := Position( template.new_funcs, dst_func.nams{[ 1 .. dst_func.narg ]} );
            
            # if this is not a new function, find matching function in src_template_tree
            if pos = fail then
                
                condition_func := function ( tree, path )
                    
                    return tree.type = "EXPR_DECLARATIVE_FUNC" and tree.nams = dst_func.nams;
                    
                end;
                
                src_template_paths := CapJitFindNodes( template.src_template_tree, condition_func );
                
                if Length( src_template_paths ) = 0 then
                    
                    # COVERAGE_IGNORE_NEXT_LINE
                    Error( "could not find matching func in src_template" );
                    
                elif Length( src_template_paths ) > 1 then
                    
                    # COVERAGE_IGNORE_NEXT_LINE
                    Error( "found multiple matching funcs in src_template" );
                    
                fi;
                
                src_func := CapJitGetNodeByPath( template.src_template_tree, src_template_paths[1] );
                
                Assert( 0, src_func.nams = dst_func.nams );
                
                if src_func.id in func_id_stack then
                    
                    # COVERAGE_IGNORE_NEXT_LINE
                    Error( "A function in src_template is used multiple times in dst_template in a nested way. This is not supported." );
                    
                fi;
                
                dst_func := CAP_JIT_INTERNAL_REPLACED_FVARS_FUNC_ID( dst_func, src_func.id, src_func.nams );
                
            fi;
            
            return dst_func;
            
        fi;
        
        # detect `List( SYNTAX_TREE_VARIABLE, x -> ... )` where `x -> ...` is a new function
        if CapJitIsCallToGlobalFunction( tree, "List" ) and tree.args.1.type = "SYNTAX_TREE_VARIABLE" and tree.args.2.type = "EXPR_DECLARATIVE_FUNC" then
            
            dst_func := tree.args.2;
            
            pos := Position( template.new_funcs, dst_func.nams{[ 1 .. dst_func.narg ]} );
            
            if pos <> fail then
                
                # detect `List( SYNTAX_TREE_VARIABLE, func )` in src_template_tree
                pre_func := function ( src_tree, additional_arguments )
                    
                    if IsBound( template.new_funcs_corresponding_src_funcs[pos] ) then
                        
                        return fail;
                        
                    fi;
                    
                    if CapJitIsCallToGlobalFunction( src_tree, "List" ) and src_tree.args.1.type = "SYNTAX_TREE_VARIABLE" and src_tree.args.1.id = tree.args.1.id and src_tree.args.2.type in [ "SYNTAX_TREE_VARIABLE", "EXPR_DECLARATIVE_FUNC" ] then
                        
                        template.new_funcs_corresponding_src_funcs[pos] := src_tree.args.2;
                        
                    fi;
                    
                    return src_tree;
                    
                end;
                
                CapJitIterateOverTree( template.src_template_tree, pre_func, ReturnTrue, ReturnTrue, true );
                
            fi;
            
        fi;
        
        # detect `ListN( SYNTAX_TREE_VARIABLE_1, SYNTAX_TREE_VARIABLE_2, { x, y } -> ... )` where `{ x, y } -> ...` is a new function
        if CapJitIsCallToGlobalFunction( tree, "ListN" ) and tree.args.1.type = "SYNTAX_TREE_VARIABLE" and tree.args.2.type = "SYNTAX_TREE_VARIABLE" and tree.args.3.type = "EXPR_DECLARATIVE_FUNC" then
            
            dst_func := tree.args.3;
            
            pos := Position( template.new_funcs, dst_func.nams{[ 1 .. dst_func.narg ]} );
            
            if pos <> fail then
                
                # detect `ListN( SYNTAX_TREE_VARIABLE_1, SYNTAX_TREE_VARIABLE_2, func )` in src_template_tree
                pre_func := function ( src_tree, additional_arguments )
                    
                    if IsBound( template.new_funcs_corresponding_src_funcs[pos] ) then
                        
                        return fail;
                        
                    fi;
                    
                    if CapJitIsCallToGlobalFunction( src_tree, "ListN" ) and src_tree.args.1.type = "SYNTAX_TREE_VARIABLE" and src_tree.args.1.id = tree.args.1.id and src_tree.args.2.type = "SYNTAX_TREE_VARIABLE" and src_tree.args.2.id = tree.args.2.id and src_tree.args.3.type in [ "SYNTAX_TREE_VARIABLE", "EXPR_DECLARATIVE_FUNC" ] then
                        
                        template.new_funcs_corresponding_src_funcs[pos] := src_tree.args.3;
                        
                    fi;
                    
                    return src_tree;
                    
                end;
                
                CapJitIterateOverTree( template.src_template_tree, pre_func, ReturnTrue, ReturnTrue, true );
                
            fi;
            
        fi;
        
        return tree;
        
    end;
    
    additional_arguments_func := function ( tree, key, func_id_stack )
        
        if tree.type = "EXPR_DECLARATIVE_FUNC" then
            
            return Concatenation( func_id_stack, [ tree.id ] );
            
        else
            
            return func_id_stack;
            
        fi;
        
    end;
    
    template.dst_template_tree := CapJitIterateOverTree( template.dst_template_tree, pre_func, CapJitResultFuncCombineChildren, additional_arguments_func, [ ] );
    
    template.is_fully_enhanced := true;
    
end );

# CallFuncList( func, [ a, b, ... ] ) => func( a, b, ... )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "func" ],
        sublist_variable_names := [ "arguments" ],
        src_template := "CallFuncList( func, [ arguments... ] )",
        dst_template := "func( arguments... )",
    )
);

# x -> x => ID_FUNC
CapJitAddLogicTemplate(
    rec(
        variable_names := [ ],
        src_template := "x -> x",
        dst_template := "ID_FUNC",
    )
);

# ID_FUNC( value ) => value
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "value" ],
        src_template := "ID_FUNC( value )",
        dst_template := "value",
    )
);

# List( list, ID_FUNC ) => list
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list" ],
        variable_filters := [ IsList ],
        src_template := "List( list, ID_FUNC )",
        dst_template := "list",
    )
);

# List( List( L, f ), g ) => List( L, x -> g( f( x ) ) )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list", "outer_func", "inner_func" ],
        src_template := "List( List( list, inner_func ), outer_func )",
        dst_template := "List( list, x -> outer_func( inner_func( x ) ) )",
        new_funcs := [ [ "x" ] ],
    )
);

# List( list, x -> func( x ) ) => List( list, func )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list", "func" ],
        src_template := "List( list, x -> func( x ) )",
        dst_template := "List( list, func )",
    )
);

# List( ListN( L1, L2, f ), g ) => ListN( L1, L2, { x, y } -> g( f( x, y ) ) )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list1", "list2", "outer_func", "inner_func" ],
        src_template := "List( ListN( list1, list2, inner_func ), outer_func )",
        dst_template := "ListN( list1, list2, { x, y } -> outer_func( inner_func( x, y ) ) )",
        new_funcs := [ [ "x", "y" ] ],
    )
);

# ListN( List( L, f1 ), List( L, f2 ), g ) => List( L, x -> g( f1( x ), f2( x ) ) )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list", "inner_func1", "inner_func2", "outer_func" ],
        src_template := "ListN( List( list, inner_func1 ), List( list, inner_func2 ), outer_func )",
        dst_template := "List( list, x -> outer_func( inner_func1( x ), inner_func2( x ) ) )",
        new_funcs := [ [ "x" ] ],
    )
);

# List( Concatenation( list ), func ) => Concatenation( List( list, x -> List( x, func ) ) )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list", "func" ],
        src_template := "List( Concatenation( list ), func )",
        dst_template := "Concatenation( List( list, x -> List( x, func ) ) )",
        new_funcs := [ [ "x" ] ],
    )
);

# List( L{poss}, f ) => List( L, f ){poss}
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list", "poss", "func" ],
        src_template := "List( list{poss}, func )",
        dst_template := "List( list, func ){poss}",
    )
);

# func( L )[index] => List( L, func )[index]
# Note: We always "push down" the function, because:
# If L is a `Concatenation`, we cannot resolve the index on the left hand side, but we can push the function further down on the right hand side.
# This causes some minor overhead if the index is fixed (e.g. for ProjectionInFactorOfDirectSum) because f is applied to the whole list
# instead of only the element given by the index, but such examples are rare.
# Additionally, this should only trigger for homogeneous lists, i.e. `func` must be applicable to all elements of `L`.
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list", "func", "index" ],
        variable_filters := [ IsList, IsFunction, IsInt ],
        src_template := "func( list[index] )",
        dst_template := "List( list, func )[index]",
    )
);

# List( list_of_lists[index], func ) => List( list_of_lists, list -> List( list, func ) )[index]
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list_of_lists", "index", "func" ],
        variable_filters := [ IsList, IsInt, IsFunction ],
        src_template := "List( list_of_lists[index], func )",
        dst_template := "List( list_of_lists, list -> List( list, func ) )[index]",
        new_funcs := [ [ "list" ] ],
    )
);

# Length( List( list, func ) ) => Length( list )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list", "func" ],
        src_template := "Length( List( list, func ) )",
        dst_template := "Length( list )",
    )
);

# Length( [ 1 .. n ] ) => n
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "n" ],
        src_template := "Length( [ 1 .. n ] )",
        dst_template := "n",
    )
);

# [ 1 .. range_end ][i] => i
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "range_end", "index" ],
        src_template := "[ 1 .. range_end ][index]",
        dst_template := "index",
    )
);

# Iterated: function always choosing first value
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list", "initial_value" ],
        src_template := "Iterated( list, { x, y } -> x, initial_value )",
        dst_template := "initial_value",
    )
);

# Iterated: function always choosing first value
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list", "initial_value", "terminal_value" ],
        src_template := "Iterated( list, { x, y } -> x, initial_value, terminal_value )",
        dst_template := "initial_value",
    )
);

# Iterated: function always choosing last value
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list", "initial_value", "terminal_value" ],
        src_template := "Iterated( list, { x, y } -> y, initial_value, terminal_value )",
        dst_template := "terminal_value",
    )
);

# AsValue( AsCapCategoryObject( cat, object_datum ) ) => object_datum
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "object_datum" ],
        src_template := "AsValue( AsCapCategoryObject( cat, object_datum ) )",
        dst_template := "object_datum",
    )
);

# Source( AsCapCategoryMorphism( cat, source, morphism_datum, range ) ) => source
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "source", "morphism_datum", "range" ],
        src_template := "Source( AsCapCategoryMorphism( cat, source, morphism_datum, range ) )",
        dst_template := "source",
    )
);

# Range( AsCapCategoryMorphism( cat, source, morphism_datum, range ) ) => range
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "source", "morphism_datum", "range" ],
        src_template := "Range( AsCapCategoryMorphism( cat, source, morphism_datum, range ) )",
        dst_template := "range",
    )
);

# AsValue( AsCapCategoryMorphism( cat, source, morphism_datum, range ) ) => morphism_datum
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "source", "morphism_datum", "range" ],
        src_template := "AsValue( AsCapCategoryMorphism( cat, source, morphism_datum, range ) )",
        dst_template := "morphism_datum",
    )
);

# booleans together with `and` and `or`
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "value" ],
        src_template := "true and value",
        dst_template := "value",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "value" ],
        src_template := "value and true",
        dst_template := "value",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "value" ],
        src_template := "false and value",
        dst_template := "false",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "value" ],
        src_template := "value and false",
        dst_template := "false",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "value" ],
        src_template := "true or value",
        dst_template := "true",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "value" ],
        src_template := "value or true",
        dst_template := "true",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "value" ],
        src_template := "false or value",
        dst_template := "value",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "value" ],
        src_template := "value or false",
        dst_template := "value",
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

# ForAll( List( list, func1 ), func2 )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "list", "func1", "func2" ],
        src_template := "ForAll( List( list, func1 ), func2 )",
        dst_template := "ForAll( list, x -> func2( func1( x ) ) )",
        new_funcs := [ [ "x" ] ],
    )
);

# IsEqualForObjects( expr, expr ) => true
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "expr" ],
        src_template := "IsEqualForObjects( cat, expr, expr )",
        dst_template := "true",
    )
);

# IsCongruentForMorphisms( expr, expr ) => true
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "mor" ],
        src_template := "IsCongruentForMorphisms( cat, mor, mor )",
        dst_template := "true",
    )
);

# Length( [ 1 .. length ] )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "length" ],
        src_template := "Length( [ 1 .. length ] )",
        dst_template := "length",
    )
);

InstallGlobalFunction( CAP_JIT_INTERNAL_TREE_MATCHES_TEMPLATE_TREE, function ( tree, template_tree, variables, variable_filters, sublist_variables, func_id_replacements, debug )
  local i, pre_func, result_func, additional_arguments_func;
    
    # bail out early if type mismatches
    if template_tree.type <> "SYNTAX_TREE_VARIABLE" and tree.type <> template_tree.type then
        
        return false;
        
    fi;
    
    # after inlining, most syntax tree nodes are of type EXPR_FUNCCALL -> we can bail out early for some frequent conditions (i.e. check the type of funcref and args)
    if template_tree.type = "EXPR_FUNCCALL" then
        
        # by the check above, tree.type = template_tree.type = "EXPR_FUNCCALL"
        
        if template_tree.funcref.type <> "SYNTAX_TREE_VARIABLE" then
            
            if tree.funcref.type <> template_tree.funcref.type then
                
                return false;
                
            fi;
            
            if template_tree.funcref.type = "EXPR_REF_GVAR" then
                
                if
                    not IsIdenticalObj( ValueGlobal( tree.funcref.gvar ), ValueGlobal( template_tree.funcref.gvar ) ) and
                    not (template_tree.funcref.gvar in [ "Range", "Target" ] and tree.funcref.gvar in [ "Range", "Target" ] and IsBound( tree.funcref.data_type ) and IsSpecializationOfFilter( IsCapCategoryMorphism, tree.funcref.data_type.signature[1][1].filter ))
                then
                    
                    return false;
                    
                fi;
                
            fi;
            
        fi;
        
        if tree.args.length <> template_tree.args.length then
            
            return false;
            
        fi;
        
        for i in [ 1 .. template_tree.args.length ] do
            
            if template_tree.args.(i).type <> "SYNTAX_TREE_VARIABLE" and tree.args.(i).type <> template_tree.args.(i).type then
                
                return false;
                
            fi;
            
        od;
        
    fi;
    
    pre_func := function ( template_tree, tree )
      local new_template_tree;
        
        if template_tree.type = "SYNTAX_TREE_SUBLIST_VARIABLE" then
            
            Error( "unexpected occurence of a subtree variable" );
            
        fi;
        
        if template_tree.type <> "SYNTAX_TREE_VARIABLE" and tree.type <> template_tree.type then
            
            return fail;
            
        fi;
        
        if template_tree.type = "SYNTAX_TREE_LIST" then
            
            if template_tree.length > 0 and template_tree.1.type = "SYNTAX_TREE_SUBLIST_VARIABLE" then
                
                if Last( template_tree ).type <> "SYNTAX_TREE_SUBLIST_VARIABLE" then
                    
                    Error( "the first part of this list is a sublist variable, but the last part is not" );
                    
                fi;
                
                if ForAny( [ 2 .. template_tree.length - 1 ], i -> template_tree.(i).type = "SYNTAX_TREE_SUBLIST_VARIABLE" ) then
                    
                    Error( "sublist variables may only occur at the beginning or the end of a list" );
                    
                fi;
                
                return fail;
                
            elif template_tree.length <> tree.length then
                
                return fail;
                
            fi;
            
        fi;
        
        if template_tree.type = "EXPR_DECLARATIVE_FUNC" then
            
            Assert( 0, tree.type = "EXPR_DECLARATIVE_FUNC" );
            
            # we are only interested in two cases:
            # a) the functions actually only differ by ID, i.e. the names of all local variables and bindings agree
            # b) there are no local variables (i.e. only a single return statement), but the argument names might differ
            if template_tree.narg = tree.narg and template_tree.variadic = tree.variadic and ((template_tree.nams = tree.nams and template_tree.bindings.names = tree.bindings.names) or (Length( template_tree.nams ) = template_tree.narg + 1 and Length( tree.nams ) = tree.narg + 1 )) then
                
                Assert( 0, not IsBound( func_id_replacements.(template_tree.id) ) );
                
                # map from template function to actual function
                func_id_replacements.(template_tree.id) := rec(
                    func_id := tree.id,
                    nams := tree.nams,
                );
                
                template_tree := CAP_JIT_INTERNAL_REPLACED_FVARS_FUNC_ID( template_tree, tree.id, tree.nams );
                
            else
                
                return fail;
                
            fi;
            
        fi;
        
        return template_tree;
        
    end;
    
    result_func := function ( template_tree, result, keys, tree )
      local elements, template_elements, found_match, new_variables, new_sublist_variables, new_func_id_replacements, pre_id, post_id, var_number, filter, i, j, k, key;
        
        if debug then
            # COVERAGE_IGNORE_BLOCK_START
            Display( "now matching against" );
            Display( template_tree );
            Display( "result" );
            Display( result );
            # COVERAGE_IGNORE_BLOCK_END
        fi;
        
        # handle sublist variables
        if template_tree.type = "SYNTAX_TREE_LIST" and tree.type = "SYNTAX_TREE_LIST" and template_tree.length > 0 and template_tree.1.type = "SYNTAX_TREE_SUBLIST_VARIABLE" then
            
            # checked in pre_func
            Assert( 0, ForAll( [ 2 .. template_tree.length - 1 ], i -> template_tree.(i).type <> "SYNTAX_TREE_SUBLIST_VARIABLE" ) and Last( template_tree ).type = "SYNTAX_TREE_SUBLIST_VARIABLE" );
            
            elements := AsListMut( tree );
            template_elements := AsListMut( template_tree ){[ 2 .. template_tree.length - 1 ]};
            
            # search for a matching position
            # `i` is the length of the non-matching prefix
            for i in [ 0 .. Length( elements ) - Length( template_elements ) ] do
                
                found_match := true;
                new_variables := ShallowCopy( variables );
                new_sublist_variables := ShallowCopy( sublist_variables );
                new_func_id_replacements := ShallowCopy( func_id_replacements );
                
                for j in [ 1 .. Length( template_elements ) ] do
                    
                    if not CAP_JIT_INTERNAL_TREE_MATCHES_TEMPLATE_TREE( elements[i + j], template_elements[j], new_variables, variable_filters, new_sublist_variables, new_func_id_replacements, debug ) then
                        
                        found_match := false;
                        break;
                        
                    fi;
                    
                od;
                
                if found_match then
                    
                    # populate sublist_variables
                    pre_id := template_tree.1.id;
                    post_id := Last( template_tree ).id;
                    
                    if IsBound( new_sublist_variables[pre_id] ) or IsBound( new_sublist_variables[post_id] ) or (template_tree.length >= 2 and pre_id = post_id) then
                        
                        Error( "sublist variables may only occur once in src_template" );
                        
                    fi;
                    
                    if pre_id = post_id then
                        
                        Assert( 0, template_tree.length = 1 and i = 0 );
                        
                    fi;
                    
                    # this also works in the case `pre_id` = `post_id`, which implies `template_tree.length` = 1 and `i` = 0
                    sublist_variables[pre_id] := Sublist( tree, [ 1 .. i ] );
                    sublist_variables[post_id] := Sublist( tree, [ i + Length( template_elements ) + 1 .. tree.length ] );
                    
                    # copy new data
                    for k in PositionsBound( new_variables ) do
                        
                        if IsBound( variables[k] ) then
                            
                            Assert( 0, IsIdenticalObj( variables[k], new_variables[k] ) );
                            
                        else
                            
                            variables[k] := new_variables[k];
                            
                        fi;
                        
                    od;
                    
                    for k in PositionsBound( new_sublist_variables ) do
                        
                        if IsBound( sublist_variables[k] ) then
                            
                            Assert( 0, IsIdenticalObj( sublist_variables[k], new_sublist_variables[k] ) );
                            
                        else
                            
                            sublist_variables[k] := new_sublist_variables[k];
                            
                        fi;
                        
                    od;
                    
                    for k in RecNames( new_func_id_replacements ) do
                        
                        if IsBound( func_id_replacements.(k) ) then
                            
                            Assert( 0, IsIdenticalObj( func_id_replacements.(k), new_func_id_replacements.(k) ) );
                            
                        else
                            
                            func_id_replacements.(k) := new_func_id_replacements.(k);
                            
                        fi;
                        
                    od;
                    
                    return true;
                    
                fi;
                
            od;
            
            return false;
            
        fi;
        
        # check if we already bailed out in pre_func
        if result = fail then
            
            return false;
            
        fi;
        
        # handle syntax tree variables
        if template_tree.type = "SYNTAX_TREE_VARIABLE" then
            
            var_number := template_tree.id;
            
            if not IsBound( variables[var_number] ) then
                
                filter := variable_filters[var_number];
                
                if IsIdenticalObj( filter, IsObject ) or (IsBound( tree.data_type ) and IsSpecializationOfFilter( filter, tree.data_type.filter )) then
                    
                    variables[var_number] := tree;
                    
                    if debug then
                        # COVERAGE_IGNORE_BLOCK_START
                        Display( "matched via variable1" );
                        Display( true );
                        # COVERAGE_IGNORE_BLOCK_END
                    fi;
                    
                    return true;
                    
                else
                    
                    if debug then
                        # COVERAGE_IGNORE_BLOCK_START
                        Display( "type could not be inferred or did not match" );
                        # COVERAGE_IGNORE_BLOCK_END
                    fi;
                    
                    return false;
                    
                fi;
                
            else
                
                if debug then
                    # COVERAGE_IGNORE_BLOCK_START
                    Display( "matched via variable2" );
                    Display( CapJitIsEqualForEnhancedSyntaxTrees( variables[var_number], tree ) );
                    # COVERAGE_IGNORE_BLOCK_END
                fi;
                
                return CapJitIsEqualForEnhancedSyntaxTrees( variables[var_number], tree );
                
            fi;
            
        fi;
        
        # <keys> are only the keys with children, but we want to test all keys -> loop over RecNames( template_tree )
        for key in RecNames( template_tree ) do
            
            if debug then
                # COVERAGE_IGNORE_BLOCK_START
                Display( "checking" );
                Display( key );
                # COVERAGE_IGNORE_BLOCK_END
            fi;
            
            if key = "data_type" then
                
                if IsBound( tree.data_type ) and tree.data_type <> template_tree.data_type then
                    
                    if debug then
                        # COVERAGE_IGNORE_NEXT_LINE
                        Display( "data type mismatch" );
                    fi;
                    
                    return false;
                    
                fi;
                
                continue;
                
            fi;
            
            # ignore these keys
            if key = "CAP_JIT_NOT_RESOLVABLE" then
                
                continue;
                
            fi;
            
            Assert( 0, IsBound( tree.(key) ) );
            
            # different gvars might point to the same value
            if key = "gvar" then
                
                if IsIdenticalObj( ValueGlobal( template_tree.gvar ), ValueGlobal( tree.gvar ) ) then
                    
                    if debug then
                        # COVERAGE_IGNORE_NEXT_LINE
                        Display( "match: gvars point to identical values" );
                    fi;
                    
                    continue;
                    
                elif template_tree.gvar in [ "Range", "Target" ] and tree.gvar in [ "Range", "Target" ] and IsBound( tree.data_type ) and IsSpecializationOfFilter( IsCapCategoryMorphism, tree.data_type.signature[1][1].filter ) then
                    
                    if debug then
                        # COVERAGE_IGNORE_NEXT_LINE
                        Display( "match: gvars are both Range resp. Target of a morphism" );
                    fi;
                    
                    continue;
                    
                else
                    
                    if debug then
                        # COVERAGE_IGNORE_NEXT_LINE
                        Display( "mismatch: gvars point to non-identical values" );
                    fi;
                    
                    return false;
                    
                fi;
                
            fi;
            
            # check if children match
            if IsBound( result.(key) ) then
                
                if result.(key) = false then
                    
                    if debug then
                        # COVERAGE_IGNORE_BLOCK_START
                        Display( "child mismatch" );
                        Display( key );
                        # COVERAGE_IGNORE_BLOCK_END
                    fi;
                    
                    return false;
                    
                else
                    
                    continue;
                    
                fi;
                
            fi;
            
            # now there should only remain integers, booleans, strings or list of strings
            Assert( 0, IsInt( template_tree.(key) ) or IsBool( template_tree.(key) ) or IsString( template_tree.(key) ) or (IsList( template_tree.(key) ) and ForAll( template_tree.(key), x -> IsString( x ) )) );
            
            if template_tree.(key) <> tree.(key) then
                
                if debug then
                    # COVERAGE_IGNORE_BLOCK_START
                    Display( "tree mismatch" );
                    Display( key );
                    # COVERAGE_IGNORE_BLOCK_END
                fi;
                
                return false;
                
            else
                
                continue;
                
            fi;
            
            # COVERAGE_IGNORE_NEXT_LINE
            Error( "should never get here" );
            
        od;
        
        if debug then
            # COVERAGE_IGNORE_NEXT_LINE
            Display( "everything matched" );
        fi;
        
        return true;
        
    end;
    
    additional_arguments_func := function ( template_tree, key, tree )
        
        return tree.(key);
        
    end;
    
    return CapJitIterateOverTree( template_tree, pre_func, result_func, additional_arguments_func, tree );
    
end );

InstallGlobalFunction( CapJitAppliedLogicTemplates, function ( tree )
  local global_templates, local_templates, template;
    
    Info( InfoCapJit, 1, "####" );
    Info( InfoCapJit, 1, "Apply logic templates." );
    
    for template in CAP_JIT_LOGIC_TEMPLATES do
        
        if IsBound( template.needed_packages ) then
            
            # check if all needed packages are loaded
            if not ForAll( template.needed_packages, p -> IsPackageMarkedForLoading( p[1], p[2] ) ) then
                
                continue;
                
            fi;
            
        fi;
        
        if not IsBound( template.is_fully_enhanced ) or template.is_fully_enhanced <> true then
            
            CAP_JIT_INTERNAL_ENHANCE_LOGIC_TEMPLATE( template );
            
        fi;
        
    od;
    
    global_templates := Filtered( CAP_JIT_LOGIC_TEMPLATES, t -> IsBound( t.is_fully_enhanced ) and t.is_fully_enhanced = true );
    
    if Length( tree.local_replacements ) > 0 then
        
        #Error("qwe");
        
    fi;
    
    local_templates := List( tree.local_replacements, x -> rec(
        variable_names := [ ],
        variable_filters := [ ],
        sublist_variable_names := [ ],
        src_template := "local template",
        src_template_tree := x.src,
        dst_template := "local template",
        dst_template_tree := x.dst,
        new_func := [ ],
        number_of_applications := infinity,
        is_fully_enhanced := true,
    ) );
    
    tree := CAP_JIT_INTERNAL_APPLIED_LOGIC_TEMPLATES( tree, Concatenation( global_templates, local_templates ) );
    
    MakeReadWriteGlobal( "CAP_JIT_LOGIC_TEMPLATES" );
    
    CAP_JIT_LOGIC_TEMPLATES := Filtered( CAP_JIT_LOGIC_TEMPLATES, t -> t.number_of_applications <> 0 );
    
    MakeReadOnlyGlobal( "CAP_JIT_LOGIC_TEMPLATES" );
    
    return tree;
    
end );

InstallGlobalFunction( CAP_JIT_INTERNAL_APPLIED_LOGIC_TEMPLATES, function ( tree, templates )
  local path_debugging_enabled, pre_func, additional_arguments_func;
    
    Assert( 0, ForAll( templates, template -> IsBound( template.is_fully_enhanced ) and template.is_fully_enhanced and template.number_of_applications > 0 ) );
    
    path_debugging_enabled := ForAny( templates, template -> IsBound( template.debug_path ) );
    
    pre_func := function ( tree, additional_arguments )
      local func_id_stack, variables, sublist_variables, func_id_replacements, well_defined, pre_func, result_func, additional_arguments_func, dst_tree, template;
        
        func_id_stack := additional_arguments[1];
        # path = additional_arguments[2] is only needed for debugging and only available if path debugging is enabled
        
        for template in templates do
            
            # Try to apply the same logic template multiple times.
            # If it does not match multiple times, this does not increase the runtime noticeably
            # but if it does, the runtime improves noticeably.
            while template.number_of_applications > 0 do
                
                if IsBound( template.debug ) and template.debug then
                    
                    # COVERAGE_IGNORE_BLOCK_START
                    Display( "try to match template:" );
                    Display( template.src_template );
                    # COVERAGE_IGNORE_BLOCK_END
                    
                fi;
                
                # populated in-place
                variables := [ ];
                sublist_variables := [ ];
                func_id_replacements := rec( );
                
                if not CAP_JIT_INTERNAL_TREE_MATCHES_TEMPLATE_TREE( tree, template.src_template_tree, variables, template.variable_filters, sublist_variables, func_id_replacements, path_debugging_enabled and IsBound( template.debug_path ) and template.debug_path = additional_arguments[2] ) then
                    
                    break;
                    
                fi;
                
                if IsBound( template.debug ) and template.debug then
                    
                    # COVERAGE_IGNORE_NEXT_LINE
                    Error( "found match" );
                    
                fi;
                
                if not IsDenseList( variables ) or Length( variables ) <> Length( template.variable_names ) then
                    
                    # COVERAGE_IGNORE_NEXT_LINE
                    Error( "the following variables where not matched: ", template.variable_names{Difference( [ 1 .. Length( template.variable_names ) ], PositionsBound( variables ) )} );
                    
                fi;
                
                if not IsDenseList( sublist_variables ) or Length( sublist_variables ) <> Length( template.sublist_variable_names ) then
                    
                    # COVERAGE_IGNORE_NEXT_LINE
                    Error( "the following sublist variables where not matched: ", template.sublist_variable_names{Difference( [ 1 .. Length( template.sublist_variable_names ) ], PositionsBound( sublist_variables ) )} );
                    
                fi;
                
                # will be modified inplace
                well_defined := true;
                
                # adjust function IDs and insert variables in dst_template_tree
                pre_func := function ( tree, func_id_stack )
                  local pos, replacement, new_nams, src_func, old_func;
                    
                    if not well_defined then
                        
                        # abort iteration
                        return fail;
                        
                    fi;
                    
                    if tree.type = "EXPR_DECLARATIVE_FUNC" then
                        
                        pos := Position( template.new_funcs, tree.nams{[ 1 .. tree.narg ]} );
                        
                        if pos = fail then
                            
                            Assert( 0, IsBound( func_id_replacements.(tree.id) ) );
                            
                            replacement := func_id_replacements.(tree.id);
                            
                            return CAP_JIT_INTERNAL_REPLACED_FVARS_FUNC_ID( tree, replacement.func_id, replacement.nams );
                            
                        else
                            
                            new_nams := ShallowCopy( tree.nams );
                            
                            # try to get the names of the function arguments from an existing function
                            if IsBound( template.new_funcs_corresponding_src_funcs[pos] ) then
                                
                                src_func := template.new_funcs_corresponding_src_funcs[pos];
                                
                                if src_func.type = "SYNTAX_TREE_VARIABLE" then
                                    
                                    old_func := variables[src_func.id];
                                    
                                    if old_func.type = "EXPR_DECLARATIVE_FUNC" then
                                        
                                        Assert( 0, tree.narg = old_func.narg );
                                        
                                        new_nams{[ 1 .. tree.narg ]} := old_func.nams{[ 1 .. tree.narg ]};
                                        
                                        return CAP_JIT_INTERNAL_REPLACED_FVARS_FUNC_ID( tree, tree.id, new_nams );
                                        
                                    fi;
                                    
                                elif src_func.type = "EXPR_DECLARATIVE_FUNC" then
                                    
                                    Assert( 0, tree.narg = src_func.narg );
                                    
                                    Assert( 0, IsBound( func_id_replacements.(src_func.id) ) );
                                    
                                    replacement := func_id_replacements.(src_func.id);
                                    
                                    new_nams{[ 1 .. tree.narg ]} := replacement.nams{[ 1 .. tree.narg ]};
                                    
                                    return CAP_JIT_INTERNAL_REPLACED_FVARS_FUNC_ID( tree, tree.id, new_nams );
                                    
                                else
                                    
                                    # COVERAGE_IGNORE_NEXT_LINE
                                    Error( "this should never happen" );
                                    
                                fi;
                                
                            fi;
                            
                            # if we cannot find a suitable existing function, prepend "logic_new_func_" to the names of arguments
                            new_nams{[ 1 .. tree.narg ]} := List( tree.nams{[ 1 .. tree.narg ]}, nam -> Concatenation( "logic_new_func_", nam ) );
                            
                            return CAP_JIT_INTERNAL_REPLACED_FVARS_FUNC_ID( tree, tree.id, new_nams );
                            
                        fi;
                        
                    fi;
                    
                    return tree;
                    
                end;
                
                result_func := function ( tree, result, keys, func_id_stack )
                  local key, pre_id, post_id;
                    
                    if not well_defined then
                        
                        return fail;
                        
                    fi;
                    
                    if tree.type = "SYNTAX_TREE_VARIABLE" then
                        
                        # check if the resulting tree would be well-defined
                        if CapJitContainsRefToFVAROutsideOfFuncStack( variables[tree.id], func_id_stack ) then
                            
                            well_defined := false;
                            
                            if IsBound( template.debug ) and template.debug then
                                
                                # COVERAGE_IGNORE_NEXT_LINE
                                Error( "variable contains fvar outside of func stack" );
                                
                            fi;
                            
                            # abort iteration
                            return fail;
                            
                        fi;
                        
                        # new function IDs will be set below
                        return StructuralCopy( variables[tree.id] );
                        
                    fi;
                    
                    tree := ShallowCopy( tree );
                    
                    for key in keys do
                        
                        tree.(key) := result.(key);
                        
                    od;
                    
                    if tree.type = "SYNTAX_TREE_LIST" and tree.length > 0 and tree.1.type = "SYNTAX_TREE_SUBLIST_VARIABLE" then
                        
                        # checked in CAP_JIT_INTERNAL_TREE_MATCHES_TEMPLATE_TREE
                        Assert( 0, ForAll( [ 2 .. tree.length - 1 ], i -> tree.(i).type <> "SYNTAX_TREE_SUBLIST_VARIABLE" ) and Last( tree ).type = "SYNTAX_TREE_SUBLIST_VARIABLE" );
                        
                        pre_id := tree.1.id;
                        post_id := Last( tree ).id;
                        
                        # check if the resulting tree would be well-defined
                        if CapJitContainsRefToFVAROutsideOfFuncStack( sublist_variables[pre_id], func_id_stack ) or CapJitContainsRefToFVAROutsideOfFuncStack( sublist_variables[post_id], func_id_stack ) then
                            
                            well_defined := false;
                            
                            if IsBound( template.debug ) and template.debug then
                                
                                # COVERAGE_IGNORE_NEXT_LINE
                                Error( "sublist variable contains fvar outside of func stack" );
                                
                            fi;
                            
                            # abort iteration
                            return fail;
                            
                        fi;
                        
                        if pre_id = post_id then
                            
                            Assert( 0, tree.length = 1 );
                            
                            # new function IDs will be set below
                            return StructuralCopy( sublist_variables[pre_id] );
                            
                        else
                            
                            # new function IDs will be set below
                            return ConcatenationForSyntaxTreeLists( StructuralCopy( sublist_variables[pre_id] ), Sublist( tree, [ 2 .. tree.length - 1 ] ), StructuralCopy( sublist_variables[post_id] ) );
                            
                        fi;
                        
                    fi;
                    
                    return tree;
                    
                end;
                
                additional_arguments_func := function ( tree, key, func_id_stack )
                    
                    if tree.type = "EXPR_DECLARATIVE_FUNC" then
                        
                        func_id_stack := Concatenation( func_id_stack, [ tree.id ] );
                        
                    fi;
                    
                    return func_id_stack;
                    
                end;
                
                dst_tree := CapJitIterateOverTree( template.dst_template_tree, pre_func, result_func, additional_arguments_func, func_id_stack );
                
                # if new_tree is well-defined, take it
                if well_defined then
                    
                    if IsBound( template.debug ) and template.debug then
                        
                        # COVERAGE_IGNORE_NEXT_LINE
                        Error( "success, dst_tree is well-defined" );
                        
                    fi;
                    
                    Info( InfoCapJit, 1, "####" );
                    Info( InfoCapJit, 1, "Applied the following template:" );
                    Info( InfoCapJit, 1, template.src_template );
                    Info( InfoCapJit, 1, template.dst_template );
                    
                    # make sure we have new function IDs
                    # Functions from src_template_tree can appear multiple times in dst_template_tree, so in dst_template_tree the same function ID can occur multiple times.
                    # Since we require function IDs to be unique in a tree except in this special case, we now have to create a copy with new IDs.
                    tree := CapJitCopyWithNewFunctionIDs( dst_tree );
                    
                    template.number_of_applications := template.number_of_applications - 1;
                    Assert( 0, template.number_of_applications >= 0 );
                    
                    continue;
                    
                else
                    
                    if IsBound( template.debug ) and template.debug then
                        
                        # COVERAGE_IGNORE_NEXT_LINE
                        Error( "dst_tree is not well-defined" );
                        
                    fi;
                    
                    break;
                    
                fi;
                
            od;
            
        od;
        
        return tree;
        
    end;
    
    if path_debugging_enabled then
        
        # COVERAGE_IGNORE_BLOCK_START
        # path is only needed when path debugging is enabled
        additional_arguments_func := function ( tree, key, additional_arguments )
          local path, func_id_stack;
            
            func_id_stack := additional_arguments[1];
            path := additional_arguments[2];
            
            if tree.type = "EXPR_DECLARATIVE_FUNC" then
                
                func_id_stack := Concatenation( func_id_stack, [ tree.id ] );
                
            fi;
            
            path := Concatenation( path, [ key ] );
            
            return [ func_id_stack, path ];
            
        end;
        # COVERAGE_IGNORE_BLOCK_END
        
    else
        
        additional_arguments_func := function ( tree, key, additional_arguments )
            
            if tree.type = "EXPR_DECLARATIVE_FUNC" then
                
                return [ Concatenation( additional_arguments[1], [ tree.id ] ) ];
                
            else
                
                return additional_arguments;
                
            fi;
            
        end;
        
    fi;
    
    return CapJitIterateOverTree( tree, pre_func, CapJitResultFuncCombineChildren, additional_arguments_func, [ [ ], [ ] ] );
    
end );
