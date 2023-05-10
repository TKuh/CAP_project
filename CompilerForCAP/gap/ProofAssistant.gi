# SPDX-License-Identifier: GPL-2.0-or-later
# CompilerForCAP: Speed up computations in CAP categories
#
# Implementations
#

CAP_JIT_PROOF_ASSISTANT_MODE_ENABLED := false;

InstallGlobalFunction( CapJitEnableProofAssistantMode, function ( )
    
    CAP_JIT_PROOF_ASSISTANT_MODE_ENABLED := true;
    
end );

InstallGlobalFunction( CapJitDisableProofAssistantMode, function ( )
    
    CAP_JIT_PROOF_ASSISTANT_MODE_ENABLED := false;
    
end );

CAP_JIT_PROOF_ASSISTANT_CURRENT_CATEGORY := fail;

BindGlobal( "SetCurrentCategory", function ( category, description )
    
    CAP_JIT_PROOF_ASSISTANT_CURRENT_CATEGORY := rec( category := category, description := description );
    
end );

BindGlobal( "PhraseEnumeration", function ( parts )
    
    Assert( 0, Length( parts ) > 0 );
    
    if Length( parts ) = 1 then
        
        return parts[1];
        
    elif Length( parts ) = 2 then
        
        return Concatenation( parts[1], " and ", parts[2] );
        
    else
        
        return Concatenation( JoinStringsWithSeparator( parts{[ 1 .. Length( parts ) - 1 ]}, ", " ), " and ", Last( parts ) );
        
    fi;
    
end );

BindGlobal( "PhraseEnumerationWithOxfordComma", function ( parts )
    
    Assert( 0, Length( parts ) > 0 );
    
    if Length( parts ) = 1 then
        
        return parts[1];
        
    elif Length( parts ) = 2 then
        
        return Concatenation( parts[1], " and ", parts[2] );
        
    else
        
        return Concatenation( JoinStringsWithSeparator( parts{[ 1 .. Length( parts ) - 1 ]}, ", " ), ", and ", Last( parts ) );
        
    fi;
    
end );

CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM := fail;

BindGlobal( "STATE_THEOREM", function ( type, func, args... )
  local cat, input_filters, text, names, handled_input_filters, parts, filter, positions, plural, numerals, numeral, current_names, part, name, inner_parts, source, range, tree, condition_func, conditions, result, i, condition;
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ENABLED );
    
    if CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM <> fail then
        
        Error( "WARNING: overwriting existing active theorem" );
        
    fi;
    
    if Length( args ) = 0 then
        
        Error( "STATE_THEOREM must be called with at least three arguments" );
        
    elif Length( args ) = 1 then
        
        if CAP_JIT_PROOF_ASSISTANT_CURRENT_CATEGORY = fail then
            
            Error( "The category can only be omitted if `SetCurrentCategory` has been called before." );
            
        fi;
        
        cat := CAP_JIT_PROOF_ASSISTANT_CURRENT_CATEGORY.category;
        input_filters := args[1];
        
    elif Length( args ) = 2 then
        
        cat := args[1];
        input_filters := args[2];
        
    else
        
        Error( "STATE_THEOREM must be called with at most 4 arguments" );
        
    fi;
    
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM := rec(
        type := type,
        claim := func,
        func := func,
        cat := cat,
        input_filters := input_filters,
        ever_compiled := false,
    );
    
    if Length( input_filters ) = 0 then
        
        Error( "cannot handle theorems without input" );
        
    elif Length( input_filters ) = 1 then
        
        Error( "TODO" );
        
    else
        
        if CAP_JIT_PROOF_ASSISTANT_CURRENT_CATEGORY = fail then
            
            text := "";
            
        else
            
            text := Concatenation( "In ", CAP_JIT_PROOF_ASSISTANT_CURRENT_CATEGORY.description, " the following statement holds true: " );
            
        fi;
        
        text := Concatenation( text, "For" );
        
        names := NamesLocalVariablesFunction( func );
        
        Assert( 0, Length( names ) >= Length( input_filters ) );
        
        handled_input_filters := [ ];
        
        parts := [ ];
        
        for i in [ 2 .. Length( input_filters ) ] do
            
            filter := input_filters[i];
            
            if filter in handled_input_filters then
                
                continue;
                
            fi;
            
            positions := Positions( input_filters, filter );
            
            Assert( 0, i in positions );
            
            if Length( positions ) = 1 then
                
                plural := "";
                
            else
                
                plural := "s";
                
            fi;
            
            numerals := [ "a", "two", "three", "four", "five", "six", "seven", "eight", "nine" ];
            
            if Length( positions ) <= Length( numerals ) then
                
                numeral := numerals[Length( positions )];
                
            else
                
                numeral := String( Length( positions ) );
                
            fi;
            
            if filter = "object" then
                
                current_names := PhraseEnumeration( List( positions, i -> Concatenation( "$\\myboxed{", LaTeXName( names[i] ), "}$" ) ) );
                
                part := Concatenation( numeral, " object", plural, " ", current_names );
                
            elif filter = "morphism" then
                
                current_names := [ ];
                
                for i in positions do
                    
                    name := names[i];
                    
                    inner_parts := MySplitString( name, "__" );
                    
                    if Length( inner_parts ) = 3 then
                        
                        name := Concatenation( "\\myboxed{", LaTeXName( inner_parts[1] ), "}" );
                        source := Concatenation( "\\myboxed{", LaTeXName( inner_parts[2] ), "}" );
                        range := Concatenation( "\\myboxed{", LaTeXName( inner_parts[3] ), "}" );
                        
                        Add( current_names, Concatenation( "$", name, " : ", source, " \\to ", range, "$" ) );
                        
                    else
                        
                        Add( current_names, Concatenation( "$\\myboxed{", LaTeXName( name ), "}$" ) );
                        
                        #source := Concatenation( "s(", name, ")" );
                        #range := Concatenation( "t(", name, ")" );
                        
                    fi;
                    
                od;
                
                current_names := PhraseEnumeration( current_names );
                
                part := Concatenation( numeral, " morphism", plural, " ", current_names );
                
            #elif filter = "object_in_range_category_of_homomorphism_structure" then
            #    
            #    part := Concatenation( numeral, " object", plural, " ", current_names, " in the range category of the homomorphism structure" );
            #    
            #elif filter = "morphism_in_range_category_of_homomorphism_structure" then
            #    
            #    part := Concatenation( numeral, " morphism", plural, " ", current_names, " in the range category of the homomorphism structure" );
            #    
            else
                
                part := "an unhandled filter";
                
            fi;
            
            part := ReplacedString( part, "a object ", "an object " );
            
            Add( parts, part );
            
            Add( handled_input_filters, filter );
            
        od;
        
        text := Concatenation( text, " ", PhraseEnumerationWithOxfordComma( parts ) );
        
        tree := ENHANCED_SYNTAX_TREE( func );
        
        if not IsEmpty( tree.local_replacements ) then
            
            condition_func := StructuralCopy( tree );
            condition_func.local_replacements := [ ];
            
            Assert( 0, Length( condition_func.bindings.names ) = 1 );
            
            conditions := List( tree.local_replacements, function ( replacement )
                
                if replacement.dst.type = "EXPR_TRUE" then
                    
                    return StructuralCopy( replacement.src );
                    
                else
                    
                    return rec(
                        type := "EXPR_EQ",
                        left := StructuralCopy( replacement.src ),
                        right := StructuralCopy( replacement.dst ),
                    );
                    
                fi;
                
            end );
            
            condition_func.bindings.BINDING_RETURN_VALUE := Remove( conditions, 1 );
            
            for condition in conditions do
                
                condition_func.bindings.BINDING_RETURN_VALUE := rec(
                    type := "EXPR_AND",
                    left := condition_func.bindings.BINDING_RETURN_VALUE,
                    right := condition,
                );
                
            od;
            
            text := Concatenation( text, " such that\n", FunctionAsMathString( ENHANCED_SYNTAX_TREE_CODE( condition_func ), cat, input_filters ) );
            
        fi;
        
        #local_replacements_strings := [ ];
        #
        #for replacement in tree.local_replacements do
        #    
        #    replacement_func := StructuralCopy( tree );
        #    replacement_func.local_replacements := [ ];
        #    
        #    Assert( 0, Length( replacement_func.bindings.names ) = 1 );
        #    
        #    if replacement.dst.type = "EXPR_TRUE" then
        #        
        #        replacement_func.bindings.BINDING_RETURN_VALUE := StructuralCopy( replacement.src );
        #        
        #    else
        #        
        #        replacement_func.bindings.BINDING_RETURN_VALUE := rec(
        #            type := "EXPR_FUNCCALL",
        #            funcref := rec(
        #                type := "EXPR_REF_GVAR",
        #                gvar := "=",
        #            ),
        #            args := AsSyntaxTreeList( [
        #                StructuralCopy( replacement.src ),
        #                StructuralCopy( replacement.dst ),
        #            ] ),
        #        );
        #        
        #    fi;
        #    
        #    Add( local_replacements_strings, FunctionAsMathString( ENHANCED_SYNTAX_TREE_CODE( replacement_func ), cat, input_filters ) );
        #    
        #od;
        #
        #if not IsEmpty( local_replacements_strings ) then
        #    
        #    text := Concatenation( text, " such that ", JoinStringsWithSeparator( local_replacements_strings, "\n" ) );
        #    
        #fi;
        
        text := Concatenation( text, " we have that" );
        
    fi;
    
    result := FunctionAsMathString( func, cat, input_filters, "." );
    
    return Concatenation(
        "\\begin{", type, "}\n",
        text, "\n",
        result, "\n",
        "\\end{", type, "}"
    );
    
end );

BindGlobal( "StateLemma", function ( args... )
    
    return CallFuncList( STATE_THEOREM, Concatenation( [ "lemma" ], args ) );
    
end );

BindGlobal( "ApplyLogicTemplate", function ( logic_template )
  local func, cat, input_filters, old_logic_templates, old_tree, new_tree;
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM <> fail );
    
    func := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.func;
    cat := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.cat;
    input_filters := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.input_filters;
    
    if not CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.ever_compiled then
        
        func := CapJitCompiledFunction( func, cat, input_filters, "bool" );
        
        CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.func := func;
        CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.ever_compiled := true;
        
    fi;
    
    old_logic_templates := StructuralCopy( CAP_JIT_LOGIC_TEMPLATES );
    
    CapJitAddLogicTemplate( logic_template );
    
    old_tree := ENHANCED_SYNTAX_TREE( func );
    
    func := CapJitCompiledFunction( func, cat, input_filters, "bool" );
    
    new_tree := ENHANCED_SYNTAX_TREE( func );
    
    if CapJitIsEqualForEnhancedSyntaxTrees( old_tree, new_tree ) then
        
        Display( ENHANCED_SYNTAX_TREE_CODE( new_tree ) );
        
        Error( "applying the logic template did not have an effect" );
        
    fi;
    
    MakeReadWriteGlobal( "CAP_JIT_LOGIC_TEMPLATES" );
    
    CAP_JIT_LOGIC_TEMPLATES := old_logic_templates;
    
    MakeReadOnlyGlobal( "CAP_JIT_LOGIC_TEMPLATES" );
    
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.func := func;
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.ever_compiled := true;
    
end );

BindGlobal( "ApplyLogicTemplateAndReturnLaTeXString", function ( logic_template, args... )
  local func, cat, input_filters, old_logic_templates, latex_string, old_tree, new_tree;
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM <> fail );
    
    func := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.func;
    cat := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.cat;
    input_filters := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.input_filters;
    
    if not CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.ever_compiled then
        
        func := CapJitCompiledFunction( func, cat, input_filters, "bool" );
        
        CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.func := func;
        CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.ever_compiled := true;
        
    fi;
    
    old_logic_templates := StructuralCopy( CAP_JIT_LOGIC_TEMPLATES );
    
    latex_string := CallFuncList( CapJitAddLogicTemplateAndReturnLaTeXString, Concatenation( [ logic_template ], args ) );
    
    old_tree := ENHANCED_SYNTAX_TREE( func );
    
    func := CapJitCompiledFunction( func, cat, input_filters, "bool" );
    
    new_tree := ENHANCED_SYNTAX_TREE( func );
    
    if CapJitIsEqualForEnhancedSyntaxTrees( old_tree, new_tree ) then
        
        Display( ENHANCED_SYNTAX_TREE_CODE( new_tree ) );
        
        Error( "applying the logic template did not have an effect" );
        
    fi;
    
    MakeReadWriteGlobal( "CAP_JIT_LOGIC_TEMPLATES" );
    
    CAP_JIT_LOGIC_TEMPLATES := old_logic_templates;
    
    MakeReadOnlyGlobal( "CAP_JIT_LOGIC_TEMPLATES" );
    
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.func := func;
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.ever_compiled := true;
    
    return latex_string;
    
end );

BindGlobal( "ASSERT_THEOREM", function ( type )
  local func, cat, input_filters, tree;
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM <> fail );
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.type = type );
    
    func := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.func;
    cat := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.cat;
    input_filters := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.input_filters;
    
    tree := CapJitCompiledFunctionAsEnhancedSyntaxTree( func, "with_post_processing", cat, input_filters, "bool" );
    
    if tree.bindings.names = [ "RETURN_VALUE" ] and tree.bindings.BINDING_RETURN_VALUE.type = "EXPR_TRUE" then
        
        CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM := fail;
        
        return "\\qedhere";
        
    else
        
        Display( ENHANCED_SYNTAX_TREE_CODE( tree ) );
        
        Error( "function is not true, not resetting theorem" );
        
        return FunctionAsMathString( ENHANCED_SYNTAX_TREE_CODE( tree ), cat, input_filters );
        
    fi;
    
end );

BindGlobal( "AssertLemma", function ( )
    
    return ASSERT_THEOREM( "lemma" );
    
end );

BindGlobal( "PRINT_THEOREM", function ( type, args... )
  local func, cat, input_filters, tree;
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM <> fail );
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.type = type );
    
    func := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.func;
    cat := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.cat;
    input_filters := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.input_filters;
    
    func := CapJitCompiledFunction( func, cat, input_filters, "bool" );
    
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.func := func;
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.ever_compiled := true;
    
    return CallFuncList( FunctionAsMathString, Concatenation( [ func, cat, input_filters ], args ) );
    
end );

BindGlobal( "PrintLemma", function ( args... )
    
    return CallFuncList( PRINT_THEOREM, Concatenation( [ "lemma" ], args ) );
    
end );

BindGlobal( "CheckDerivationSourceAndRange", function ( )
  local cat, info, derivations, func1, template_func, compiled_tree1, template_tree, tree, func2, compiled_tree2, name, derivation;
    
    CapJitAddLogicFunction( function ( tree )
      local pre_func;
        
        #if not CAP_JIT_PROOF_ASSISTANT_MODE_ENABLED then
        #    
        #    return tree;
        #    
        #fi;
        
        Info( InfoCapJit, 1, "####" );
        Info( InfoCapJit, 1, "Apply logic for Source and Range of CAP operations." );
        
        pre_func := function ( tree, additional_arguments )
          local info, getter;
            
            if CapJitIsCallToGlobalFunction( tree, gvar -> gvar = "Source" or gvar = "Range" ) and tree.args.length = 1 and CapJitIsCallToGlobalFunction( tree.args.1, gvar -> gvar in RecNames( CAP_INTERNAL_METHOD_NAME_RECORD ) ) then
                
                info := CAP_INTERNAL_METHOD_NAME_RECORD.(tree.args.1.funcref.gvar);
                
                if Length( info.filter_list ) = tree.args.1.args.length then
                
                    if tree.funcref.gvar = "Source" and IsBound( info.output_source_getter ) then
                        
                        getter := info.output_source_getter;
                        
                    elif tree.funcref.gvar = "Range" and IsBound( info.output_range_getter ) then
                        
                        getter := info.output_range_getter;
                        
                    else
                        
                        return tree;
                        
                    fi;
                    
                    return rec(
                        type := "EXPR_FUNCCALL",
                        funcref := ENHANCED_SYNTAX_TREE( getter ),
                        args := tree.args.1.args,
                    );
                    
                fi;
                
            fi;
            
            return tree;
            
        end;
        
        return CapJitIterateOverTree( tree, pre_func, CapJitResultFuncCombineChildren, ReturnTrue, true );
        
    end );
    
    cat := DummyCategory( rec( list_of_operations_to_install := RecNames( CAP_INTERNAL_METHOD_NAME_RECORD ) ) );
    SetRangeCategoryOfHomomorphismStructure( cat, cat );
    StopCompilationAtCategory( cat );
    
    for name in SortedList( RecNames( CAP_INTERNAL_METHOD_NAME_RECORD ) ) do
        
        #if name <= "PushoutComplement" then
        #    
        #    continue;
        #    
        #fi;
        #
        #if name < "SingletonMorphism" then
        #    
        #    continue;
        #    
        #fi;
        
        name := "CocartesianCoevaluationMorphismWithGivenSource";
        
        info := CAP_INTERNAL_METHOD_NAME_RECORD.(name);
        
        if not info.return_type in [ "morphism", "morphism_in_range_category_of_homomorphism_structure", "other_morphism" ] then
            
            continue;
            
        fi;
        
        if false and IsBound( info.output_source_getter_string ) then
            
            Print( "#### ", name, "\n" );
            
            derivations := CAP_INTERNAL_DERIVATION_GRAPH!.derivations_by_target.(name);
            
            func1 := info.output_source_getter;
            
            template_func := EvalString( ReplacedStringViaRecord( """function ( arguments... )
                
                return Source( ReturnFirst( arguments... ) );
                
            end""", rec(
                arguments := info.input_arguments_names,
            ) ) );
            
            compiled_tree1 := ENHANCED_SYNTAX_TREE( CapJitCompiledFunction( func1, cat ) );
            
            template_tree := ENHANCED_SYNTAX_TREE( template_func );
            
            for derivation in derivations do
                
                if PositionSublist( DerivationName( derivation ), "with the WithGiven argument(s) dropped" ) <> fail then
                    
                    continue;
                    
                fi;
                
                if IsFilter( CategoryFilter( derivation ) ) then
                    
                    if IsSpecializationOfFilter( IsSkeletalCategory, CategoryFilter( derivation ) ) then
                        
                        continue;
                        
                    elif IsSpecializationOfFilter( IsStrictMonoidalCategory, CategoryFilter( derivation ) ) then
                        
                        continue;
                        
                    elif IsSpecializationOfFilter( IsStrictCartesianCategory, CategoryFilter( derivation ) ) then
                        
                        continue;
                        
                    elif IsSpecializationOfFilter( IsStrictCocartesianCategory, CategoryFilter( derivation ) ) then
                        
                        continue;
                        
                    fi;
                        
                fi;
                
                Print( DerivationName( derivation ), "\n" );
                Print( LocationFunc( DerivationFunction( derivation ) ), "\n" );
                
                tree := CapJitCopyWithNewFunctionIDs( template_tree );
                
                tree.bindings.BINDING_RETURN_VALUE.args.1.funcref := ENHANCED_SYNTAX_TREE( DerivationFunction( derivation ) );
                
                func2 := ENHANCED_SYNTAX_TREE_CODE( tree );
                
                compiled_tree2 := ENHANCED_SYNTAX_TREE( CapJitCompiledFunction( func2, cat ) );
                
                if not CapJitIsEqualForEnhancedSyntaxTrees( compiled_tree1, compiled_tree2 ) then
                    
                    Display( func1 );
                    Display( func2 );
                    
                    Display( ENHANCED_SYNTAX_TREE_CODE( compiled_tree1 ) );
                    Display( ENHANCED_SYNTAX_TREE_CODE( compiled_tree2 ) );
                    
                    Error("asd");
                    
                fi;
                
            od;
            
            Print( "\n" );
            
        fi;
        
        if IsBound( info.output_range_getter_string ) then
            
            Print( "#### ", name, "\n" );
            
            derivations := CAP_INTERNAL_DERIVATION_GRAPH!.derivations_by_target.(name);
            
            func1 := info.output_range_getter;
            
            template_func := EvalString( ReplacedStringViaRecord( """function ( arguments... )
                
                return Range( ReturnFirst( arguments... ) );
                
            end""", rec(
                arguments := info.input_arguments_names,
            ) ) );
            
            compiled_tree1 := ENHANCED_SYNTAX_TREE( CapJitCompiledFunction( func1, cat ) );
            
            template_tree := ENHANCED_SYNTAX_TREE( template_func );
            
            for derivation in derivations do
                
                if PositionSublist( DerivationName( derivation ), "with the WithGiven argument(s) dropped" ) <> fail then
                    
                    continue;
                    
                fi;
                
                if IsFilter( CategoryFilter( derivation ) ) then
                    
                    if IsSpecializationOfFilter( IsSkeletalCategory, CategoryFilter( derivation ) ) then
                        
                        continue;
                        
                    elif IsSpecializationOfFilter( IsStrictMonoidalCategory, CategoryFilter( derivation ) ) then
                        
                        continue;
                        
                    elif IsSpecializationOfFilter( IsStrictCartesianCategory, CategoryFilter( derivation ) ) then
                        
                        continue;
                        
                    elif IsSpecializationOfFilter( IsStrictCocartesianCategory, CategoryFilter( derivation ) ) then
                        
                        continue;
                        
                    fi;
                        
                fi;
                
                Print( DerivationName( derivation ), "\n" );
                Print( LocationFunc( DerivationFunction( derivation ) ), "\n" );
                
                tree := CapJitCopyWithNewFunctionIDs( template_tree );
                
                tree.bindings.BINDING_RETURN_VALUE.args.1.funcref := ENHANCED_SYNTAX_TREE( DerivationFunction( derivation ) );
                
                func2 := ENHANCED_SYNTAX_TREE_CODE( tree );
                
                compiled_tree2 := ENHANCED_SYNTAX_TREE( CapJitCompiledFunction( func2, cat ) );
                
                if not CapJitIsEqualForEnhancedSyntaxTrees( compiled_tree1, compiled_tree2 ) then
                    
                    Display( func1 );
                    Display( func2 );
                    
                    Display( ENHANCED_SYNTAX_TREE_CODE( compiled_tree1 ) );
                    Display( ENHANCED_SYNTAX_TREE_CODE( compiled_tree2 ) );
                    
                    Error("asd");
                    
                fi;
                
            od;
            
            Print( "\n" );
            
        fi;
        
    od;
    
    #CAP_INTERNAL_DERIVATION_GRAPH
    
end );
