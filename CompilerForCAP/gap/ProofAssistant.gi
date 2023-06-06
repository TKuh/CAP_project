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

BindGlobal( "SetCurrentCategory", function ( category, description, symbols... )
    
    CAP_JIT_PROOF_ASSISTANT_CURRENT_CATEGORY := rec( category := category, description := description );
    
    Assert( 0, Length( symbols ) <= 1 );
    
    if Length( symbols ) = 1 then
        
        symbols := symbols[1];
        
    else
        
        symbols := [ ];
        
    fi;
    
    CAP_JIT_PROOF_ASSISTANT_CURRENT_CATEGORY_SYMBOLS := symbols;
    
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
  local cat, input_filters, text, names, handled_input_filters, parts, filter, positions, plural, numerals, numeral, current_names, part, name, inner_parts, source, range, tree, condition_func, conditions, result, i, condition, latex_string;
    
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
        cat := cat,
        input_filters := input_filters,
        ever_compiled := false,
    );
    
    if Length( input_filters ) = 0 then
        
        Error( "cannot handle theorems without input" );
        
    else
        
        if CAP_JIT_PROOF_ASSISTANT_CURRENT_CATEGORY = fail then
            
            text := "";
            
        else
            
            text := Concatenation( "In ", CAP_JIT_PROOF_ASSISTANT_CURRENT_CATEGORY.description, " the following statement holds true: " );
            
        fi;
        
        text := Concatenation( text, "For" );
        
        names := NamesLocalVariablesFunction( func );
        
        Assert( 0, Length( names ) >= Length( input_filters ) );
        
        if CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION <> fail then
            
            # TODO: only names of things in the category
            names := List( names, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION.variable_name_translator );
            
        fi;
        
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
            
            # TODO: only box things in the category
            if filter = "integer" then
                
                current_names := PhraseEnumeration( List( positions, i -> Concatenation( "$", LaTeXName( names[i] ), "$" ) ) );
                
                part := Concatenation( numeral, " integer", plural, " ", current_names );
                
            elif filter = "object" then
                
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
            elif filter = "list_of_objects" then
                
                current_names := [ ];
                
                for i in positions do
                    
                    name := names[i];
                    
                    inner_parts := MySplitString( name, "__" );
                    
                    Assert( 0, Length( inner_parts ) > 0 );
                    
                    if Length( inner_parts ) = 1 then
                        
                        Add( current_names, Concatenation( "$", LaTeXName( name ), "$" ) );
                        
                    elif Length( inner_parts ) = 2 then
                        
                        name := LaTeXName( inner_parts[1] );
                        length := LaTeXName( inner_parts[2] );
                        
                        Add( current_names, Concatenation( "$(", name , "_1,\\dots,", name, "_", length, ")$" ) );
                        
                    else
                        
                        Error( "wrong usage" );
                        
                    fi;
                    
                od;
                
                current_names := PhraseEnumeration( current_names );
                
                part := Concatenation( numeral, " list", plural, " of objects ", current_names );
                
            else
                
                part := Concatenation( "TODO: ", ReplacedString( filter, "_", "\\_" ) );
                
            fi;
            
            part := ReplacedString( part, "a object ", "an object " );
            
            Add( parts, part );
            
            Add( handled_input_filters, filter );
            
        od;
        
        if Length( input_filters ) > 1 then
            
            text := Concatenation( text, " ", PhraseEnumerationWithOxfordComma( parts ) );
            
        fi;
        
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
    
    latex_string := Concatenation(
        "\\begin{", type, "}\n",
        text, "\n",
        result, "\n",
        "\\end{", type, "}"
    );
    
    # twice to resolve operations added by local replacements
    tree := CapJitCompiledFunctionAsEnhancedSyntaxTree( func, "with_post_processing", cat, input_filters, "bool" );
    tree := CapJitCompiledFunctionAsEnhancedSyntaxTree( tree, "with_post_processing" );
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.tree := tree;
    
    if tree.bindings.names = [ "RETURN_VALUE" ] and tree.bindings.BINDING_RETURN_VALUE.type = "EXPR_TRUE" then
        
        latex_string := Concatenation(
            latex_string, "\n\n",
            "\\begin{proof}\n",
            "This is immediate from the construction.\n",
            "\\end{proof}\n"
        );
        
        CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM := fail;
        
    fi;
    
    return latex_string;
    
end );

BindGlobal( "StateLemma", function ( args... )
    
    return CallFuncList( STATE_THEOREM, Concatenation( [ "lemma" ], args ) );
    
end );

BindGlobal( "ApplyLogicTemplate", function ( logic_template )
  local tree, cat, input_filters, old_tree, new_tree;
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM <> fail );
    
    tree := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.tree;
    cat := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.cat;
    input_filters := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.input_filters;
    
    logic_template := ShallowCopy( logic_template );
    
    if not IsBound( logic_template.number_of_applications ) then
        
        logic_template.number_of_applications := 1;
        
    fi;
    
    CapJitAddLogicTemplate( logic_template );
    
    old_tree := StructuralCopy( tree );
    
    new_tree := CapJitCompiledFunctionAsEnhancedSyntaxTree( tree, "with_post_processing" );
    
    if ForAny( CAP_JIT_LOGIC_TEMPLATES, t -> t.number_of_applications <> infinity and t.number_of_applications <> 0 ) then
        
        Display( ENHANCED_SYNTAX_TREE_CODE( new_tree ) );
        
        Perform( CAP_JIT_LOGIC_TEMPLATES, function ( t ) if t.number_of_applications <> infinity and t.number_of_applications <> 0 then Display( t.number_of_applications ); fi; end );
        
        Error( "there are logic templates with a non-zero number of remaining applications" );
        
    fi;
    
    if CapJitIsEqualForEnhancedSyntaxTrees( old_tree, new_tree ) then
        
        Display( ENHANCED_SYNTAX_TREE_CODE( new_tree ) );
        
        Error( "applying the logic template did not change the tree" );
        
    fi;
    
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.tree := new_tree;
    
end );

BindGlobal( "ApplyLogicTemplateAndReturnLaTeXString", function ( logic_template, args... )
  local tree, cat, input_filters, latex_string, old_tree, new_tree;
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM <> fail );
    
    tree := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.tree;
    cat := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.cat;
    input_filters := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.input_filters;
    
    logic_template := ShallowCopy( logic_template );
    
    if not IsBound( logic_template.number_of_applications ) then
        
        logic_template.number_of_applications := 1;
        
    fi;
    
    latex_string := CallFuncList( CapJitAddLogicTemplateAndReturnLaTeXString, Concatenation( [ logic_template ], args ) );
    
    old_tree := StructuralCopy( tree );
    
    new_tree := CapJitCompiledFunctionAsEnhancedSyntaxTree( tree, "with_post_processing" );
    
    if ForAny( CAP_JIT_LOGIC_TEMPLATES, t -> t.number_of_applications <> infinity and t.number_of_applications <> 0 ) then
        
        Display( ENHANCED_SYNTAX_TREE_CODE( new_tree ) );
        
        Perform( CAP_JIT_LOGIC_TEMPLATES, function ( t ) if t.number_of_applications <> infinity and t.number_of_applications <> 0 then Display( t.number_of_applications ); fi; end );
        
        Error( "there are logic templates with a non-zero number of remaining applications" );
        
    fi;
    
    if CapJitIsEqualForEnhancedSyntaxTrees( old_tree, new_tree ) then
        
        Display( ENHANCED_SYNTAX_TREE_CODE( new_tree ) );
        
        Error( "applying the logic template did not change the tree" );
        
    fi;
    
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.tree := new_tree;
    
    return latex_string;
    
end );

BindGlobal( "ASSERT_THEOREM", function ( type )
  local cat, input_filters, tree;
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM <> fail );
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.type = type );
    
    tree := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.tree;
    cat := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.cat;
    input_filters := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.input_filters;
    
    if tree.bindings.names = [ "RETURN_VALUE" ] and tree.bindings.BINDING_RETURN_VALUE.type = "EXPR_TRUE" then
        
        CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM := fail;
        
        return "With this, the claim follows and we let CompilerForCAP end the proof.\\qedhere";
        
    else
        
        Display( ENHANCED_SYNTAX_TREE_CODE( tree ) );
        
        Error( "function is not true, not resetting theorem" );
        
        return FunctionAsMathString( ENHANCED_SYNTAX_TREE_CODE( tree ), cat, input_filters );
        
    fi;
    
end );

BindGlobal( "AssertLemma", function ( )
    
    return ASSERT_THEOREM( "lemma" );
    
end );

BindGlobal( "RESET_THEOREM", function ( type )
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM <> fail );
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.type = type );
    
    Print( "WARNING: Resetting ", type, ".\n" );
    
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM := fail;
    
end );

BindGlobal( "ResetLemma", function ( )
    
    RESET_THEOREM( "lemma" );
    
end );

BindGlobal( "PRINT_THEOREM", function ( type, args... )
  local tree, cat, input_filters, latex_string;
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM <> fail );
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.type = type );
    
    tree := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.tree;
    cat := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.cat;
    input_filters := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.input_filters;
    
    # TODO
    latex_string := CallFuncList( FunctionAsMathString, Concatenation( [ tree, cat, input_filters ], args ) : raw := false );
    
    #latex_string := Concatenation( "\\text{(claim)}\\quad ", latex_string );
    
    return latex_string;
    
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

specifications := rec(
    PreCompose := rec(
        preconditions := """
            CapJitAddLocalReplacement( Source( beta ), Range( alpha ) );
        """,
        postconditions := [
            rec(
                # composition is associative
                input_types := [ "category", "morphism", "morphism", "morphism" ],
                func := function( cat, alpha, beta, gamma )
                    
                    CapJitAddLocalReplacement( Source( beta ), Range( alpha ) );
                    CapJitAddLocalReplacement( Range( beta ), Source( gamma ) );
                    
                    return IsCongruentForMorphisms( cat, PreCompose( cat, PreCompose( cat, alpha, beta ), gamma ), PreCompose( cat, alpha, PreCompose( cat, beta, gamma ) ) );
                    
                end,
            ),
        ],
    ),
    IdentityMorphism := rec(
        postconditions := [
            rec(
                # identity is left-neutral
                input_types := [ "category", "morphism" ],
                func := { cat, alpha } -> IsCongruentForMorphisms( cat, PreCompose( cat, IdentityMorphism( cat, Source( alpha ) ), alpha ), alpha ),
            ),
            rec(
                # identity is right-neutral
                input_types := [ "category", "morphism" ],
                func := { cat, alpha } -> IsCongruentForMorphisms( cat, PreCompose( cat, alpha, IdentityMorphism( cat, Range( alpha ) ) ), alpha ),
            ),
        ],
    ),
    AdditionForMorphisms := rec(
        preconditions := """
            CapJitAddLocalReplacement( Source( beta ), Source( alpha ) );
            CapJitAddLocalReplacement( Range( beta ), Range( alpha ) );
        """,
        postconditions := [
            rec(
                # addition is associative
                input_types := [ "category", "morphism", "morphism", "morphism" ],
                func := function( cat, alpha, beta, gamma )
                    
                    CapJitAddLocalReplacement( Source( beta ), Source( alpha ) );
                    CapJitAddLocalReplacement( Range( beta ), Range( alpha ) );
                    CapJitAddLocalReplacement( Source( gamma ), Source( alpha ) );
                    CapJitAddLocalReplacement( Range( gamma ), Range( alpha ) );
                    
                    return IsCongruentForMorphisms( cat, AdditionForMorphisms( cat, AdditionForMorphisms( cat, alpha, beta ), gamma ), AdditionForMorphisms( cat, alpha, AdditionForMorphisms( cat, beta, gamma ) ) );
                    
                end,
            ),
            rec(
                # addition is commutative
                input_types := [ "category", "morphism", "morphism" ],
                func := function ( cat, alpha, beta )
                    
                    CapJitAddLocalReplacement( Source( beta ), Source( alpha ) );
                    CapJitAddLocalReplacement( Range( beta ), Range( alpha ) );
                    
                    return IsCongruentForMorphisms( cat,
                        AdditionForMorphisms( cat, alpha, beta ),
                        AdditionForMorphisms( cat, beta, alpha )
                    );
                    
                end,
            )
        ],
    ),
    ZeroMorphism := rec(
        postconditions := [
            rec(
                # zero is left-neutral
                input_types := [ "category", "morphism" ],
                func := { cat, alpha } -> IsCongruentForMorphisms( cat, AdditionForMorphisms( cat, ZeroMorphism( cat, Source( alpha ), Range( alpha ) ), alpha ), alpha ),
            ),
            rec(
                # zero is right-neutral
                input_types := [ "category", "morphism" ],
                func := { cat, alpha } -> IsCongruentForMorphisms( cat, AdditionForMorphisms( cat, alpha, ZeroMorphism( cat, Source( alpha ), Range( alpha ) ) ), alpha ),
            ),
        ],
    ),
    AdditiveInverseForMorphisms := rec(
        postconditions := [
            rec(
                # additive inverse is left-inverse
                input_types := [ "category", "morphism" ],
                func := { cat, alpha } -> IsCongruentForMorphisms( cat, AdditionForMorphisms( cat, AdditiveInverseForMorphisms( cat, alpha ), alpha ), ZeroMorphism( cat, Source( alpha ), Range( alpha ) ) ),
            ),
            rec(
                # additive inverse is right-inverse
                input_types := [ "category", "morphism" ],
                func := { cat, alpha } -> IsCongruentForMorphisms( cat, AdditionForMorphisms( cat, alpha, AdditiveInverseForMorphisms( cat, alpha ) ), ZeroMorphism( cat, Source( alpha ), Range( alpha ) ) ),
            ),
        ],
    ),
    ZeroObject := rec( ),
    UniversalMorphismIntoZeroObject := rec(
        postconditions := [
            rec(
                input_types := [ "category", "morphism" ],
                func := function ( cat, u )
                    
                    CapJitAddLocalReplacement( Range( u ), ZeroObject( cat ) );
                    
                    return IsCongruentForMorphisms( cat,
                        UniversalMorphismIntoZeroObject( cat, Source( u ) ),
                        u
                    );
                    
                end,
            ),
        ],
    ),
    UniversalMorphismFromZeroObject := rec(
        postconditions := [
            rec(
                input_types := [ "category", "morphism" ],
                func := function ( cat, u )
                    
                    CapJitAddLocalReplacement( Source( u ), ZeroObject( cat ) );
                    
                    return IsCongruentForMorphisms( cat,
                        UniversalMorphismFromZeroObject( cat, Range( u ) ),
                        u
                    );
                    
                end,
            ),
        ],
    ),
    DirectSum := rec( ),
    KernelEmbedding := rec(
        postconditions := [
            rec(
                input_types := [ "category", "morphism" ],
                func := { cat, alpha } -> IsZeroForMorphisms( cat, PreCompose( cat, KernelEmbedding( cat, alpha ), alpha ) ),
            ),
        ],
    ),
    KernelLift := rec(
        preconditions := """
            CapJitAddLocalReplacement( Range( tau ), Source( alpha ) );
            CapJitAddLocalReplacement( IsZeroForMorphisms( PreCompose( tau, alpha ) ), true );
        """,
        postconditions := [
        ],
    ),
);

propositions := rec(
    is_category := rec(
        description := "is indeed a category",
        operations := [ "PreCompose", "IdentityMorphism" ],
    ),
    is_pre_additive_category := rec(
        description := "is a pre-additive category",
        operations := [ "AdditionForMorphisms", "ZeroMorphism", "AdditiveInverseForMorphisms" ],
    ),
    has_zero_object := rec(
        description := "has a zero object",
        operations := [ "ZeroObject", "UniversalMorphismIntoZeroObject", "UniversalMorphismFromZeroObject" ],
    ),
    has_direct_sums_via_components_of_morphisms := rec(
        description := "has direct sums",
        operations := [ "DirectSum" ],
    ),
    has_kernels := rec(
        description := "has kernels",
        operations := [ "KernelEmbedding", "KernelLift" ],
    ),
);

enhance_propositions := function ( propositions )
  local prop, info, specification, preconditions, is_well_defined, id, operation;
    
    for id in RecNames( propositions ) do
        
        prop := propositions.(id);
        
        Assert( 0, not IsBound( prop.lemmata ) );
        
        prop.lemmata := [ ];
        
        for operation in prop.operations do
            
            Assert( 0, IsBound( CAP_INTERNAL_METHOD_NAME_RECORD.(operation) ) );
            Assert( 0, IsBound( specifications.(operation) ) );
            
            info := CAP_INTERNAL_METHOD_NAME_RECORD.(operation);
            
            specification := specifications.(operation);
            
            if IsBound( specification.preconditions ) then
                
                preconditions := specification.preconditions;
                
            else
                
                preconditions := "";
                
            fi;
            
            ## check well-definedness
            
            if info.return_type = "object" then
                
                is_well_defined := "IsWellDefinedForObjects";
                
            elif info.return_type = "morphism" then
                
                is_well_defined := "IsWellDefinedForMorphisms";
                
            else
                
                Error( "return_type ", info.return_type, " is not supported yet when checking well-definedness" );
                
            fi;
            
            Add( prop.lemmata, rec(
                input_types := info.filter_list,
                func := EvalString( ReplacedStringViaRecord(
                    """function ( input_arguments... )
                        
                        preconditions
                        
                        return is_well_defined( cat, operation( input_arguments... ) );
                        
                    end""",
                    rec(
                        is_well_defined := is_well_defined,
                        operation := operation,
                        input_arguments := info.input_arguments_names,
                        preconditions := preconditions,
                    )
                ) )
            ) );
            
            ## check source and range (if required)
            
            if info.return_type = "object" then
                
                # nothing to do
            
            elif info.return_type = "morphism" then
                
                Add( prop.lemmata, rec(
                    input_types := info.filter_list,
                    func := EvalString( ReplacedStringViaRecord(
                        """function ( input_arguments... )
                            
                            preconditions
                            
                            return IsEqualForObjects( cat, Source( operation( input_arguments... ) ), output_source_getter );
                            
                        end""",
                        rec(
                            operation := operation,
                            output_source_getter := info.output_source_getter_string,
                            input_arguments := info.input_arguments_names,
                            preconditions := preconditions,
                        )
                    ) )
                ) );
                
                Add( prop.lemmata, rec(
                    input_types := info.filter_list,
                    func := EvalString( ReplacedStringViaRecord(
                        """function ( input_arguments... )
                            
                            preconditions
                            
                            return IsEqualForObjects( cat, Range( operation( input_arguments... ) ), output_range_getter );
                            
                        end""",
                        rec(
                            operation := operation,
                            output_range_getter := info.output_range_getter_string,
                            input_arguments := info.input_arguments_names,
                            preconditions := preconditions,
                        )
                    ) )
                ) );
                
            else
                
                Error( "return_type ", info.return_type, " is not supported yet when checking source and range" );
                
            fi;
            
            if IsBound( specification.postconditions ) then
                
                prop.lemmata := Concatenation( prop.lemmata, specification.postconditions );
                
            fi;
            
        od;
        
    od;
    
end;

enhance_propositions( propositions );

CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION := fail;

StateProposition := function ( cat, cat_description, category_symbols, proposition_id, variable_name_translator )
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION = fail );
    
    if not IsBound( propositions.(proposition_id) ) then
        
        Error( "unknown proposition ", proposition_id );
        
    fi;
    
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION := rec( );
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION.proposition := propositions.(proposition_id);
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION.active_lemma_index := 0;
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION.variable_name_translator := variable_name_translator;
    
    SetCurrentCategory( cat, cat_description, category_symbols );
    
    return Concatenation(
        "\\begin{proposition}\n",
        UppercaseString(cat_description{[ 1 ]}), cat_description{[ 2 .. Length( cat_description ) ]}, " ", CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION.proposition.description, ".\n",
        "\\end{proposition}"
    );
    
end;

StateNextLemma := function ( )
  local active_lemma_index, lemmata;
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION <> fail );
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM = fail );
    
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION.active_lemma_index := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION.active_lemma_index + 1;
    
    active_lemma_index := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION.active_lemma_index;
    lemmata := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION.proposition.lemmata;
    
    if active_lemma_index > Length( lemmata ) then
        
        Error( "All lemmata proven." );
        return;
        
    fi;
    
    return StateLemma( lemmata[active_lemma_index].func, lemmata[active_lemma_index].input_types );
    
end;

AssertProposition := function ( )
  local cat_description, proposition_description;
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION <> fail );
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM = fail );
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION.active_lemma_index = Length( CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION.proposition.lemmata ) );
    
    cat_description := CAP_JIT_PROOF_ASSISTANT_CURRENT_CATEGORY.description;
    proposition_description := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION.proposition.description;
    
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION := fail;
    CAP_JIT_PROOF_ASSISTANT_CURRENT_CATEGORY := fail;
    
    return Concatenation(
        "With this, we have shown:\n",
        UppercaseString(cat_description{[ 1 ]}), cat_description{[ 2 .. Length( cat_description ) ]}, " ", proposition_description, ".\n"
    );
    
end;

ResetProposition := function ( )
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION <> fail );
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM = fail );
    
    Print( "WARNING: Resetting proposition.\n" );
    
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_PROPOSITION := fail;
    
end;

AssumeValidInputs := function ( )
  local tree, cat, input_filters, pre_func;
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM <> fail );
    
    tree := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.tree;
    cat := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.cat;
    input_filters := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.input_filters;
    
    # assert that the tree is well-typed
    Assert( 0, IsBound( tree.bindings.BINDING_RETURN_VALUE.data_type ) );
    
    pre_func := function ( tree, additional_arguments )
        
        # properties like IsZeroForMorphisms can be applied to applied to two arguments, a category and a morphism
        if CapJitIsCallToGlobalFunction( tree, x -> IsFilter( ValueGlobal( x ) ) ) and tree.args.length = 1 then
            
            if IsSpecializationOfFilter( ValueGlobal( tree.funcref.gvar ), tree.args.1.data_type.filter ) then
                
                return rec( type := "EXPR_TRUE" );
                
            fi;
            
            # We do not want to return `false` in the `else` case, for example because `IsList( Pair( 1, 2 ) )` is `true` but `IsNTuple` does not imply `IsList`.
            
        fi;
        
        if CapJitIsCallToGlobalFunction( tree, "IsWellDefinedForObjects" ) and tree.args.length = 2 then
            
            Assert( 0, IsSpecializationOfFilter( "category", tree.args.1.data_type.filter ) );
            Assert( 0, IsSpecializationOfFilter( ObjectFilter( tree.args.1.data_type.category ), tree.args.2.data_type.filter ) );
            
            return rec( type := "EXPR_TRUE" );
            
        fi;
        
        if CapJitIsCallToGlobalFunction( tree, "IsWellDefinedForMorphisms" ) and tree.args.length = 2 then
            
            Assert( 0, IsSpecializationOfFilter( "category", tree.args.1.data_type.filter ) );
            Assert( 0, IsSpecializationOfFilter( MorphismFilter( tree.args.1.data_type.category ), tree.args.2.data_type.filter ) );
            
            return rec( type := "EXPR_TRUE" );
            
        fi;
        
        return tree;
        
    end;
    
    tree := CapJitIterateOverTree( tree, pre_func, CapJitResultFuncCombineChildren, ReturnTrue, true );
    
    tree := CapJitCompiledFunctionAsEnhancedSyntaxTree( tree, "with_post_processing" );
    
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.tree := tree;
    
    return "We let CompilerForCAP assume that all inputs are valid.";
    
end;
