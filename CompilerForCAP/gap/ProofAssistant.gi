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

BindGlobal( "StateTheorem", function ( func, args... )
  local cat, input_filters, type, text, names, handled_input_filters, parts, filter, positions, plural, numerals, numeral, current_names, part, tree, local_replacements_strings, replacement_func, result, i, replacement;
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ENABLED );
    
    if CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM <> fail then
        
        Display( "WARNING: overwriting existing active theorem" );
        
    fi;
    
    if not IsCapCategory( args[1] ) then
        
        if CAP_JIT_PROOF_ASSISTANT_CURRENT_CATEGORY = fail then
            
            Error( "The category can only be omitted if `SetCurrentCategory` has been called before." );
            
        fi;
        
        Add( args, CAP_JIT_PROOF_ASSISTANT_CURRENT_CATEGORY.category, 1 );
        
    fi;
    
    cat := Remove( args, 1 );
    input_filters := Remove( args, 1 );
    
    if Length( args ) = 0 then
        
        type := "theorem";
        
    elif Length( args ) = 1 then
        
        type := args[1];
        
    else
        
        Error( "StateTheorem must be called with at most 4 arguments" );
        
    fi;
    
    CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM := rec(
        type := type,
        claim := func,
        func := func,
        cat := cat,
        input_filters := input_filters,
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
            
            current_names := PhraseEnumeration( List( positions, i -> Concatenation( "$", LaTeXName( names[i] ), "$" )  ));
            
            if filter = "object" then
                
                part := Concatenation( numeral, " object", plural, " ", current_names );
                
            elif filter = "morphism" then
                
                part := Concatenation( numeral, " morphism", plural, " ", current_names );
                
            elif filter = "object_in_range_category_of_homomorphism_structure" then
                
                part := Concatenation( numeral, " object", plural, " ", current_names, " in the range category of the homomorphism structure" );
                
            elif filter = "morphism_in_range_category_of_homomorphism_structure" then
                
                part := Concatenation( numeral, " morphism", plural, " ", current_names, " in the range category of the homomorphism structure" );
                
            else
                
                part := "an unhandled filter";
                
            fi;
            
            part := ReplacedString( part, "a object ", "an object " );
            
            Add( parts, part );
            
            Add( handled_input_filters, filter );
            
        od;
        
        text := Concatenation( text, " ", PhraseEnumerationWithOxfordComma( parts ) );
        
        tree := ENHANCED_SYNTAX_TREE( func );
        
        local_replacements_strings := [ ];
        
        for replacement in tree.local_replacements do
            
            replacement_func := StructuralCopy( tree );
            replacement_func.local_replacements := [ ];
            
            Assert( 0, Length( replacement_func.bindings.names ) = 1 );
            
            replacement_func.bindings.BINDING_RETURN_VALUE := rec(
                type := "EXPR_FUNCCALL",
                funcref := rec(
                    type := "EXPR_REF_GVAR",
                    gvar := "=",
                ),
                args := AsSyntaxTreeList( [
                    StructuralCopy( replacement.src ),
                    StructuralCopy( replacement.dst),
                ] ),
            );
            
            Add( local_replacements_strings, FunctionAsMathString( ENHANCED_SYNTAX_TREE_CODE( replacement_func ), cat, input_filters ) );
            
        od;
        
        if not IsEmpty( local_replacements_strings ) then
            
            text := Concatenation( text, " such that ", JoinStringsWithSeparator( local_replacements_strings, "\n" ) );
            
        fi;
        
        text := Concatenation( text, " we have" );
        
    fi;
    
    result := FunctionAsMathString( func, cat, input_filters );
    
    return Concatenation(
        "\\begin{", type, "}\n",
        text, "\n",
        result, "\n",
        "\\end{", type, "}"
    );
    
end );

BindGlobal( "StateLemma", function ( args... )
    
    return CallFuncList( StateTheorem, Concatenation( args, [ "lemma" ] ) );
    
end );

BindGlobal( "ApplyLogicTemplate", function ( logic_template )
  local func, cat, input_filters, old_logic_templates, old_tree, new_tree;
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM <> fail );
    
    func := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.func;
    cat := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.cat;
    input_filters := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.input_filters;
    
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
    
end );

BindGlobal( "ApplyLogicTemplateAndReturnLaTeXString", function ( logic_template, args... )
  local func, cat, input_filters, old_logic_templates, latex_string, old_tree, new_tree;
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM <> fail );
    
    func := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.func;
    cat := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.cat;
    input_filters := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.input_filters;
    
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
    
    return latex_string;
    
end );

BindGlobal( "AssertTheorem", function ( args... )
  local type, func, cat, input_filters, tree;
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM <> fail );
    
    if Length( args ) = 0 then
        
        type := "theorem";
        
    elif Length( args ) = 1 then
        
        type := args[1];
        
    else
        
        Error( "AssertTheorem must be called with at most one argument" );
        
    fi;
    
    Assert( 0, type = CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.type );
    
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
    
    return AssertTheorem( "lemma" );
    
end );

BindGlobal( "PrintTheorem", function ( args... )
  local type, func, cat, input_filters, tree;
    
    Assert( 0, CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM <> fail );
    
    if Length( args ) = 0 then
        
        type := "theorem";
        
    elif Length( args ) = 1 then
        
        type := args[1];
        
    else
        
        Error( "PrintTheorem must be called with at most one argument" );
        
    fi;
    
    Assert( 0, type = CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.type );
    
    func := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.func;
    cat := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.cat;
    input_filters := CAP_JIT_PROOF_ASSISTANT_MODE_ACTIVE_THEOREM.input_filters;
    
    tree := CapJitCompiledFunctionAsEnhancedSyntaxTree( func, "with_post_processing", cat, input_filters, "bool" );
    
    return FunctionAsMathString( ENHANCED_SYNTAX_TREE_CODE( tree ), cat, input_filters );
    
end );

BindGlobal( "PrintLemma", function ( )
    
    return PrintTheorem( "lemma" );
    
end );
