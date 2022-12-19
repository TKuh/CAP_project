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

CAP_JIT_PROOF_ASSISTANT_MODE_CATEGORY_DESCRIPTION := "not set";

BindGlobal( "SetCategoryDescription", function ( string )
    
    CAP_JIT_PROOF_ASSISTANT_MODE_CATEGORY_DESCRIPTION := string;
    
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

BindGlobal( "StateLemma", function ( proposition, cat, input_filters )
  local text, names, handled_input_filters, parts, filter, positions, plural, numerals, numeral, current_names, part, tree, local_replacements_strings, func, args, result, i, replacement;
    
    if Length( input_filters ) = 0 then
        
        Error( "cannot handle statements without input" );
        
    elif Length( input_filters ) = 1 then
        
        Error( "TODO" );
        
    else
        
        text := "For";
        
        names := NamesLocalVariablesFunction( proposition );
        
        Assert( 0, Length( names ) >= Length( input_filters ) );
        
        handled_input_filters := [ ];
        
        parts := [ ];
        
        for i in [ 2 .. Length( input_filters ) ] do
            
            #if i > 2 and (i < Length( input_filters ) or Length( input_filters ) > 3) then
            #    
            #    text := Concatenation( text, "," );
            #    
            #fi;
            #
            #if i = Length( input_filters ) then
            #    
            #    text := Concatenation( text, " and" );
            #    
            #fi;
            
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
        
        tree := ENHANCED_SYNTAX_TREE( proposition );
        
        local_replacements_strings := [ ];
        
        for replacement in tree.local_replacements do
            
            func := StructuralCopy( tree );
            func.local_replacements := [ ];
            
            Assert( 0, Length( func.bindings.names ) = 1 );
            
            func.bindings.BINDING_RETURN_VALUE := rec(
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
            
            Add( local_replacements_strings, FunctionAsMathString( ENHANCED_SYNTAX_TREE_CODE( func ), cat, input_filters ) );
            
        od;
        
        if not IsEmpty( local_replacements_strings ) then
            
            text := Concatenation( text, " such that ", JoinStringsWithSeparator( local_replacements_strings, "\n" ) );
            
        fi;
        
        text := Concatenation( text, " we have" );
        
    fi;
    
    result := FunctionAsMathString( proposition, cat, input_filters );
    
    return Concatenation( "\\begin{lemma}\n", text, "\n", result, "\\end{lemma}\n" );
    
end );
