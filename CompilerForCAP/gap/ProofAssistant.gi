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

BindGlobal( "StateLemma", function ( proposition, cat, input_filters )
  local text, names, filter, name, result, i;
    
    if Length( input_filters ) = 0 then
        
        Error( "cannot handle statements without input" );
        
    elif Length( input_filters ) = 1 then
        
        Error( "TODO" );
        
    else
        
        text := "For";
        
        names := NamesLocalVariablesFunction( proposition );
        
        Assert( 0, Length( names ) >= Length( input_filters ) );
        
        for i in [ 2 .. Length( input_filters ) ] do
            
            if i > 2 and (i < Length( input_filters ) or Length( input_filters ) > 3) then
                
                text := Concatenation( text, "," );
                
            fi;
            
            if i = Length( input_filters ) then
                
                text := Concatenation( text, " and" );
                
            fi;
            
            filter := input_filters[i];
            name := names[i];
            
            if filter = "object" then
                
                text := Concatenation( text, " an object ", name );
                
            elif filter = "morphism" then
                
                text := Concatenation( text, " a morphism ", name );
                
            else
                
                text := Concatenation( text, " an unhandled filter" );
                
            fi;
            
        od;
        
        text := Concatenation( text, " we have" );
        
    fi;
    
    result := FunctionAsMathString( proposition, cat, input_filters );
    
    return Concatenation( "\\begin{lemma}\n", text, "\n", result, "\\end{lemma}\n" );
    
end );
