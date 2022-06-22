# Assume that we have a symmetric monoidal category with duals, i.e. with
# * DualOnObjects
# * DualOnMorphisms
# * EvaluationForDual
# * CoevaluationForDual

LoadPackage( "MonoidalCategories" );

dummy := DummyCategory( rec(
    list_of_operations_to_install := [
        # category
        "IsEqualForObjects",
        "IsEqualForMorphisms",
        "PreCompose",
        "IdentityMorphism",
        # computable
        "IsCongruentForMorphisms",
        # monoidal
        "TensorUnit",
        "TensorProductOnObjects",
        "TensorProductOnMorphismsWithGivenTensorProducts",
        "LeftUnitor",
        "LeftUnitorInverse",
        "RightUnitor",
        "RightUnitorInverse",
        "AssociatorLeftToRight",
        "AssociatorRightToLeft",
        # symmetric
        "Braiding",
        "BraidingInverse",
        # with duals
        "DualOnObjects",
        "DualOnMorphisms",
        "EvaluationForDual",
        "CoevaluationForDual",
    ],
    properties := [
        "IsRigidSymmetricClosedMonoidalCategory",
    ],
) );

# all operations needed for defining a lambda calculus
Assert( 0, CanCompute( dummy, "TensorProductOnObjects" ) );
Assert( 0, CanCompute( dummy, "InternalHomOnObjects" ) );
Assert( 0, CanCompute( dummy, "TensorUnit" ) );
Assert( 0, CanCompute( dummy, "IdentityMorphism" ) );
Assert( 0, CanCompute( dummy, "TensorProductOnMorphisms" ) );
Assert( 0, CanCompute( dummy, "EvaluationMorphism" ) );
Assert( 0, CanCompute( dummy, "LeftUnitor" ) );
Assert( 0, CanCompute( dummy, "LambdaIntroduction" ) );
Assert( 0, CanCompute( dummy, "TensorProductToInternalHomAdjunctionMap" ) );

CapJitEnableProofAssistantMode( );
StopCompilationAtPrimitivelyInstalledOperationsOfCategory( dummy );

# TensorProductToInternalHomAdjunctionMap ⋅ InternalHomToTensorProductAdjunctionMap = id
func := function ( cat, a, b, c, f )
    
    CapJitAddLocalReplacement( Source( f ), TensorProductOnObjects( cat, a, b ) );
    CapJitAddLocalReplacement( Range( f ), c );
    
    # f: a ⊗ b → c
    
    return IsCongruentForMorphisms( cat,
        InternalHomToTensorProductAdjunctionMap( cat, b, c, TensorProductToInternalHomAdjunctionMap( cat, a, b, f ) ),
        f
    );
    
end;

# functoriality of the tensor product
#CapJitAddLogicTemplate(
#    rec(
#        variable_names := [ "cat", "mor1", "mor2", "mor3", "mor4" ],
#        src_template := "PreCompose( cat, TensorProductOnMorphisms( cat, mor1, mor2 ), TensorProductOnMorphisms( cat, mor3, mor4 ) )",
#        dst_template := "TensorProductOnMorphisms( cat, PreCompose( cat, mor1, mor3 ), PreCompose( cat, mor2, mor4 ) )",
#    )
#);

#CapJitAddLogicTemplate(
#    rec(
#        variable_names := [ "cat", "object1", "object2" ],
#        src_template := "TensorProductOnMorphisms( cat, IdentityMorphism( cat, object1 ), IdentityMorphism( cat, object2 ) )",
#        dst_template := "IdentityMorphism( cat, TensorProductOnObjects( cat, object1, object2 ) )",
#    )
#);
#
#CapJitAddLogicTemplate(
#    rec(
#        variable_names := [ "cat", "mor1", "mor2", "mor3" ],
#        src_template := "TensorProductOnMorphisms( cat, PreCompose( cat, mor1, mor2 ), mor3 )",
#        dst_template := "PreCompose( cat, TensorProductOnMorphisms( cat, mor1, mor3 ), TensorProductOnMorphisms( cat, mor2, IdentityMorphism( cat, Range( mor3 ) ) ) )",
#    )
#);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "source", "object1", "object2", "range" ],
        src_template := "TensorProductOnMorphismsWithGivenTensorProducts( cat, source, IdentityMorphism( cat, object1 ), IdentityMorphism( cat, object2 ), range )",
        dst_template := "IdentityMorphism( cat, TensorProductOnObjects( cat, object1, object2 ) )",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "source", "mor1", "mor2", "mor3", "range" ],
        src_template := "TensorProductOnMorphismsWithGivenTensorProducts( cat, source, PreCompose( cat, mor1, mor2 ), mor3, range )",
        dst_template := "PreCompose( cat, TensorProductOnMorphismsWithGivenTensorProducts( cat, source, mor1, mor3, TensorProductOnObjects( cat, Range( mor1 ), Range( mor3 ) ) ), TensorProductOnMorphismsWithGivenTensorProducts( cat, TensorProductOnObjects( cat, Source( mor2 ), Source( mor3 ) ), mor2, IdentityMorphism( cat, Range( mor3 ) ), range ) )",
    )
);

# Source( id_a ) = a
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "object" ],
        src_template := "Source( IdentityMorphism( cat, object ) )",
        dst_template := "object",
    )
);

# Range( id_a ) = a
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "object" ],
        src_template := "Range( IdentityMorphism( cat, object ) )",
        dst_template := "object",
    )
);

# identity morphism is the neutral element w.r.t composition
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "object", "morphism" ],
        src_template := "PreCompose( cat, IdentityMorphism( cat, object ), morphism )",
        dst_template := "morphism",
    )
);
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "object", "morphism" ],
        src_template := "PreCompose( cat, morphism, IdentityMorphism( cat, object ) )",
        dst_template := "morphism",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "object" ],
        src_template := "Source( EvaluationForDual( cat, object ) )",
        dst_template := "TensorProductOnObjects( cat, DualOnObjects( cat, object ), object )",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "object" ],
        src_template := "Range( EvaluationForDual( cat, object ) )",
        dst_template := "TensorUnit( cat )",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "object" ],
        src_template := "Source( CoevaluationForDual( cat, object ) )",
        dst_template := "TensorUnit( cat )",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "object" ],
        src_template := "Range( CoevaluationForDual( cat, object ) )",
        dst_template := "TensorProductOnObjects( cat, object, DualOnObjects( cat, object ) )",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "object1", "object2" ],
        src_template := "Source( Braiding( cat, object1, object2 ) )",
        dst_template := "TensorProductOnObjects( cat, object1, object2 )",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "object1", "object2" ],
        src_template := "Range( Braiding( cat, object1, object2 ) )",
        dst_template := "TensorProductOnObjects( cat, object2, object1 )",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "morphism" ],
        src_template := "Source( DualOnMorphisms( cat, morphism ) )",
        dst_template := "DualOnObjects( cat, Range( morphism ) )",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "morphism" ],
        src_template := "Range( DualOnMorphisms( cat, morphism ) )",
        dst_template := "DualOnObjects( cat, Source( morphism ) )",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "source", "morphism1", "morphism2", "range" ],
        src_template := "Source( TensorProductOnMorphismsWithGivenTensorProducts( cat, source, morphism1, morphism2, range ) )",
        dst_template := "source",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "source", "morphism1", "morphism2", "range" ],
        src_template := "Range( TensorProductOnMorphismsWithGivenTensorProducts( cat, source, morphism1, morphism2, range ) )",
        dst_template := "range",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "object1", "object2", "object3" ],
        src_template := "Source( AssociatorLeftToRight( cat, object1, object2, object3 ) )",
        dst_template := "TensorProductOnObjects( cat, TensorProductOnObjects( cat, object1, object2 ), object3 )",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "object1", "object2", "object3" ],
        src_template := "Range( AssociatorLeftToRight( cat, object1, object2, object3 ) )",
        dst_template := "TensorProductOnObjects( cat, object1, TensorProductOnObjects( cat, object2, object3 ) )",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "mor1", "mor2" ],
        src_template := "Source( PreCompose( cat, mor1, mor2 ) )",
        dst_template := "Source( mor1 )",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "mor1", "mor2" ],
        src_template := "Range( PreCompose( cat, mor1, mor2 ) )",
        dst_template := "Range( mor2 )",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "obj" ],
        src_template := "Source( LeftUnitorInverse( cat, obj ) )",
        dst_template := "obj",
    )
);

CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "obj" ],
        src_template := "Range( LeftUnitorInverse( cat, obj ) )",
        dst_template := "TensorProductOnObjects( cat, TensorUnit( cat ), obj )",
    )
);

compiled_func := CapJitCompiledFunction( func, dummy, [ "category", "object", "object", "object", "morphism" ], "bool" );

Display( compiled_func );

prepare_for_tensoring := function ( string, tree )
    
    return string;
    
    #if CapJitIsCallToGlobalFunction( tree, gvar -> gvar in [ "TensorProductOnMorphisms", "LeftUnitorInverse", "Braiding", "AssociatorLeftToRight", "AssociatorRightToLeft", "CoevaluationForDual" ] ) then
    if CapJitIsCallToGlobalFunction( tree, gvar -> gvar in [ "TensorProductOnMorphisms" ] ) then
        
        return Concatenation( "(", string, ")" );
        
    else
        
        return string;
        
    fi;
    
end;

ShowTikzCd := function( str )
    local scale, dir, filename, string, x, file;
       
    scale := ValueOption( "ScaleBox" );
    
    if scale = fail then
      
      scale := "1";
      
    elif not IsString( scale ) then
      
      scale := String( scale );
      
    fi;
    
    dir := DirectoryTemporary();
    
    filename := Filename( dir, "main.tex" );
    
    string := Concatenation(
"""
\documentclass{standalone}
\usepackage[mathletters]{ucs}
\usepackage[utf8]{inputenc}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage{amsmath}
\usepackage[dvipsnames]{xcolor}
\usepackage{tikz-cd}
\usepackage{adjustbox}
\DeclareMathOperator{\id}{id}
\begin{document}
\begin{tikzcd}""",
    str,
"""\end{tikzcd}
\end{document}
"""
    );
    
    file := OutputTextFile( filename, true );
    
    SetPrintFormattingStatus( file, false );
    
    PrintTo( file, string );
    
    str := "";
    
    x := Process(
            dir,
            Filename( DirectoriesSystemPrograms(), "pdflatex" ),
            InputTextUser( ),
            OutputTextString( str, true ),
            [ "-halt-on-error", "main.tex" ]
          );
          
    if x <> 0 then
      
      Error( "Something went wrong!, please check the main.tex file at ", filename );
      
    elif Filename( DirectoriesSystemPrograms(), "xdg-open" ) <> fail then
      
      Exec( Concatenation( "xdg-open ", Filename( dir, "main.pdf" ), " &" ) );
      
    elif Filename( DirectoriesSystemPrograms(), "open" ) <> fail then
      
      Exec( Concatenation( "open ", Filename( dir, "main.pdf" ), " &" ) );
      
    else
      
      Print( Filename( dir, "main.pdf" ) );
      
    fi;
    
    return;
    
end;

DisplayFunctionAsMath := function ( func, input_filters )
  local func_tree, return_value, result_func, left, right, mor;
    
    if not IsList( input_filters ) or Length( input_filters ) <> NumberArgumentsFunction( func ) then
        
        Error( "<input_filters> must be a list of length `NumberArgumentsFunction( <func> )`" );
        
    fi;
    
    func_tree := ENHANCED_SYNTAX_TREE( func );
    
    if Length( func_tree.bindings.names ) > 1 then
        
        Error( "only functions without proper bindings can be displayed as math" );
        
    fi;
    
    return_value := func_tree.bindings.BINDING_RETURN_VALUE;
    
    if not CapJitIsCallToGlobalFunction( return_value, "IsCongruentForMorphisms" ) then
        
        Error( "only functions returning the result of a call to IsCongruentForMorphisms can be displayed as math" );
        
    fi;
    
    result_func := function ( tree, result, keys, additional_arguments )
      local pos, type, first, first_list, second, second_list;
        
        if tree.type = "SYNTAX_TREE_LIST" then
            
            return result;
            
        elif tree.type = "EXPR_REF_GVAR" then
            
            return rec(
                type := "var",
                string := tree.gvar,
            );
            
        elif tree.type = "EXPR_REF_FVAR" then
            
            # we currently do not support nested functions (in particular, variable names are unique)
            Assert( 0, tree.func_id = func_tree.id );
            
            pos := Position( func_tree.nams, tree.name );
            
            Assert( 0, pos <> fail );
            
            type := input_filters[pos];
            
            if type = "category" then
                
                return rec(
                    type := "category",
                    string := tree.name,
                );
                
            elif type = "object" then
                
                return rec(
                    type := "object",
                    string := tree.name,
                );
                
            elif type = "morphism" then
                
                return rec(
                    type := "morphism",
                    source := Concatenation( "s(", tree.name, ")" ),
                    range := Concatenation( "t(", tree.name, ")" ),
                    string := tree.name,
                );
                
            else
                
                Error( "unkown type ", type );
                
            fi;
            
        elif CapJitIsCallToGlobalFunction( tree, ReturnTrue ) then
            
            if tree.funcref.gvar = "PreCompose" then
                
                first := result.args.2;
                
                if first.type = "morphism" then
                    
                    first_list := [ first ];
                    
                elif first.type = "PreComposeList" then
                    
                    first_list := first.list;
                    
                else
                    
                    Error( "unknown type ", first.type, " in PreCompose" );
                    
                fi;
                
                second := result.args.3;
                
                if second.type = "morphism" then
                    
                    second_list := [ second ];
                    
                elif second.type = "PreComposeList" then
                    
                    second_list := second.list;
                    
                else
                    
                    Error( "unknown type ", second.type, " in PreCompose" );
                    
                fi;
                
                return rec(
                    type := "PreComposeList",
                    list := Concatenation( first_list, second_list ),
                );
                
            fi;
            
            if tree.funcref.gvar = "TensorProductOnMorphismsWithGivenTensorProducts" then
                
                #if result.args.2.type = "morphism" and result.args.3.type = "morphism" then
                if result.args.3.type = "morphism" and result.args.4.type = "morphism" then
                    
                    return rec(
                        type := "morphism",
                        #source := Concatenation( prepare_for_tensoring( result.args.2.source, tree.args.2 ), " ⊗ ", prepare_for_tensoring( result.args.3.source, tree.args.3 ) ),
                        #range := Concatenation( prepare_for_tensoring( result.args.2.range, tree.args.2 ), " ⊗ ", prepare_for_tensoring( result.args.3.range, tree.args.3 ) ),
                        #string := Concatenation( prepare_for_tensoring( result.args.2.string, tree.args.2 ), " ⊗ ", prepare_for_tensoring( result.args.3.string, tree.args.3 ) ),
                        source := result.args.2.string,
                        range := result.args.5.string,
                        string := Concatenation( prepare_for_tensoring( result.args.3.string, tree.args.3 ), " ⊗ ", prepare_for_tensoring( result.args.4.string, tree.args.4 ) ),
                    );
                    
                #elif result.args.2.type = "PreComposeList" and result.args.3.type = "morphism" then
                #    
                #    return rec(
                #        type := "PreComposeList",
                #        list := List( result.args.2.list, l -> rec(
                #            type := "morphism",
                #            source := Concatenation( l.source, " ⊗ TODO: ", result.args.3.source ),
                #            range := Concatenation( l.range, " ⊗ TODO: ", result.args.3.range ),
                #            string := Concatenation( l.string, " ⊗ TODO: ", result.args.3.string ),
                #        ) ),
                #    );
                #    
                else
                    
                    Error( "case not handled yet" );
                    
                fi;
                
            fi;
            
            if ForAny( [ 1 .. tree.args.length ], i -> not result.args.(i).type in [ "category", "object", "morphism" ] ) then
                
                Error( tree.funcref.gvar, " can only handle categories, objects and morphisms" );
                
            fi;
            
            if tree.funcref.gvar = "IdentityMorphism" then
                
                return rec(
                    type := "morphism",
                    source := result.args.2.string,
                    range := result.args.2.string,
                    #string := Concatenation( "id(", result.args.2.string, ")" ),
                    string := "id",
                );
                
            elif tree.funcref.gvar = "TensorUnit" then
                
                return rec(
                    type := "object",
                    string := "1",
                );
                
            elif tree.funcref.gvar = "TensorProductOnObjects" then
                
                return rec(
                    type := "object",
                    string := Concatenation( result.args.2.string, " ⊗ ", result.args.3.string ),
                );
                
            elif tree.funcref.gvar = "LeftUnitor" then
                
                return rec(
                    type := "morphism",
                    source := Concatenation( "1 ⊗ ", result.args.2.string ),
                    range := result.args.2.string,
                    string := "λ",
                );
                
            elif tree.funcref.gvar = "LeftUnitorInverse" then
                
                return rec(
                    type := "morphism",
                    source := result.args.2.string,
                    range := Concatenation( "1 ⊗ ", result.args.2.string ),
                    string := "λ⁻¹",
                );
                
            elif tree.funcref.gvar = "RightUnitor" then
                
                return rec(
                    type := "morphism",
                    source := Concatenation( result.args.2.string, " ⊗ 1" ),
                    range := result.args.2.string,
                    string := "ρ",
                );
                
            elif tree.funcref.gvar = "RightUnitorInverse" then
                
                return rec(
                    type := "morphism",
                    source := result.args.2.string,
                    range := Concatenation( result.args.2.string, " ⊗ 1" ),
                    string := "ρ⁻¹",
                );
                
            elif tree.funcref.gvar = "AssociatorLeftToRight" then
                
                return rec(
                    type := "morphism",
                    #source := Concatenation( "(", result.args.2.string, " ⊗ ", result.args.3.string, ") ⊗ ", result.args.4.string ),
                    #range := Concatenation( result.args.2.string, " ⊗ (", result.args.3.string, " ⊗ ", result.args.4.string, ")" ),
                    source := Concatenation( "", result.args.2.string, " ⊗ ", result.args.3.string, " ⊗ ", result.args.4.string ),
                    range := Concatenation( result.args.2.string, " ⊗ ", result.args.3.string, " ⊗ ", result.args.4.string, "" ),
                    string := "α",
                );
                
            elif tree.funcref.gvar = "AssociatorRightToLeft" then
                
                return rec(
                    type := "morphism",
                    #source := Concatenation( result.args.2.string, " ⊗ (", result.args.3.string, " ⊗ ", result.args.4.string, ")" ),
                    #range := Concatenation( "(", result.args.2.string, " ⊗ ", result.args.3.string, ") ⊗ ", result.args.4.string ),
                    source := Concatenation( result.args.2.string, " ⊗ ", result.args.3.string, " ⊗ ", result.args.4.string, "" ),
                    range := Concatenation( "", result.args.2.string, " ⊗ ", result.args.3.string, " ⊗ ", result.args.4.string ),
                    string := "α⁻¹",
                );
                
            elif tree.funcref.gvar = "Braiding" then
                
                return rec(
                    type := "morphism",
                    source := Concatenation( result.args.2.string, " ⊗ ", result.args.3.string ),
                    range := Concatenation( result.args.3.string, " ⊗ ", result.args.2.string ),
                    string := "γ",
                );
                
            elif tree.funcref.gvar = "BraidingInverse" then
                
                return rec(
                    type := "morphism",
                    source := Concatenation( result.args.3.string, " ⊗ ", result.args.2.string ),
                    range := Concatenation( result.args.2.string, " ⊗ ", result.args.3.string ),
                    string := "γ⁻¹",
                );
                
            elif tree.funcref.gvar = "Source" then
                
                return rec(
                    type := "object",
                    string := Concatenation( "s(", result.args.1.string, ")" ),
                );
                
            elif tree.funcref.gvar = "Range" then
                
                return rec(
                    type := "object",
                    string := Concatenation( "t(", result.args.1.string, ")" ),
                );
                
            elif tree.funcref.gvar = "DualOnObjects" then
                
                return rec(
                    type := "object",
                    string := Concatenation( result.args.2.string, "ᵛ" ),
                );
                
            elif tree.funcref.gvar = "DualOnMorphisms" then
                
                return rec(
                    type := "morphism",
                    source := Concatenation( result.args.2.range, "ᵛ" ),
                    range := Concatenation( result.args.2.source, "ᵛ" ),
                    string := Concatenation( result.args.2.string, "ᵛ" ),
                );
                
            elif tree.funcref.gvar = "EvaluationForDual" then
                
                return rec(
                    type := "morphism",
                    source := Concatenation( result.args.2.string, "ᵛ ⊗ ", result.args.2.string ),
                    range := "1",
                    string := "ev",
                );
                
            elif tree.funcref.gvar = "CoevaluationForDual" then
                
                return rec(
                    type := "morphism",
                    source := "1",
                    range := Concatenation( result.args.2.string, " ⊗ ", result.args.2.string, "ᵛ" ),
                    string := "coev",
                );
                
            elif tree.funcref.gvar = "InternalHomOnObjects" then
                
                return rec(
                    type := "object",
                    string := Concatenation( "hom(", result.args.2.string, ",", result.args.3.string, ")" ),
                );
                
            #elif tree.funcref.gvar = "InternalHomOnMorphisms" then
            #    
            #    return rec(
            #        type := "morphism",
            #        source := "TODO",
            #        range := "TODO",
            #        string := Concatenation( "hom(", result.args.2.string, ",", result.args.3.string, ")" ),
            #    );
            #    
            fi;
            
            Error( tree.funcref.gvar, " is not yet handled" );
            
        fi;
        
        Error( tree.type, " is not yet handled" );
        
    end;
    
    left := CapJitIterateOverTree( func_tree.bindings.BINDING_RETURN_VALUE.args.2, ReturnFirst, result_func, ReturnTrue, true );
    right := CapJitIterateOverTree( func_tree.bindings.BINDING_RETURN_VALUE.args.3, ReturnFirst, result_func, ReturnTrue, true );
    
    latex_string := "";
    
    if left.type = "morphism" then
        
        Display( left.string );
        
    elif left.type = "PreComposeList" then
        
        max_length := Maximum( List( left.list, mor -> Maximum( WidthUTF8String( mor.source ), WidthUTF8String( mor.range ) ) ) );
        
        #if IsEven( max_length ) then
        #    max_length := max_length + 1;
        #fi;
        
        for i in [ 1 .. Length( left.list ) ] do
            
            mor := left.list[i];
            
            DisplayCentered( mor.source, max_length, "" );
            DisplayCentered( "│", max_length, TextAttr.7 );
            PrintCentered( "│", max_length, TextAttr.7 );
            Print( " ", TextAttr.bold, " ", mor.string, " ", TextAttr.reset, "\n" );
            DisplayCentered( "∨", max_length, TextAttr.7 );
            
            latex_string := Concatenation( latex_string, mor.source ); 
            latex_string := Concatenation( latex_string, "\\arrow[dd, \"" ); 
            latex_string := Concatenation( latex_string, mor.string ); 
            latex_string := Concatenation( latex_string, "\"] \\\\\n\\\\\n" ); 
            
            if i < Length( left.list ) and mor.range <> left.list[i + 1].source then
                
                DisplayCentered( mor.range, max_length, "" );
                DisplayCentered( "∥", max_length, TextAttr.7 );
                
                latex_string := Concatenation( latex_string, mor.range ); 
                latex_string := Concatenation( latex_string, "\\arrow[d, Rightarrow, no head] \\\\\n" ); 
                
            fi;
            
        od;
        
        DisplayCentered( Last( left.list ).range, max_length, "" );
        latex_string := Concatenation( latex_string, Last( left.list ).range ); 
        
    else
        
        Error( "unsupported type" );
        
    fi;
    
    Display( "∼" );
    Display( right.string );
    
    LoadPackage( "ToolsForHigher" );
    
    latex_string := ReplacedString( latex_string, "⁻¹", """^{-1}""" );
    latex_string := ReplacedString( latex_string, "ᵛ", """^{\vee}""" );
    latex_string := ReplacedString( latex_string, "⊗", """\otimes""" );
    latex_string := ReplacedString( latex_string, "id", """\id""" );
    latex_string := ReplacedString( latex_string, "coev", """\operatorname{coev}""" );
    latex_string := ReplacedString( latex_string, "ev", """\operatorname{ev}""" );
    latex_string := ReplacedString( latex_string, "α", """\alpha""" );
    latex_string := ReplacedString( latex_string, "β", """\beta""" );
    latex_string := ReplacedString( latex_string, "γ", """\gamma""" );
    latex_string := ReplacedString( latex_string, "λ", """\lambda""" );
    latex_string := ReplacedString( latex_string, "ρ", """\rho""" );
    
    ShowTikzCd( latex_string : scale := "0.5" );
    
end;

PrintCentered := function ( string, length, text_attr )
  local nr_spaces, nr_spaces_left;
    
    Assert( 0, WidthUTF8String( string ) <= length );
    
    nr_spaces := length - WidthUTF8String( string );
    
    nr_spaces_left := QuoInt( nr_spaces, 2 );
    
    Print( ListWithIdenticalEntries( nr_spaces_left, ' ' ), text_attr, string, TextAttr.reset );
    
end;

DisplayCentered := function ( string, length, text_attr )
    
    PrintCentered( string, length, text_attr );
    
    Print( "\n" );
    
end;

DisplayFunctionAsMath( compiled_func, [ "category", "object", "object", "object", "morphism" ] );

Error("stop");


# InternalHomToTensorProductAdjunctionMap ⋅ TensorProductToInternalHomAdjunctionMap = id
func := function ( cat, a, b, c, g )
    
    # g: a → hom(b,c) = b^v ⊗ c
    
    return IsCongruentForMorphisms( cat,
        TensorProductToInternalHomAdjunctionMap( cat, a, b, InternalHomToTensorProductAdjunctionMap( cat, b, c, g ) ),
        g
    );
    
end;

Display( CapJitCompiledFunction( func, dummy, [ "category", "object", "object", "object", "morphism" ], "bool" ) );

# naturality of the isomorphism
func := function ( cat, X, Xprime, Y, Yprime, Z, f, g, alpha )
    
    # https://en.wikipedia.org/wiki/Adjoint_functors#Definition_via_counit%E2%80%93unit_adjunction
    # F = - ⊗₀ Z, - ⊗₁ id_Z
    # G = hom(Z,-), hom(id_Z,-)
    # f: X  → X'
    # g: Y' → Y
    # alpha: Y ⊗₀ Z = F(Y) → X
    
    return IsCongruentForMorphisms( cat,
        # (Hom(Fg,f) ⋅ TensorProductToInternalHomAdjunctionMap)(alpha)
        # =
        # TensorProductToInternalHomAdjunctionMap((g ⊗₁ id_Z) ⋅ alpha ⋅ f)
        TensorProductToInternalHomAdjunctionMap( cat, Yprime, Z, PreComposeList( cat, [ TensorProductOnMorphisms( cat, g, IdentityMorphism( cat, Z ) ), alpha, f ] ) ),
        # (TensorProductToInternalHomAdjunctionMap ⋅ Hom(g,Gf))(alpha)
        # =
        # g ⋅ TensorProductToInternalHomAdjunctionMap(alpha) ⋅ hom(id_Z,f)
        PreComposeList( cat, [ g, TensorProductToInternalHomAdjunctionMap( cat, Y, Z, alpha ), InternalHomOnMorphisms( cat, IdentityMorphism( cat, Z ), f ) ] )
    );
    
end;

Display( CapJitCompiledFunction( func, dummy, [ "category", "object", "object", "object", "object", "object", "morphism", "morphism", "morphism" ], "bool" ) );

# check that hom(a,b) is a functor
func := function ( cat, a, b )
    
    return IsCongruentForMorphisms( cat,
        InternalHomOnMorphisms( cat, IdentityMorphism( cat, a ), IdentityMorphism( cat, b ) ),
        IdentityMorphism( cat, InternalHomOnObjects( cat, a, b ) )
    );
    
end;

# Source( id_a ) = a
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "object" ],
        src_template := "Source( IdentityMorphism( cat, object ) )",
        dst_template := "object",
    )
);

Display( CapJitCompiledFunction( func, dummy, [ "category", "object", "object" ], "bool" ) );

func := function ( cat, alpha, beta, alpha_prime, beta_prime )
    
    return IsCongruentForMorphisms( cat,
        InternalHomOnMorphisms( cat, PreCompose( cat, alpha_prime, alpha ), PreCompose( cat, beta, beta_prime ) ),
        PreCompose( cat,
            InternalHomOnMorphisms( cat, alpha, beta ),
            InternalHomOnMorphisms( cat, alpha_prime, beta_prime )
        )
    );
    
end;

# Source( α ⋅ β ) = Source( α )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "alpha", "beta" ],
        src_template := "Source( PreCompose( cat, alpha, beta ) )",
        dst_template := "Source( alpha )",
    )
);

# Range( α ⋅ β ) = Range( β )
CapJitAddLogicTemplate(
    rec(
        variable_names := [ "cat", "alpha", "beta" ],
        src_template := "Range( PreCompose( cat, alpha, beta ) )",
        dst_template := "Range( beta )",
    )
);

Display( CapJitCompiledFunction( func, dummy, [ "category", "morphism", "morphism", "morphism", "morphism" ], "bool" ) );
