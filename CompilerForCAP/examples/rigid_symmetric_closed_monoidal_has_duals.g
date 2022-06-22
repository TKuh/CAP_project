# We use the following definition of "rigid symmetric closed monoidal category":
#
# A symmetric closed monoidal category $\mathbf{C}$ satisfying
# * the natural morphism
#  $\mathrm{\underline{Hom}}(a, a') \otimes \mathrm{\underline{Hom}}(b, b') \rightarrow \mathrm{\underline{Hom}}(a \otimes b, a' \otimes b')$
#  is an isomorphism,
# * the natural morphism
#  $a \rightarrow \mathrm{\underline{Hom}}(\mathrm{\underline{Hom}}(a, 1), 1)$
#  is an isomorphism.
#
# We show that $\underline{Hom}(-, 1)$ with suitable evaluation and coevaluation gives duals.

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
        "TensorProductOnMorphisms",
        "LeftUnitor",
        "LeftUnitorInverse",
        "RightUnitor",
        "RightUnitorInverse",
        "AssociatorLeftToRight",
        "AssociatorRightToLeft",
        # symmetric
        "Braiding",
        "BraidingInverse",
        # invert morphisms
        "InverseForMorphisms",
        # closed structure
        "InternalHomOnObjects",
        "InternalHomOnMorphisms",
        #"TensorProductToInternalHomAdjunctionMap",
        #"InternalHomToTensorProductAdjunctionMap",
        "EvaluationMorphism",
        "CoevaluationMorphism",
        #"TensorProductInternalHomCompatibilityMorphismInverse",
    ],
    properties := [
        "IsRigidSymmetricClosedMonoidalCategory"
    ],
) );

CanCompute( dummy, "DualOnObjects" );
CanCompute( dummy, "DualOnMorphisms" );
CanCompute( dummy, "EvaluationForDual" );
CanCompute( dummy, "CoevaluationForDual" );

CapJitEnableProofAssistantMode( );
StopCompilationAtPrimitivelyInstalledOperationsOfCategory( dummy );

# first pentagon
func := function ( cat, X )
    
    return IsCongruentForMorphisms( cat,
        IdentityMorphism( cat, X ),
        PreComposeList( cat, [
            LeftUnitorInverse( cat, X ),
            TensorProductOnMorphisms( cat, CoevaluationForDual( cat, X ), IdentityMorphism( cat, X ) ),
            AssociatorLeftToRight( cat, X, DualOnObjects( cat, X ), X ),
            TensorProductOnMorphisms( cat, IdentityMorphism( cat, X ), EvaluationForDual( cat, X ) ),
            RightUnitor( cat, X )
        ] )
    );
    
end;

## functoriality of the tensor product
#CapJitAddLogicTemplate(
#    rec(
#        variable_names := [ "cat", "mor1", "mor2", "mor3", "mor4" ],
#        src_template := "PreCompose( cat, TensorProductOnMorphisms( cat, mor1, mor2 ), TensorProductOnMorphisms( cat, mor3, mor4 ) )",
#        dst_template := "TensorProductOnMorphisms( cat, PreCompose( cat, mor1, mor3 ), PreCompose( cat, mor2, mor4 ) )",
#    )
#);
#
## identity morphism is the neutral element w.r.t composition
#CapJitAddLogicTemplate(
#    rec(
#        variable_names := [ "cat", "object", "morphism" ],
#        src_template := "PreCompose( cat, IdentityMorphism( cat, object ), morphism )",
#        dst_template := "morphism",
#    )
#);
#CapJitAddLogicTemplate(
#    rec(
#        variable_names := [ "cat", "object", "morphism" ],
#        src_template := "PreCompose( cat, morphism, IdentityMorphism( cat, object ) )",
#        dst_template := "morphism",
#    )
#);

compiled_func := CapJitCompiledFunction( func, dummy, [ "category", "object" ], "bool" );

Display( compiled_func );



## Source( id_a ) = a
#CapJitAddLogicTemplate(
#    rec(
#        variable_names := [ "cat", "object" ],
#        src_template := "Source( IdentityMorphism( cat, object ) )",
#        dst_template := "object",
#    )
#);
#
## id(A) ⊗ id(B) = id(A ⊗ B)
#CapJitAddLogicTemplate(
#    rec(
#        variable_names := [ "cat", "object1", "object2" ],
#        src_template := "TensorProductOnMorphisms( cat, IdentityMorphism( cat, object1 ), IdentityMorphism( cat, object2 ) )",
#        dst_template := "IdentityMorphism( cat, TensorProductOnObjects( cat, object1, object2 ) )",
#    )
#);
#
## identity morphism is the neutral element w.r.t composition
#CapJitAddLogicTemplate(
#    rec(
#        variable_names := [ "cat", "object", "morphism" ],
#        src_template := "PreCompose( cat, IdentityMorphism( cat, object ), morphism )",
#        dst_template := "morphism",
#    )
#);
#CapJitAddLogicTemplate(
#    rec(
#        variable_names := [ "cat", "object", "morphism" ],
#        src_template := "PreCompose( cat, morphism, IdentityMorphism( cat, object ) )",
#        dst_template := "morphism",
#    )
#);
#
## functoriality of the tensor product
#CapJitAddLogicTemplate(
#    rec(
#        variable_names := [ "cat", "object", "mor1", "mor2" ],
#        src_template := "TensorProductOnMorphisms( cat, IdentityMorphism( cat, object ), PreCompose( cat, mor1, mor2 ) )",
#        dst_template := "PreCompose( cat, TensorProductOnMorphisms( cat, IdentityMorphism( cat, object ), mor1 ), TensorProductOnMorphisms( cat, IdentityMorphism( cat, object ), mor2 ) )",
#    )
#);
#
## functoriality of the internal hom
#CapJitAddLogicTemplate(
#    rec(
#        variable_names := [ "cat", "object", "mor1", "mor2" ],
#        src_template := "InternalHomOnMorphisms( cat, IdentityMorphism( cat, object ), PreCompose( cat, mor1, mor2 ) )",
#        dst_template := "PreCompose( cat, InternalHomOnMorphisms( cat, IdentityMorphism( cat, object ), mor1 ), InternalHomOnMorphisms( cat, IdentityMorphism( cat, object ), mor2 ) )",
#    )
#);
#
## make PreCompose left-balanced
#CapJitAddLogicTemplate(
#    rec(
#        variable_names := [ "cat", "α", "β", "γ" ],
#        src_template := "PreCompose( cat, α, PreCompose( cat, β, γ ) )",
#        dst_template := "PreCompose( cat, PreCompose( cat, α, β ), γ )",
#    )
#);
#
## DualOnMorphisms derivation
#func := function ( cat, alpha )
#  local a, b, av, bv;
#    
#    a := Source( alpha );
#    b := Range( alpha );
#    av := DualOnObjects( cat, a );
#    bv := DualOnObjects( cat, b );
#    
#    return IsCongruentForMorphisms( cat,
#        PreComposeList( cat, [
#            IsomorphismFromDualObjectToInternalHomIntoTensorUnit( cat, b ),
#            InternalHomOnMorphisms( cat,
#                alpha,
#                IdentityMorphism( cat, TensorUnit( cat ) )
#            ),
#            IsomorphismFromInternalHomIntoTensorUnitToDualObject( cat, a )
#        ] ),
#        PreComposeList( cat, [
#            RightUnitorInverse( cat, bv ),
#            TensorProductOnMorphisms( cat, IdentityMorphism( cat, bv ), CoevaluationForDual( cat, a ) ),
#            TensorProductOnMorphisms( cat, IdentityMorphism( cat, bv ), TensorProductOnMorphisms( cat, alpha, IdentityMorphism( cat, av ) ) ),
#            AssociatorRightToLeft( cat, bv, b, av ),
#            TensorProductOnMorphisms( cat, EvaluationForDual( cat, b ), IdentityMorphism( cat, av ) ),
#            LeftUnitor( cat, av )
#        ] )
#    );
#    
#end;
#
#Display( CapJitCompiledFunction( func, dummy, [ "category", "morphism" ], "bool" ) );
