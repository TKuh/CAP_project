# SPDX-License-Identifier: GPL-2.0-or-later
# CompilerForCAP: Speed up computations in CAP categories
#
# Declarations
#
#! @Chapter Improving and extending the compiler

#! @Section Logic

#! @Description
#!   Adds the function <A>func</A> to the list of logic functions.
#!   For a list of pre-installed logic functions, which can be used as guiding examples, see `CompilerForCAP/gap/Logic.gi`.
#!   Technically, <A>func</A> should accept an (enhanced) syntax tree and some JIT arguments and return an (enhanced) syntax tree.
#!   Semantically, <A>func</A> should use some kind of "logic" to transform the tree.
#!   For example, <A>func</A> could look for calls of `CallFuncList` and replace them by calls to the actual function.
#!   Note: Often it is easier to use a logic template (see <Ref Func="CapJitAddLogicTemplate" />) than a logic function.
#! @Arguments func
DeclareGlobalFunction( "CapJitAddLogicFunction" );

#! @Section Compilation steps

#! @Description
#!   Applies all logic functions (see <Ref Func="CapJitAddLogicFunction" />) and logic templates
#!   (see <Ref Func="CapJitAppliedLogicTemplates" />) to <A>tree</A>.
#! @Returns a record
#! @Arguments tree, jit_args
DeclareGlobalFunction( "CapJitAppliedLogic" );

DeclareGlobalFunction( "CAP_JIT_INTERNAL_TELESCOPED_ITERATION" );
