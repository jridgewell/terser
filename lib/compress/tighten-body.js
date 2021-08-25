/***********************************************************************

  A JavaScript tokenizer / parser / beautifier / compressor.
  https://github.com/mishoo/UglifyJS2

  -------------------------------- (C) ---------------------------------

                           Author: Mihai Bazon
                         <mihai.bazon@gmail.com>
                       http://mihai.bazon.net/blog

  Distributed under the BSD license:

    Copyright 2012 (c) Mihai Bazon <mihai.bazon@gmail.com>

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

        * Redistributions of source code must retain the above
          copyright notice, this list of conditions and the following
          disclaimer.

        * Redistributions in binary form must reproduce the above
          copyright notice, this list of conditions and the following
          disclaimer in the documentation and/or other materials
          provided with the distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER “AS IS” AND ANY
    EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
    IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
    PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE
    LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY,
    OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
    PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
    PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
    THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
    TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
    THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
    SUCH DAMAGE.

 ***********************************************************************/

import {
    AST_Array,
    AST_Arrow,
    AST_Assign,
    AST_Await,
    AST_Binary,
    AST_Block,
    AST_BlockStatement,
    AST_Break,
    AST_Call,
    AST_Case,
    AST_Catch,
    AST_Chain,
    AST_Class,
    AST_Conditional,
    AST_Const,
    AST_Constant,
    AST_Continue,
    AST_Debugger,
    AST_Default,
    AST_Definitions,
    AST_Defun,
    AST_Destructuring,
    AST_Directive,
    AST_Dot,
    AST_DWLoop,
    AST_EmptyStatement,
    AST_Exit,
    AST_Expansion,
    AST_Export,
    AST_Finally,
    AST_For,
    AST_ForIn,
    AST_If,
    AST_Import,
    AST_IterationStatement,
    AST_Lambda,
    AST_Let,
    AST_LoopControl,
    AST_Node,
    AST_Number,
    AST_Object,
    AST_ObjectKeyVal,
    AST_PropAccess,
    AST_RegExp,
    AST_Return,
    AST_Scope,
    AST_Sequence,
    AST_SimpleStatement,
    AST_Sub,
    AST_Switch,
    AST_Symbol,
    AST_SymbolConst,
    AST_SymbolDeclaration,
    AST_SymbolDefun,
    AST_SymbolFunarg,
    AST_SymbolLambda,
    AST_SymbolLet,
    AST_SymbolRef,
    AST_SymbolVar,
    AST_This,
    AST_Try,
    AST_Unary,
    AST_UnaryPostfix,
    AST_UnaryPrefix,
    AST_Undefined,
    AST_Var,
    AST_VarDef,
    AST_With,
    AST_Yield,

    TreeTransformer,
    TreeWalker,
    walk,
    walk_abort,

    _NOINLINE
} from "../ast.js";
import {
    make_node,
    MAP,
    member,
    remove,
    has_annotation
} from "../utils/index.js";

import { pure_prop_access_globals } from "./native-objects.js";
import {
    lazy_op,
    unary_side_effects,
    is_modified,
    is_lhs,
    aborts
} from "./inference.js";
import { WRITE_ONLY, clear_flag } from "./compressor-flags.js";
import {
    make_sequence,
    merge_sequence,
    maintain_this_binding,
    is_func_expr,
    is_identifier_atom,
    is_ref_of,
    can_be_evicted_from_block,
    as_statement_array,
} from "./common.js";

function loop_body(x) {
    if (AST_IterationStatement.hasInstance(x)) {
        return AST_BlockStatement.hasInstance(x.body) ? x.body : x;
    }
    return x;
}

function is_lhs_read_only(lhs) {
    if (AST_This.hasInstance(lhs)) return true;
    if (AST_SymbolRef.hasInstance(lhs)) return AST_SymbolLambda.hasInstance(lhs.definition().orig[0]);
    if (AST_PropAccess.hasInstance(lhs)) {
        lhs = lhs.expression;
        if (AST_SymbolRef.hasInstance(lhs)) {
            if (lhs.is_immutable()) return false;
            lhs = lhs.fixed_value();
        }
        if (!lhs) return true;
        if (AST_RegExp.hasInstance(lhs)) return false;
        if (AST_Constant.hasInstance(lhs)) return true;
        return is_lhs_read_only(lhs);
    }
    return false;
}

// Remove code which we know is unreachable.
export function trim_unreachable_code(compressor, stat, target) {
    walk(stat, node => {
        if (AST_Var.hasInstance(node)) {
            node.remove_initializers();
            target.push(node);
            return true;
        }
        if (
            AST_Defun.hasInstance(node)
            && (node === stat || !compressor.has_directive("use strict"))
        ) {
            target.push(node === stat ? node : make_node(AST_Var, node, {
                definitions: [
                    make_node(AST_VarDef, node, {
                        name: make_node(AST_SymbolVar, node.name, node.name),
                        value: null
                    })
                ]
            }));
            return true;
        }
        if (AST_Export.hasInstance(node) || AST_Import.hasInstance(node)) {
            target.push(node);
            return true;
        }
        if (AST_Scope.hasInstance(node)) {
            return true;
        }
    });
}

// Tighten a bunch of statements together, and perform statement-level optimization.
export function tighten_body(statements, compressor) {
    var in_loop, in_try;
    var scope = compressor.find_parent(AST_Scope).get_defun_scope();
    find_loop_scope_try();
    var CHANGED, max_iter = 10;
    do {
        CHANGED = false;
        eliminate_spurious_blocks(statements);
        if (compressor.option("dead_code")) {
            eliminate_dead_code(statements, compressor);
        }
        if (compressor.option("if_return")) {
            handle_if_return(statements, compressor);
        }
        if (compressor.sequences_limit > 0) {
            sequencesize(statements, compressor);
            sequencesize_2(statements, compressor);
        }
        if (compressor.option("join_vars")) {
            join_consecutive_vars(statements);
        }
        if (compressor.option("collapse_vars")) {
            collapse(statements, compressor);
        }
    } while (CHANGED && max_iter-- > 0);

    function find_loop_scope_try() {
        var node = compressor.self(), level = 0;
        do {
            if (AST_Catch.hasInstance(node) || AST_Finally.hasInstance(node)) {
                level++;
            } else if (AST_IterationStatement.hasInstance(node)) {
                in_loop = true;
            } else if (AST_Scope.hasInstance(node)) {
                scope = node;
                break;
            } else if (AST_Try.hasInstance(node)) {
                in_try = true;
            }
        } while (node = compressor.parent(level++));
    }

    // Search from right to left for assignment-like expressions:
    // - `var a = x;`
    // - `a = x;`
    // - `++a`
    // For each candidate, scan from left to right for first usage, then try
    // to fold assignment into the site for compression.
    // Will not attempt to collapse assignments into or past code blocks
    // which are not sequentially executed, e.g. loops and conditionals.
    function collapse(statements, compressor) {
        if (scope.pinned())
            return statements;
        var args;
        var candidates = [];
        var stat_index = statements.length;
        var scanner = new TreeTransformer(function (node) {
            if (abort)
                return node;
            // Skip nodes before `candidate` as quickly as possible
            if (!hit) {
                if (node !== hit_stack[hit_index])
                    return node;
                hit_index++;
                if (hit_index < hit_stack.length)
                    return handle_custom_scan_order(node);
                hit = true;
                stop_after = find_stop(node, 0);
                if (stop_after === node)
                    abort = true;
                return node;
            }
            // Stop immediately if these node types are encountered
            var parent = scanner.parent();
            if (AST_Assign.hasInstance(node)
                    && (node.logical || node.operator != "=" && lhs.equivalent_to(node.left))
                || AST_Await.hasInstance(node)
                || AST_Call.hasInstance(node) && AST_PropAccess.hasInstance(lhs) && lhs.equivalent_to(node.expression)
                || AST_Debugger.hasInstance(node)
                || AST_Destructuring.hasInstance(node)
                || AST_Expansion.hasInstance(node)
                    && AST_Symbol.hasInstance(node.expression)
                    && (
                        AST_This.hasInstance(node.expression)
                        || node.expression.definition().references.length > 1
                    )
                || AST_IterationStatement.hasInstance(node) && !AST_For.hasInstance(node)
                || AST_LoopControl.hasInstance(node)
                || AST_Try.hasInstance(node)
                || AST_With.hasInstance(node)
                || AST_Yield.hasInstance(node)
                || AST_Export.hasInstance(node)
                || AST_Class.hasInstance(node)
                || AST_For.hasInstance(parent) && node !== parent.init
                || !replace_all
                    && (
                        AST_SymbolRef.hasInstance(node)
                        && !node.is_declared(compressor)
                        && !pure_prop_access_globals.has(node)
                    )
                || AST_SymbolRef.hasInstance(node)
                    && AST_Call.hasInstance(parent)
                    && has_annotation(parent, _NOINLINE)
            ) {
                abort = true;
                return node;
            }
            // Stop only if candidate is found within conditional branches
            if (!stop_if_hit && (!lhs_local || !replace_all)
                && (AST_Binary.hasInstance(parent) && lazy_op.has(parent.operator) && parent.left !== node
                    || AST_Conditional.hasInstance(parent) && parent.condition !== node
                    || AST_If.hasInstance(parent) && parent.condition !== node)) {
                stop_if_hit = parent;
            }
            // Replace variable with assignment when found
            if (can_replace
                && !AST_SymbolDeclaration.hasInstance(node)
                && lhs.equivalent_to(node)) {
                if (stop_if_hit) {
                    abort = true;
                    return node;
                }
                if (is_lhs(node, parent)) {
                    if (value_def)
                        replaced++;
                    return node;
                } else {
                    replaced++;
                    if (value_def && AST_VarDef.hasInstance(candidate))
                        return node;
                }
                CHANGED = abort = true;
                if (AST_UnaryPostfix.hasInstance(candidate)) {
                    return make_node(AST_UnaryPrefix, candidate, candidate);
                }
                if (AST_VarDef.hasInstance(candidate)) {
                    var def = candidate.name.definition();
                    var value = candidate.value;
                    if (def.references.length - def.replaced == 1 && !compressor.exposed(def)) {
                        def.replaced++;
                        if (funarg && is_identifier_atom(value)) {
                            return value.transform(compressor);
                        } else {
                            return maintain_this_binding(parent, node, value);
                        }
                    }
                    return make_node(AST_Assign, candidate, {
                        operator: "=",
                        logical: false,
                        left: make_node(AST_SymbolRef, candidate.name, candidate.name),
                        right: value
                    });
                }
                clear_flag(candidate, WRITE_ONLY);
                return candidate;
            }
            // These node types have child nodes that execute sequentially,
            // but are otherwise not safe to scan into or beyond them.
            var sym;
            if (AST_Call.hasInstance(node)
                || AST_Exit.hasInstance(node)
                && (side_effects || AST_PropAccess.hasInstance(lhs) || may_modify(lhs))
                || AST_PropAccess.hasInstance(node)
                && (side_effects || node.expression.may_throw_on_access(compressor))
                || AST_SymbolRef.hasInstance(node)
                && (lvalues.get(node.name) || side_effects && may_modify(node))
                || AST_VarDef.hasInstance(node) && node.value
                && (lvalues.has(node.name.name) || side_effects && may_modify(node.name))
                || (sym = is_lhs(node.left, node))
                && (AST_PropAccess.hasInstance(sym) || lvalues.has(sym.name))
                || may_throw
                && (in_try ? node.has_side_effects(compressor) : side_effects_external(node))) {
                stop_after = node;
                if (AST_Scope.hasInstance(node))
                    abort = true;
            }
            return handle_custom_scan_order(node);
        }, function (node) {
            if (abort)
                return;
            if (stop_after === node)
                abort = true;
            if (stop_if_hit === node)
                stop_if_hit = null;
        });

        var multi_replacer = new TreeTransformer(function (node) {
            if (abort)
                return node;
            // Skip nodes before `candidate` as quickly as possible
            if (!hit) {
                if (node !== hit_stack[hit_index])
                    return node;
                hit_index++;
                if (hit_index < hit_stack.length)
                    return;
                hit = true;
                return node;
            }
            // Replace variable when found
            if (AST_SymbolRef.hasInstance(node)
                && node.name == def.name) {
                if (!--replaced)
                    abort = true;
                if (is_lhs(node, multi_replacer.parent()))
                    return node;
                def.replaced++;
                value_def.replaced--;
                return candidate.value;
            }
            // Skip (non-executed) functions and (leading) default case in switch statements
            if (AST_Default.hasInstance(node) || AST_Scope.hasInstance(node))
                return node;
        });

        while (--stat_index >= 0) {
            // Treat parameters as collapsible in IIFE, i.e.
            //   function(a, b){ ... }(x());
            // would be translated into equivalent assignments:
            //   var a = x(), b = undefined;
            if (stat_index == 0 && compressor.option("unused"))
                extract_args();
            // Find collapsible assignments
            var hit_stack = [];
            extract_candidates(statements[stat_index]);
            while (candidates.length > 0) {
                hit_stack = candidates.pop();
                var hit_index = 0;
                var candidate = hit_stack[hit_stack.length - 1];
                var value_def = null;
                var stop_after = null;
                var stop_if_hit = null;
                var lhs = get_lhs(candidate);
                if (!lhs || is_lhs_read_only(lhs) || lhs.has_side_effects(compressor))
                    continue;
                // Locate symbols which may execute code outside of scanning range
                var lvalues = get_lvalues(candidate);
                var lhs_local = is_lhs_local(lhs);
                if (AST_SymbolRef.hasInstance(lhs))
                    lvalues.set(lhs.name, false);
                var side_effects = value_has_side_effects(candidate);
                var replace_all = replace_all_symbols();
                var may_throw = candidate.may_throw(compressor);
                var funarg = AST_SymbolFunarg.hasInstance(candidate.name);
                var hit = funarg;
                var abort = false, replaced = 0, can_replace = !args || !hit;
                if (!can_replace) {
                    for (var j = compressor.self().argnames.lastIndexOf(candidate.name) + 1; !abort && j < args.length; j++) {
                        args[j].transform(scanner);
                    }
                    can_replace = true;
                }
                for (var i = stat_index; !abort && i < statements.length; i++) {
                    statements[i].transform(scanner);
                }
                if (value_def) {
                    var def = candidate.name.definition();
                    if (abort && def.references.length - def.replaced > replaced)
                        replaced = false;
                    else {
                        abort = false;
                        hit_index = 0;
                        hit = funarg;
                        for (var i = stat_index; !abort && i < statements.length; i++) {
                            statements[i].transform(multi_replacer);
                        }
                        value_def.single_use = false;
                    }
                }
                if (replaced && !remove_candidate(candidate))
                    statements.splice(stat_index, 1);
            }
        }

        function handle_custom_scan_order(node) {
            // Skip (non-executed) functions
            if (AST_Scope.hasInstance(node))
                return node;

            // Scan case expressions first in a switch statement
            if (AST_Switch.hasInstance(node)) {
                node.expression = node.expression.transform(scanner);
                for (var i = 0, len = node.body.length; !abort && i < len; i++) {
                    var branch = node.body[i];
                    if (AST_Case.hasInstance(branch)) {
                        if (!hit) {
                            if (branch !== hit_stack[hit_index])
                                continue;
                            hit_index++;
                        }
                        branch.expression = branch.expression.transform(scanner);
                        if (!replace_all)
                            break;
                    }
                }
                abort = true;
                return node;
            }
        }

        function redefined_within_scope(def, scope) {
            if (def.global)
                return false;
            let cur_scope = def.scope;
            while (cur_scope && cur_scope !== scope) {
                if (cur_scope.variables.has(def.name))
                    return true;
                cur_scope = cur_scope.parent_scope;
            }
            return false;
        }

        function has_overlapping_symbol(fn, arg, fn_strict) {
            var found = false, scan_this = !AST_Arrow.hasInstance(fn);
            arg.walk(new TreeWalker(function (node, descend) {
                if (found)
                    return true;
                if (AST_SymbolRef.hasInstance(node) && (fn.variables.has(node.name) || redefined_within_scope(node.definition(), fn))) {
                    var s = node.definition().scope;
                    if (s !== scope)
                        while (s = s.parent_scope) {
                            if (s === scope)
                                return true;
                        }
                    return found = true;
                }
                if ((fn_strict || scan_this) && AST_This.hasInstance(node)) {
                    return found = true;
                }
                if (AST_Scope.hasInstance(node) && !AST_Arrow.hasInstance(node)) {
                    var prev = scan_this;
                    scan_this = false;
                    descend();
                    scan_this = prev;
                    return true;
                }
            }));
            return found;
        }

        function extract_args() {
            var iife, fn = compressor.self();
            if (is_func_expr(fn)
                && !fn.name
                && !fn.uses_arguments
                && !fn.pinned()
                && AST_Call.hasInstance(iife = compressor.parent())
                && iife.expression === fn
                && iife.args.every((arg) => !AST_Expansion.hasInstance(arg))) {
                var fn_strict = compressor.has_directive("use strict");
                if (fn_strict && !member(fn_strict, fn.body))
                    fn_strict = false;
                var len = fn.argnames.length;
                args = iife.args.slice(len);
                var names = new Set();
                for (var i = len; --i >= 0;) {
                    var sym = fn.argnames[i];
                    var arg = iife.args[i];
                    // The following two line fix is a duplicate of the fix at
                    // https://github.com/terser/terser/commit/011d3eb08cefe6922c7d1bdfa113fc4aeaca1b75
                    // This might mean that these two pieces of code (one here in collapse_vars and another in reduce_vars
                    // Might be doing the exact same thing.
                    const def = sym.definition && sym.definition();
                    const is_reassigned = def && def.orig.length > 1;
                    if (is_reassigned)
                        continue;
                    args.unshift(make_node(AST_VarDef, sym, {
                        name: sym,
                        value: arg
                    }));
                    if (names.has(sym.name))
                        continue;
                    names.add(sym.name);
                    if (AST_Expansion.hasInstance(sym)) {
                        var elements = iife.args.slice(i);
                        if (elements.every((arg) => !has_overlapping_symbol(fn, arg, fn_strict)
                        )) {
                            candidates.unshift([make_node(AST_VarDef, sym, {
                                name: sym.expression,
                                value: make_node(AST_Array, iife, {
                                    elements: elements
                                })
                            })]);
                        }
                    } else {
                        if (!arg) {
                            arg = make_node(AST_Undefined, sym).transform(compressor);
                        } else if (AST_Lambda.hasInstance(arg) && arg.pinned()
                            || has_overlapping_symbol(fn, arg, fn_strict)) {
                            arg = null;
                        }
                        if (arg)
                            candidates.unshift([make_node(AST_VarDef, sym, {
                                name: sym,
                                value: arg
                            })]);
                    }
                }
            }
        }

        function extract_candidates(expr) {
            hit_stack.push(expr);
            if (AST_Assign.hasInstance(expr)) {
                if (!expr.left.has_side_effects(compressor)
                    && !AST_Chain.hasInstance(expr.right)) {
                    candidates.push(hit_stack.slice());
                }
                extract_candidates(expr.right);
            } else if (AST_Binary.hasInstance(expr)) {
                extract_candidates(expr.left);
                extract_candidates(expr.right);
            } else if (AST_Call.hasInstance(expr) && !has_annotation(expr, _NOINLINE)) {
                extract_candidates(expr.expression);
                expr.args.forEach(extract_candidates);
            } else if (AST_Case.hasInstance(expr)) {
                extract_candidates(expr.expression);
            } else if (AST_Conditional.hasInstance(expr)) {
                extract_candidates(expr.condition);
                extract_candidates(expr.consequent);
                extract_candidates(expr.alternative);
            } else if (AST_Definitions.hasInstance(expr)) {
                var len = expr.definitions.length;
                // limit number of trailing variable definitions for consideration
                var i = len - 200;
                if (i < 0)
                    i = 0;
                for (; i < len; i++) {
                    extract_candidates(expr.definitions[i]);
                }
            } else if (AST_DWLoop.hasInstance(expr)) {
                extract_candidates(expr.condition);
                if (!AST_Block.hasInstance(expr.body)) {
                    extract_candidates(expr.body);
                }
            } else if (AST_Exit.hasInstance(expr)) {
                if (expr.value)
                    extract_candidates(expr.value);
            } else if (AST_For.hasInstance(expr)) {
                if (expr.init)
                    extract_candidates(expr.init);
                if (expr.condition)
                    extract_candidates(expr.condition);
                if (expr.step)
                    extract_candidates(expr.step);
                if (!AST_Block.hasInstance(expr.body)) {
                    extract_candidates(expr.body);
                }
            } else if (AST_ForIn.hasInstance(expr)) {
                extract_candidates(expr.object);
                if (!AST_Block.hasInstance(expr.body)) {
                    extract_candidates(expr.body);
                }
            } else if (AST_If.hasInstance(expr)) {
                extract_candidates(expr.condition);
                if (!AST_Block.hasInstance(expr.body)) {
                    extract_candidates(expr.body);
                }
                if (expr.alternative && !AST_Block.hasInstance(expr.alternative)) {
                    extract_candidates(expr.alternative);
                }
            } else if (AST_Sequence.hasInstance(expr)) {
                expr.expressions.forEach(extract_candidates);
            } else if (AST_SimpleStatement.hasInstance(expr)) {
                extract_candidates(expr.body);
            } else if (AST_Switch.hasInstance(expr)) {
                extract_candidates(expr.expression);
                expr.body.forEach(extract_candidates);
            } else if (AST_Unary.hasInstance(expr)) {
                if (expr.operator == "++" || expr.operator == "--") {
                    candidates.push(hit_stack.slice());
                }
            } else if (AST_VarDef.hasInstance(expr)) {
                if (expr.value && !AST_Chain.hasInstance(expr.value)) {
                    candidates.push(hit_stack.slice());
                    extract_candidates(expr.value);
                }
            }
            hit_stack.pop();
        }

        function find_stop(node, level, write_only) {
            var parent = scanner.parent(level);
            if (AST_Assign.hasInstance(parent)) {
                if (write_only
                    && !parent.logical
                    && !(AST_PropAccess.hasInstance(parent.left)
                        || lvalues.has(parent.left.name))) {
                    return find_stop(parent, level + 1, write_only);
                }
                return node;
            }
            if (AST_Binary.hasInstance(parent)) {
                if (write_only && (!lazy_op.has(parent.operator) || parent.left === node)) {
                    return find_stop(parent, level + 1, write_only);
                }
                return node;
            }
            if (AST_Call.hasInstance(parent))
                return node;
            if (AST_Case.hasInstance(parent))
                return node;
            if (AST_Conditional.hasInstance(parent)) {
                if (write_only && parent.condition === node) {
                    return find_stop(parent, level + 1, write_only);
                }
                return node;
            }
            if (AST_Definitions.hasInstance(parent)) {
                return find_stop(parent, level + 1, true);
            }
            if (AST_Exit.hasInstance(parent)) {
                return write_only ? find_stop(parent, level + 1, write_only) : node;
            }
            if (AST_If.hasInstance(parent)) {
                if (write_only && parent.condition === node) {
                    return find_stop(parent, level + 1, write_only);
                }
                return node;
            }
            if (AST_IterationStatement.hasInstance(parent))
                return node;
            if (AST_Sequence.hasInstance(parent)) {
                return find_stop(parent, level + 1, parent.tail_node() !== node);
            }
            if (AST_SimpleStatement.hasInstance(parent)) {
                return find_stop(parent, level + 1, true);
            }
            if (AST_Switch.hasInstance(parent))
                return node;
            if (AST_VarDef.hasInstance(parent))
                return node;
            return null;
        }

        function mangleable_var(var_def) {
            var value = var_def.value;
            if (!AST_SymbolRef.hasInstance(value))
                return;
            if (value.name == "arguments")
                return;
            var def = value.definition();
            if (def.undeclared)
                return;
            return value_def = def;
        }

        function get_lhs(expr) {
            if (AST_Assign.hasInstance(expr) && expr.logical) {
                return false;
            } else if (AST_VarDef.hasInstance(expr) && AST_SymbolDeclaration.hasInstance(expr.name)) {
                var def = expr.name.definition();
                if (!member(expr.name, def.orig))
                    return;
                var referenced = def.references.length - def.replaced;
                if (!referenced)
                    return;
                var declared = def.orig.length - def.eliminated;
                if (declared > 1 && !AST_SymbolFunarg.hasInstance(expr.name)
                    || (referenced > 1 ? mangleable_var(expr) : !compressor.exposed(def))) {
                    return make_node(AST_SymbolRef, expr.name, expr.name);
                }
            } else {
                const lhs = AST_Assign.hasInstance(expr)
                    ? expr.left
                    : expr.expression;
                return !is_ref_of(lhs, AST_SymbolConst)
                    && !is_ref_of(lhs, AST_SymbolLet) && lhs;
            }
        }

        function get_rvalue(expr) {
            if (AST_Assign.hasInstance(expr)) {
                return expr.right;
            } else {
                return expr.value;
            }
        }

        function get_lvalues(expr) {
            var lvalues = new Map();
            if (AST_Unary.hasInstance(expr))
                return lvalues;
            var tw = new TreeWalker(function (node) {
                var sym = node;
                while (AST_PropAccess.hasInstance(sym))
                    sym = sym.expression;
                if (AST_SymbolRef.hasInstance(sym) || AST_This.hasInstance(sym)) {
                    lvalues.set(sym.name, lvalues.get(sym.name) || is_modified(compressor, tw, node, node, 0));
                }
            });
            get_rvalue(expr).walk(tw);
            return lvalues;
        }

        function remove_candidate(expr) {
            if (AST_SymbolFunarg.hasInstance(expr.name)) {
                var iife = compressor.parent(), argnames = compressor.self().argnames;
                var index = argnames.indexOf(expr.name);
                if (index < 0) {
                    iife.args.length = Math.min(iife.args.length, argnames.length - 1);
                } else {
                    var args = iife.args;
                    if (args[index])
                        args[index] = make_node(AST_Number, args[index], {
                            value: 0
                        });
                }
                return true;
            }
            var found = false;
            return statements[stat_index].transform(new TreeTransformer(function (node, descend, in_list) {
                if (found)
                    return node;
                if (node === expr || node.body === expr) {
                    found = true;
                    if (AST_VarDef.hasInstance(node)) {
                        node.value = AST_SymbolConst.hasInstance(node.name)
                            ? make_node(AST_Undefined, node.value) // `const` always needs value.
                            : null;
                        return node;
                    }
                    return in_list ? MAP.skip : null;
                }
            }, function (node) {
                if (AST_Sequence.hasInstance(node))
                    switch (node.expressions.length) {
                        case 0: return null;
                        case 1: return node.expressions[0];
                    }
            }));
        }

        function is_lhs_local(lhs) {
            while (AST_PropAccess.hasInstance(lhs))
                lhs = lhs.expression;
            return AST_SymbolRef.hasInstance(lhs)
                && lhs.definition().scope === scope
                && !(in_loop
                    && (lvalues.has(lhs.name)
                        || AST_Unary.hasInstance(candidate)
                        || (AST_Assign.hasInstance(candidate)
                            && !candidate.logical
                            && candidate.operator != "=")));
        }

        function value_has_side_effects(expr) {
            if (AST_Unary.hasInstance(expr))
                return unary_side_effects.has(expr.operator);
            return get_rvalue(expr).has_side_effects(compressor);
        }

        function replace_all_symbols() {
            if (side_effects)
                return false;
            if (value_def)
                return true;
            if (AST_SymbolRef.hasInstance(lhs)) {
                var def = lhs.definition();
                if (def.references.length - def.replaced == (AST_VarDef.hasInstance(candidate) ? 1 : 2)) {
                    return true;
                }
            }
            return false;
        }

        function may_modify(sym) {
            if (!sym.definition)
                return true; // AST_Destructuring
            var def = sym.definition();
            if (def.orig.length == 1 && AST_SymbolDefun.hasInstance(def.orig[0]))
                return false;
            if (def.scope.get_defun_scope() !== scope)
                return true;
            return !def.references.every((ref) => {
                var s = ref.scope.get_defun_scope();
                // "block" scope within AST_Catch
                if (s.TYPE == "Scope")
                    s = s.parent_scope;
                return s === scope;
            });
        }

        function side_effects_external(node, lhs) {
            if (AST_Assign.hasInstance(node))
                return side_effects_external(node.left, true);
            if (AST_Unary.hasInstance(node))
                return side_effects_external(node.expression, true);
            if (AST_VarDef.hasInstance(node))
                return node.value && side_effects_external(node.value);
            if (lhs) {
                if (AST_Dot.hasInstance(node))
                    return side_effects_external(node.expression, true);
                if (AST_Sub.hasInstance(node))
                    return side_effects_external(node.expression, true);
                if (AST_SymbolRef.hasInstance(node))
                    return node.definition().scope !== scope;
            }
            return false;
        }
    }

    function eliminate_spurious_blocks(statements) {
        var seen_dirs = [];
        for (var i = 0; i < statements.length;) {
            var stat = statements[i];
            if (AST_BlockStatement.hasInstance(stat) && stat.body.every(can_be_evicted_from_block)) {
                CHANGED = true;
                eliminate_spurious_blocks(stat.body);
                statements.splice(i, 1, ...stat.body);
                i += stat.body.length;
            } else if (AST_EmptyStatement.hasInstance(stat)) {
                CHANGED = true;
                statements.splice(i, 1);
            } else if (AST_Directive.hasInstance(stat)) {
                if (seen_dirs.indexOf(stat.value) < 0) {
                    i++;
                    seen_dirs.push(stat.value);
                } else {
                    CHANGED = true;
                    statements.splice(i, 1);
                }
            } else
                i++;
        }
    }

    function handle_if_return(statements, compressor) {
        var self = compressor.self();
        var multiple_if_returns = has_multiple_if_returns(statements);
        var in_lambda = AST_Lambda.hasInstance(self);
        for (var i = statements.length; --i >= 0;) {
            var stat = statements[i];
            var j = next_index(i);
            var next = statements[j];

            if (in_lambda && !next && AST_Return.hasInstance(stat)) {
                if (!stat.value) {
                    CHANGED = true;
                    statements.splice(i, 1);
                    continue;
                }
                if (AST_UnaryPrefix.hasInstance(stat.value) && stat.value.operator == "void") {
                    CHANGED = true;
                    statements[i] = make_node(AST_SimpleStatement, stat, {
                        body: stat.value.expression
                    });
                    continue;
                }
            }

            if (AST_If.hasInstance(stat)) {
                var ab = aborts(stat.body);
                if (can_merge_flow(ab)) {
                    if (ab.label) {
                        remove(ab.label.thedef.references, ab);
                    }
                    CHANGED = true;
                    stat = stat.clone();
                    stat.condition = stat.condition.negate(compressor);
                    var body = as_statement_array_with_return(stat.body, ab);
                    stat.body = make_node(AST_BlockStatement, stat, {
                        body: as_statement_array(stat.alternative).concat(extract_functions())
                    });
                    stat.alternative = make_node(AST_BlockStatement, stat, {
                        body: body
                    });
                    statements[i] = stat.transform(compressor);
                    continue;
                }

                var ab = aborts(stat.alternative);
                if (can_merge_flow(ab)) {
                    if (ab.label) {
                        remove(ab.label.thedef.references, ab);
                    }
                    CHANGED = true;
                    stat = stat.clone();
                    stat.body = make_node(AST_BlockStatement, stat.body, {
                        body: as_statement_array(stat.body).concat(extract_functions())
                    });
                    var body = as_statement_array_with_return(stat.alternative, ab);
                    stat.alternative = make_node(AST_BlockStatement, stat.alternative, {
                        body: body
                    });
                    statements[i] = stat.transform(compressor);
                    continue;
                }
            }

            if (AST_If.hasInstance(stat) && AST_Return.hasInstance(stat.body)) {
                var value = stat.body.value;
                //---
                // pretty silly case, but:
                // if (foo()) return; return; ==> foo(); return;
                if (!value && !stat.alternative
                    && (in_lambda && !next || AST_Return.hasInstance(next) && !next.value)) {
                    CHANGED = true;
                    statements[i] = make_node(AST_SimpleStatement, stat.condition, {
                        body: stat.condition
                    });
                    continue;
                }
                //---
                // if (foo()) return x; return y; ==> return foo() ? x : y;
                if (value && !stat.alternative && AST_Return.hasInstance(next) && next.value) {
                    CHANGED = true;
                    stat = stat.clone();
                    stat.alternative = next;
                    statements[i] = stat.transform(compressor);
                    statements.splice(j, 1);
                    continue;
                }
                //---
                // if (foo()) return x; [ return ; ] ==> return foo() ? x : undefined;
                if (value && !stat.alternative
                    && (!next && in_lambda && multiple_if_returns
                        || AST_Return.hasInstance(next))) {
                    CHANGED = true;
                    stat = stat.clone();
                    stat.alternative = next || make_node(AST_Return, stat, {
                        value: null
                    });
                    statements[i] = stat.transform(compressor);
                    if (next)
                        statements.splice(j, 1);
                    continue;
                }
                //---
                // if (a) return b; if (c) return d; e; ==> return a ? b : c ? d : void e;
                //
                // if sequences is not enabled, this can lead to an endless loop (issue #866).
                // however, with sequences on this helps producing slightly better output for
                // the example code.
                var prev = statements[prev_index(i)];
                if (compressor.option("sequences") && in_lambda && !stat.alternative
                    && AST_If.hasInstance(prev) && AST_Return.hasInstance(prev.body)
                    && next_index(j) == statements.length && AST_SimpleStatement.hasInstance(next)) {
                    CHANGED = true;
                    stat = stat.clone();
                    stat.alternative = make_node(AST_BlockStatement, next, {
                        body: [
                            next,
                            make_node(AST_Return, next, {
                                value: null
                            })
                        ]
                    });
                    statements[i] = stat.transform(compressor);
                    statements.splice(j, 1);
                    continue;
                }
            }
        }

        function has_multiple_if_returns(statements) {
            var n = 0;
            for (var i = statements.length; --i >= 0;) {
                var stat = statements[i];
                if (AST_If.hasInstance(stat) && AST_Return.hasInstance(stat.body)) {
                    if (++n > 1)
                        return true;
                }
            }
            return false;
        }

        function is_return_void(value) {
            return !value || AST_UnaryPrefix.hasInstance(value) && value.operator == "void";
        }

        function can_merge_flow(ab) {
            if (!ab)
                return false;
            for (var j = i + 1, len = statements.length; j < len; j++) {
                var stat = statements[j];
                if (AST_Const.hasInstance(stat) || AST_Let.hasInstance(stat))
                    return false;
            }
            var lct = AST_LoopControl.hasInstance(ab) ? compressor.loopcontrol_target(ab) : null;
            return AST_Return.hasInstance(ab) && in_lambda && is_return_void(ab.value)
                || AST_Continue.hasInstance(ab) && self === loop_body(lct)
                || AST_Break.hasInstance(ab) && AST_BlockStatement.hasInstance(lct) && self === lct;
        }

        function extract_functions() {
            var tail = statements.slice(i + 1);
            statements.length = i + 1;
            return tail.filter(function (stat) {
                if (AST_Defun.hasInstance(stat)) {
                    statements.push(stat);
                    return false;
                }
                return true;
            });
        }

        function as_statement_array_with_return(node, ab) {
            var body = as_statement_array(node).slice(0, -1);
            if (ab.value) {
                body.push(make_node(AST_SimpleStatement, ab.value, {
                    body: ab.value.expression
                }));
            }
            return body;
        }

        function next_index(i) {
            for (var j = i + 1, len = statements.length; j < len; j++) {
                var stat = statements[j];
                if (!(AST_Var.hasInstance(stat) && declarations_only(stat))) {
                    break;
                }
            }
            return j;
        }

        function prev_index(i) {
            for (var j = i; --j >= 0;) {
                var stat = statements[j];
                if (!(AST_Var.hasInstance(stat) && declarations_only(stat))) {
                    break;
                }
            }
            return j;
        }
    }

    function eliminate_dead_code(statements, compressor) {
        var has_quit;
        var self = compressor.self();
        for (var i = 0, n = 0, len = statements.length; i < len; i++) {
            var stat = statements[i];
            if (AST_LoopControl.hasInstance(stat)) {
                var lct = compressor.loopcontrol_target(stat);
                if (AST_Break.hasInstance(stat)
                    && !AST_IterationStatement.hasInstance(lct)
                    && loop_body(lct) === self
                    || AST_Continue.hasInstance(stat)
                    && loop_body(lct) === self) {
                    if (stat.label) {
                        remove(stat.label.thedef.references, stat);
                    }
                } else {
                    statements[n++] = stat;
                }
            } else {
                statements[n++] = stat;
            }
            if (aborts(stat)) {
                has_quit = statements.slice(i + 1);
                break;
            }
        }
        statements.length = n;
        CHANGED = n != len;
        if (has_quit)
            has_quit.forEach(function (stat) {
                trim_unreachable_code(compressor, stat, statements);
            });
    }

    function declarations_only(node) {
        return node.definitions.every((var_def) => !var_def.value
        );
    }

    function sequencesize(statements, compressor) {
        if (statements.length < 2)
            return;
        var seq = [], n = 0;
        function push_seq() {
            if (!seq.length)
                return;
            var body = make_sequence(seq[0], seq);
            statements[n++] = make_node(AST_SimpleStatement, body, { body: body });
            seq = [];
        }
        for (var i = 0, len = statements.length; i < len; i++) {
            var stat = statements[i];
            if (AST_SimpleStatement.hasInstance(stat)) {
                if (seq.length >= compressor.sequences_limit)
                    push_seq();
                var body = stat.body;
                if (seq.length > 0)
                    body = body.drop_side_effect_free(compressor);
                if (body)
                    merge_sequence(seq, body);
            } else if (AST_Definitions.hasInstance(stat) && declarations_only(stat)
                || AST_Defun.hasInstance(stat)) {
                statements[n++] = stat;
            } else {
                push_seq();
                statements[n++] = stat;
            }
        }
        push_seq();
        statements.length = n;
        if (n != len)
            CHANGED = true;
    }

    function to_simple_statement(block, decls) {
        if (!AST_BlockStatement.hasInstance(block))
            return block;
        var stat = null;
        for (var i = 0, len = block.body.length; i < len; i++) {
            var line = block.body[i];
            if (AST_Var.hasInstance(line) && declarations_only(line)) {
                decls.push(line);
            } else if (stat) {
                return false;
            } else {
                stat = line;
            }
        }
        return stat;
    }

    function sequencesize_2(statements, compressor) {
        function cons_seq(right) {
            n--;
            CHANGED = true;
            var left = prev.body;
            return make_sequence(left, [left, right]).transform(compressor);
        }
        var n = 0, prev;
        for (var i = 0; i < statements.length; i++) {
            var stat = statements[i];
            if (prev) {
                if (AST_Exit.hasInstance(stat)) {
                    stat.value = cons_seq(stat.value || make_node(AST_Undefined, stat).transform(compressor));
                } else if (AST_For.hasInstance(stat)) {
                    if (!AST_Definitions.hasInstance(stat.init)) {
                        const abort = walk(prev.body, node => {
                            if (AST_Scope.hasInstance(node))
                                return true;
                            if (AST_Binary.hasInstance(node)
                                && node.operator === "in") {
                                return walk_abort;
                            }
                        });
                        if (!abort) {
                            if (stat.init)
                                stat.init = cons_seq(stat.init);
                            else {
                                stat.init = prev.body;
                                n--;
                                CHANGED = true;
                            }
                        }
                    }
                } else if (AST_ForIn.hasInstance(stat)) {
                    if (!AST_Const.hasInstance(stat.init) && !AST_Let.hasInstance(stat.init)) {
                        stat.object = cons_seq(stat.object);
                    }
                } else if (AST_If.hasInstance(stat)) {
                    stat.condition = cons_seq(stat.condition);
                } else if (AST_Switch.hasInstance(stat)) {
                    stat.expression = cons_seq(stat.expression);
                } else if (AST_With.hasInstance(stat)) {
                    stat.expression = cons_seq(stat.expression);
                }
            }
            if (compressor.option("conditionals") && AST_If.hasInstance(stat)) {
                var decls = [];
                var body = to_simple_statement(stat.body, decls);
                var alt = to_simple_statement(stat.alternative, decls);
                if (body !== false && alt !== false && decls.length > 0) {
                    var len = decls.length;
                    decls.push(make_node(AST_If, stat, {
                        condition: stat.condition,
                        body: body || make_node(AST_EmptyStatement, stat.body),
                        alternative: alt
                    }));
                    decls.unshift(n, 1);
                    [].splice.apply(statements, decls);
                    i += len;
                    n += len + 1;
                    prev = null;
                    CHANGED = true;
                    continue;
                }
            }
            statements[n++] = stat;
            prev = AST_SimpleStatement.hasInstance(stat) ? stat : null;
        }
        statements.length = n;
    }

    function join_object_assignments(defn, body) {
        if (!AST_Definitions.hasInstance(defn))
            return;
        var def = defn.definitions[defn.definitions.length - 1];
        if (!AST_Object.hasInstance(def.value))
            return;
        var exprs;
        if (AST_Assign.hasInstance(body) && !body.logical) {
            exprs = [body];
        } else if (AST_Sequence.hasInstance(body)) {
            exprs = body.expressions.slice();
        }
        if (!exprs)
            return;
        var trimmed = false;
        do {
            var node = exprs[0];
            if (!AST_Assign.hasInstance(node))
                break;
            if (node.operator != "=")
                break;
            if (!AST_PropAccess.hasInstance(node.left))
                break;
            var sym = node.left.expression;
            if (!AST_SymbolRef.hasInstance(sym))
                break;
            if (def.name.name != sym.name)
                break;
            if (!node.right.is_constant_expression(scope))
                break;
            var prop = node.left.property;
            if (AST_Node.hasInstance(prop)) {
                prop = prop.evaluate(compressor);
            }
            if (AST_Node.hasInstance(prop))
                break;
            prop = "" + prop;
            var diff = compressor.option("ecma") < 2015
                && compressor.has_directive("use strict") ? function (node) {
                    return node.key != prop && (node.key && node.key.name != prop);
                } : function (node) {
                    return node.key && node.key.name != prop;
                };
            if (!def.value.properties.every(diff))
                break;
            var p = def.value.properties.filter(function (p) { return p.key === prop; })[0];
            if (!p) {
                def.value.properties.push(make_node(AST_ObjectKeyVal, node, {
                    key: prop,
                    value: node.right
                }));
            } else {
                p.value = new AST_Sequence({
                    start: p.start,
                    expressions: [p.value.clone(), node.right.clone()],
                    end: p.end
                });
            }
            exprs.shift();
            trimmed = true;
        } while (exprs.length);
        return trimmed && exprs;
    }

    function join_consecutive_vars(statements) {
        var defs;
        for (var i = 0, j = -1, len = statements.length; i < len; i++) {
            var stat = statements[i];
            var prev = statements[j];
            if (AST_Definitions.hasInstance(stat)) {
                if (prev && prev.TYPE == stat.TYPE) {
                    prev.definitions = prev.definitions.concat(stat.definitions);
                    CHANGED = true;
                } else if (defs && defs.TYPE == stat.TYPE && declarations_only(stat)) {
                    defs.definitions = defs.definitions.concat(stat.definitions);
                    CHANGED = true;
                } else {
                    statements[++j] = stat;
                    defs = stat;
                }
            } else if (AST_Exit.hasInstance(stat)) {
                stat.value = extract_object_assignments(stat.value);
            } else if (AST_For.hasInstance(stat)) {
                var exprs = join_object_assignments(prev, stat.init);
                if (exprs) {
                    CHANGED = true;
                    stat.init = exprs.length ? make_sequence(stat.init, exprs) : null;
                    statements[++j] = stat;
                } else if (AST_Var.hasInstance(prev) && (!stat.init || stat.init.TYPE == prev.TYPE)) {
                    if (stat.init) {
                        prev.definitions = prev.definitions.concat(stat.init.definitions);
                    }
                    stat.init = prev;
                    statements[j] = stat;
                    CHANGED = true;
                } else if (defs && stat.init && defs.TYPE == stat.init.TYPE && declarations_only(stat.init)) {
                    defs.definitions = defs.definitions.concat(stat.init.definitions);
                    stat.init = null;
                    statements[++j] = stat;
                    CHANGED = true;
                } else {
                    statements[++j] = stat;
                }
            } else if (AST_ForIn.hasInstance(stat)) {
                stat.object = extract_object_assignments(stat.object);
            } else if (AST_If.hasInstance(stat)) {
                stat.condition = extract_object_assignments(stat.condition);
            } else if (AST_SimpleStatement.hasInstance(stat)) {
                var exprs = join_object_assignments(prev, stat.body);
                if (exprs) {
                    CHANGED = true;
                    if (!exprs.length)
                        continue;
                    stat.body = make_sequence(stat.body, exprs);
                }
                statements[++j] = stat;
            } else if (AST_Switch.hasInstance(stat)) {
                stat.expression = extract_object_assignments(stat.expression);
            } else if (AST_With.hasInstance(stat)) {
                stat.expression = extract_object_assignments(stat.expression);
            } else {
                statements[++j] = stat;
            }
        }
        statements.length = j + 1;

        function extract_object_assignments(value) {
            statements[++j] = stat;
            var exprs = join_object_assignments(prev, value);
            if (exprs) {
                CHANGED = true;
                if (exprs.length) {
                    return make_sequence(value, exprs);
                } else if (AST_Sequence.hasInstance(value)) {
                    return value.tail_node().left;
                } else {
                    return value.left;
                }
            }
            return value;
        }
    }
}
