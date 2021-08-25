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
    AST_Accessor,
    AST_Array,
    AST_Arrow,
    AST_Assign,
    AST_BigInt,
    AST_Binary,
    AST_Block,
    AST_BlockStatement,
    AST_Boolean,
    AST_Break,
    AST_Call,
    AST_Catch,
    AST_Chain,
    AST_Class,
    AST_ClassExpression,
    AST_ClassProperty,
    AST_ConciseMethod,
    AST_Conditional,
    AST_Const,
    AST_Constant,
    AST_Debugger,
    AST_Default,
    AST_DefaultAssign,
    AST_DefClass,
    AST_Definitions,
    AST_Defun,
    AST_Destructuring,
    AST_Directive,
    AST_Do,
    AST_Dot,
    AST_DWLoop,
    AST_EmptyStatement,
    AST_Exit,
    AST_Expansion,
    AST_Export,
    AST_False,
    AST_For,
    AST_ForIn,
    AST_Function,
    AST_Hole,
    AST_If,
    AST_Import,
    AST_Infinity,
    AST_IterationStatement,
    AST_LabeledStatement,
    AST_Lambda,
    AST_Let,
    AST_NaN,
    AST_New,
    AST_Node,
    AST_Null,
    AST_Number,
    AST_Object,
    AST_ObjectKeyVal,
    AST_ObjectProperty,
    AST_PrefixedTemplateString,
    AST_PropAccess,
    AST_RegExp,
    AST_Return,
    AST_Scope,
    AST_Sequence,
    AST_SimpleStatement,
    AST_Statement,
    AST_String,
    AST_Sub,
    AST_Switch,
    AST_SwitchBranch,
    AST_Symbol,
    AST_SymbolBlockDeclaration,
    AST_SymbolCatch,
    AST_SymbolClassProperty,
    AST_SymbolDeclaration,
    AST_SymbolDefun,
    AST_SymbolExport,
    AST_SymbolFunarg,
    AST_SymbolLambda,
    AST_SymbolLet,
    AST_SymbolMethod,
    AST_SymbolRef,
    AST_SymbolVar,
    AST_TemplateString,
    AST_This,
    AST_Toplevel,
    AST_True,
    AST_Try,
    AST_Unary,
    AST_UnaryPostfix,
    AST_UnaryPrefix,
    AST_Undefined,
    AST_Var,
    AST_VarDef,
    AST_While,
    AST_With,
    AST_Yield,

    TreeTransformer,
    TreeWalker,
    walk,
    walk_abort,
    walk_parent,

    _INLINE,
    _NOINLINE,
    _PURE
} from "../ast.js";
import {
    defaults,
    HOP,
    keep_name,
    make_node,
    makePredicate,
    map_add,
    MAP,
    member,
    remove,
    return_false,
    return_true,
    regexp_source_fix,
    has_annotation
} from "../utils/index.js";
import { first_in_statement } from "../utils/first_in_statement.js";
import { equivalent_to } from "../equivalent-to.js";
import {
    is_basic_identifier_string,
    JS_Parse_Error,
    parse,
    PRECEDENCE,
} from "../parse.js";
import { OutputStream } from "../output.js";
import {
    base54,
    SymbolDef,
} from "../scope.js";
import "../size.js";

import "./evaluate.js";
import "./drop-side-effect-free.js";
import "./reduce-vars.js";
import {
    is_undeclared_ref,
    lazy_op,
    is_nullish,
    is_undefined,
    is_lhs,
    aborts,
} from "./inference.js";
import {
    SQUEEZED,
    OPTIMIZED,
    INLINED,
    CLEAR_BETWEEN_PASSES,
    TOP,
    WRITE_ONLY,
    UNDEFINED,
    UNUSED,
    TRUTHY,
    FALSY,

    has_flag,
    set_flag,
    clear_flag,
} from "./compressor-flags.js";
import {
    make_sequence,
    best_of,
    best_of_expression,
    make_node_from_constant,
    merge_sequence,
    get_simple_key,
    has_break_or_continue,
    maintain_this_binding,
    identifier_atom,
    is_identifier_atom,
    is_func_expr,
    is_ref_of,
    can_be_evicted_from_block,
    as_statement_array,
    is_iife_call,
    is_recursive_ref
} from "./common.js";
import { tighten_body, trim_unreachable_code } from "./tighten-body.js";

class Compressor extends TreeWalker {
    constructor(options, { false_by_default = false, mangle_options = false }) {
        super();
        if (options.defaults !== undefined && !options.defaults) false_by_default = true;
        this.options = defaults(options, {
            arguments     : false,
            arrows        : !false_by_default,
            booleans      : !false_by_default,
            booleans_as_integers : false,
            collapse_vars : !false_by_default,
            comparisons   : !false_by_default,
            computed_props: !false_by_default,
            conditionals  : !false_by_default,
            dead_code     : !false_by_default,
            defaults      : true,
            directives    : !false_by_default,
            drop_console  : false,
            drop_debugger : !false_by_default,
            ecma          : 5,
            evaluate      : !false_by_default,
            expression    : false,
            global_defs   : false,
            hoist_funs    : false,
            hoist_props   : !false_by_default,
            hoist_vars    : false,
            ie8           : false,
            if_return     : !false_by_default,
            inline        : !false_by_default,
            join_vars     : !false_by_default,
            keep_classnames: false,
            keep_fargs    : true,
            keep_fnames   : false,
            keep_infinity : false,
            loops         : !false_by_default,
            module        : false,
            negate_iife   : !false_by_default,
            passes        : 1,
            properties    : !false_by_default,
            pure_getters  : !false_by_default && "strict",
            pure_funcs    : null,
            reduce_funcs  : !false_by_default,
            reduce_vars   : !false_by_default,
            sequences     : !false_by_default,
            side_effects  : !false_by_default,
            switches      : !false_by_default,
            top_retain    : null,
            toplevel      : !!(options && options["top_retain"]),
            typeofs       : !false_by_default,
            unsafe        : false,
            unsafe_arrows : false,
            unsafe_comps  : false,
            unsafe_Function: false,
            unsafe_math   : false,
            unsafe_symbols: false,
            unsafe_methods: false,
            unsafe_proto  : false,
            unsafe_regexp : false,
            unsafe_undefined: false,
            unused        : !false_by_default,
            warnings      : false  // legacy
        }, true);
        var global_defs = this.options["global_defs"];
        if (typeof global_defs == "object") for (var key in global_defs) {
            if (key[0] === "@" && HOP(global_defs, key)) {
                global_defs[key.slice(1)] = parse(global_defs[key], {
                    expression: true
                });
            }
        }
        if (this.options["inline"] === true) this.options["inline"] = 3;
        var pure_funcs = this.options["pure_funcs"];
        if (typeof pure_funcs == "function") {
            this.pure_funcs = pure_funcs;
        } else {
            this.pure_funcs = pure_funcs ? function(node) {
                return !pure_funcs.includes(node.expression.print_to_string());
            } : return_true;
        }
        var top_retain = this.options["top_retain"];
        if (top_retain instanceof RegExp) {
            this.top_retain = function(def) {
                return top_retain.test(def.name);
            };
        } else if (typeof top_retain == "function") {
            this.top_retain = top_retain;
        } else if (top_retain) {
            if (typeof top_retain == "string") {
                top_retain = top_retain.split(/,/);
            }
            this.top_retain = function(def) {
                return top_retain.includes(def.name);
            };
        }
        if (this.options["module"]) {
            this.directives["use strict"] = true;
            this.options["toplevel"] = true;
        }
        var toplevel = this.options["toplevel"];
        this.toplevel = typeof toplevel == "string" ? {
            funcs: /funcs/.test(toplevel),
            vars: /vars/.test(toplevel)
        } : {
            funcs: toplevel,
            vars: toplevel
        };
        var sequences = this.options["sequences"];
        this.sequences_limit = sequences == 1 ? 800 : sequences | 0;
        this.evaluated_regexps = new Map();
        this._toplevel = undefined;
        this.mangle_options = mangle_options;
    }

    option(key) {
        return this.options[key];
    }

    exposed(def) {
        if (def.export) return true;
        if (def.global) for (var i = 0, len = def.orig.length; i < len; i++)
            if (!this.toplevel[AST_SymbolDefun.hasInstance(def.orig[i]) ? "funcs" : "vars"])
                return true;
        return false;
    }

    in_boolean_context() {
        if (!this.option("booleans")) return false;
        var self = this.self();
        for (var i = 0, p; p = this.parent(i); i++) {
            if (AST_SimpleStatement.hasInstance(p)
                || AST_Conditional.hasInstance(p) && p.condition === self
                || AST_DWLoop.hasInstance(p) && p.condition === self
                || AST_For.hasInstance(p) && p.condition === self
                || AST_If.hasInstance(p) && p.condition === self
                || AST_UnaryPrefix.hasInstance(p) && p.operator == "!" && p.expression === self) {
                return true;
            }
            if (
                AST_Binary.hasInstance(p)
                    && (
                        p.operator == "&&"
                        || p.operator == "||"
                        || p.operator == "??"
                    )
                || AST_Conditional.hasInstance(p)
                || p.tail_node() === self
            ) {
                self = p;
            } else {
                return false;
            }
        }
    }

    get_toplevel() {
        return this._toplevel;
    }

    compress(toplevel) {
        toplevel = toplevel.resolve_defines(this);
        this._toplevel = toplevel;
        if (this.option("expression")) {
            this._toplevel.process_expression(true);
        }
        var passes = +this.options.passes || 1;
        var min_count = 1 / 0;
        var stopping = false;
        var nth_identifier = this.mangle_options && this.mangle_options.nth_identifier || base54;
        var mangle = { ie8: this.option("ie8"), nth_identifier: nth_identifier };
        for (var pass = 0; pass < passes; pass++) {
            this._toplevel.figure_out_scope(mangle);
            if (pass === 0 && this.option("drop_console")) {
                // must be run before reduce_vars and compress pass
                this._toplevel = this._toplevel.drop_console();
            }
            if (pass > 0 || this.option("reduce_vars")) {
                this._toplevel.reset_opt_flags(this);
            }
            this._toplevel = this._toplevel.transform(this);
            if (passes > 1) {
                let count = 0;
                walk(this._toplevel, () => { count++; });
                if (count < min_count) {
                    min_count = count;
                    stopping = false;
                } else if (stopping) {
                    break;
                } else {
                    stopping = true;
                }
            }
        }
        if (this.option("expression")) {
            this._toplevel.process_expression(false);
        }
        toplevel = this._toplevel;
        this._toplevel = undefined;
        return toplevel;
    }

    before(node, descend) {
        if (has_flag(node, SQUEEZED)) return node;
        var was_scope = false;
        if (AST_Scope.hasInstance(node)) {
            node = node.hoist_properties(this);
            node = node.hoist_declarations(this);
            was_scope = true;
        }
        // Before https://github.com/mishoo/UglifyJS2/pull/1602 AST_Node.optimize()
        // would call AST_Node.transform() if a different instance of AST_Node is
        // produced after def_optimize().
        // This corrupts TreeWalker.stack, which cause AST look-ups to malfunction.
        // Migrate and defer all children's AST_Node.transform() to below, which
        // will now happen after this parent AST_Node has been properly substituted
        // thus gives a consistent AST snapshot.
        descend(node, this);
        // Existing code relies on how AST_Node.optimize() worked, and omitting the
        // following replacement call would result in degraded efficiency of both
        // output and performance.
        descend(node, this);
        var opt = node.optimize(this);
        if (was_scope && AST_Scope.hasInstance(opt)) {
            opt.drop_unused(this);
            descend(opt, this);
        }
        if (opt === node) set_flag(opt, SQUEEZED);
        return opt;
    }
}

function def_optimize(node, optimizer) {
    node.DEFMETHOD("optimize", function(compressor) {
        var self = this;
        if (has_flag(self, OPTIMIZED)) return self;
        if (compressor.has_directive("use asm")) return self;
        var opt = optimizer(self, compressor);
        set_flag(opt, OPTIMIZED);
        return opt;
    });
}

def_optimize(AST_Node, function(self) {
    return self;
});

AST_Toplevel.DEFMETHOD("drop_console", function() {
    return this.transform(new TreeTransformer(function(self) {
        if (self.TYPE == "Call") {
            var exp = self.expression;
            if (AST_PropAccess.hasInstance(exp)) {
                var name = exp.expression;
                while (name.expression) {
                    name = name.expression;
                }
                if (is_undeclared_ref(name) && name.name == "console") {
                    return make_node(AST_Undefined, self);
                }
            }
        }
    }));
});

AST_Node.DEFMETHOD("equivalent_to", function(node) {
    return equivalent_to(this, node);
});

AST_Scope.DEFMETHOD("process_expression", function(insert, compressor) {
    var self = this;
    var tt = new TreeTransformer(function(node) {
        if (insert && AST_SimpleStatement.hasInstance(node)) {
            return make_node(AST_Return, node, {
                value: node.body
            });
        }
        if (!insert && AST_Return.hasInstance(node)) {
            if (compressor) {
                var value = node.value && node.value.drop_side_effect_free(compressor, true);
                return value
                    ? make_node(AST_SimpleStatement, node, { body: value })
                    : make_node(AST_EmptyStatement, node);
            }
            return make_node(AST_SimpleStatement, node, {
                body: node.value || make_node(AST_UnaryPrefix, node, {
                    operator: "void",
                    expression: make_node(AST_Number, node, {
                        value: 0
                    })
                })
            });
        }
        if (AST_Class.hasInstance(node) || AST_Lambda.hasInstance(node) && node !== self) {
            return node;
        }
        if (AST_Block.hasInstance(node)) {
            var index = node.body.length - 1;
            if (index >= 0) {
                node.body[index] = node.body[index].transform(tt);
            }
        } else if (AST_If.hasInstance(node)) {
            node.body = node.body.transform(tt);
            if (node.alternative) {
                node.alternative = node.alternative.transform(tt);
            }
        } else if (AST_With.hasInstance(node)) {
            node.body = node.body.transform(tt);
        }
        return node;
    });
    self.transform(tt);
});

AST_Toplevel.DEFMETHOD("reset_opt_flags", function(compressor) {
    const self = this;
    const reduce_vars = compressor.option("reduce_vars");

    const preparation = new TreeWalker(function(node, descend) {
        clear_flag(node, CLEAR_BETWEEN_PASSES);
        if (reduce_vars) {
            if (compressor.top_retain
                && AST_Defun.hasInstance(node)  // Only functions are retained
                && preparation.parent() === self
            ) {
                set_flag(node, TOP);
            }
            return node.reduce_vars(preparation, descend, compressor);
        }
    });
    // Stack of look-up tables to keep track of whether a `SymbolDef` has been
    // properly assigned before use:
    // - `push()` & `pop()` when visiting conditional branches
    preparation.safe_ids = Object.create(null);
    preparation.in_loop = null;
    preparation.loop_ids = new Map();
    preparation.defs_to_safe_ids = new Map();
    self.walk(preparation);
});

AST_Symbol.DEFMETHOD("fixed_value", function() {
    var fixed = this.thedef.fixed;
    if (!fixed || AST_Node.hasInstance(fixed)) return fixed;
    return fixed();
});

AST_SymbolRef.DEFMETHOD("is_immutable", function() {
    var orig = this.definition().orig;
    return orig.length == 1 && AST_SymbolLambda.hasInstance(orig[0]);
});

function find_scope(tw) {
    for (let i = 0;;i++) {
        const p = tw.parent(i);
        if (AST_Toplevel.hasInstance(p)) return p;
        if (AST_Lambda.hasInstance(p)) return p;
        if (p.block_scope) return p.block_scope;
    }
}

function find_variable(compressor, name) {
    var scope, i = 0;
    while (scope = compressor.parent(i++)) {
        if (AST_Scope.hasInstance(scope)) break;
        if (AST_Catch.hasInstance(scope) && scope.argname) {
            scope = scope.argname.definition().scope;
            break;
        }
    }
    return scope.find_variable(name);
}

function is_empty(thing) {
    if (thing === null) return true;
    if (AST_EmptyStatement.hasInstance(thing)) return true;
    if (AST_BlockStatement.hasInstance(thing)) return thing.body.length == 0;
    return false;
}

var global_names = makePredicate("Array Boolean clearInterval clearTimeout console Date decodeURI decodeURIComponent encodeURI encodeURIComponent Error escape eval EvalError Function isFinite isNaN JSON Math Number parseFloat parseInt RangeError ReferenceError RegExp Object setInterval setTimeout String SyntaxError TypeError unescape URIError");
AST_SymbolRef.DEFMETHOD("is_declared", function(compressor) {
    return !this.definition().undeclared
        || compressor.option("unsafe") && global_names.has(this.name);
});

/* -----[ optimizers ]----- */

var directives = new Set(["use asm", "use strict"]);
def_optimize(AST_Directive, function(self, compressor) {
    if (compressor.option("directives")
        && (!directives.has(self.value) || compressor.has_directive(self.value) !== self)) {
        return make_node(AST_EmptyStatement, self);
    }
    return self;
});

def_optimize(AST_Debugger, function(self, compressor) {
    if (compressor.option("drop_debugger"))
        return make_node(AST_EmptyStatement, self);
    return self;
});

def_optimize(AST_LabeledStatement, function(self, compressor) {
    if (AST_Break.hasInstance(self.body)
        && compressor.loopcontrol_target(self.body) === self.body) {
        return make_node(AST_EmptyStatement, self);
    }
    return self.label.references.length == 0 ? self.body : self;
});

def_optimize(AST_Block, function(self, compressor) {
    tighten_body(self.body, compressor);
    return self;
});

function can_be_extracted_from_if_block(node) {
    return !(
        AST_Const.hasInstance(node)
        || AST_Let.hasInstance(node)
        || AST_Class.hasInstance(node)
    );
}

def_optimize(AST_BlockStatement, function(self, compressor) {
    tighten_body(self.body, compressor);
    switch (self.body.length) {
      case 1:
        if (!compressor.has_directive("use strict")
            && AST_If.hasInstance(compressor.parent())
            && can_be_extracted_from_if_block(self.body[0])
            || can_be_evicted_from_block(self.body[0])) {
            return self.body[0];
        }
        break;
      case 0: return make_node(AST_EmptyStatement, self);
    }
    return self;
});

function opt_AST_Lambda(self, compressor) {
    tighten_body(self.body, compressor);
    if (compressor.option("side_effects")
        && self.body.length == 1
        && self.body[0] === compressor.has_directive("use strict")) {
        self.body.length = 0;
    }
    return self;
}
def_optimize(AST_Lambda, opt_AST_Lambda);

const r_keep_assign = /keep_assign/;
AST_Scope.DEFMETHOD("drop_unused", function(compressor) {
    if (!compressor.option("unused")) return;
    if (compressor.has_directive("use asm")) return;
    var self = this;
    if (self.pinned()) return;
    var drop_funcs = !AST_Toplevel.hasInstance(self) || compressor.toplevel.funcs;
    var drop_vars = !AST_Toplevel.hasInstance(self) || compressor.toplevel.vars;
    const assign_as_unused = r_keep_assign.test(compressor.option("unused")) ? return_false : function(node) {
        if (AST_Assign.hasInstance(node)
            && !node.logical
            && (has_flag(node, WRITE_ONLY) || node.operator == "=")
        ) {
            return node.left;
        }
        if (AST_Unary.hasInstance(node) && has_flag(node, WRITE_ONLY)) {
            return node.expression;
        }
    };
    var in_use_ids = new Map();
    var fixed_ids = new Map();
    if (AST_Toplevel.hasInstance(self) && compressor.top_retain) {
        self.variables.forEach(function(def) {
            if (compressor.top_retain(def) && !in_use_ids.has(def.id)) {
                in_use_ids.set(def.id, def);
            }
        });
    }
    var var_defs_by_id = new Map();
    var initializations = new Map();
    // pass 1: find out which symbols are directly used in
    // this scope (not in nested scopes).
    var scope = this;
    var tw = new TreeWalker(function(node, descend) {
        if (AST_Lambda.hasInstance(node) && node.uses_arguments && !tw.has_directive("use strict")) {
            node.argnames.forEach(function(argname) {
                if (!AST_SymbolDeclaration.hasInstance(argname)) return;
                var def = argname.definition();
                if (!in_use_ids.has(def.id)) {
                    in_use_ids.set(def.id, def);
                }
            });
        }
        if (node === self) return;
        if (AST_Defun.hasInstance(node) || AST_DefClass.hasInstance(node)) {
            var node_def = node.name.definition();
            const in_export = AST_Export.hasInstance(tw.parent());
            if (in_export || !drop_funcs && scope === self) {
                if (node_def.global && !in_use_ids.has(node_def.id)) {
                    in_use_ids.set(node_def.id, node_def);
                }
            }
            if (AST_DefClass.hasInstance(node)) {
                if (
                    node.extends
                    && (node.extends.has_side_effects(compressor)
                    || node.extends.may_throw(compressor))
                ) {
                    node.extends.walk(tw);
                }
                for (const prop of node.properties) {
                    if (
                        prop.has_side_effects(compressor) ||
                        prop.may_throw(compressor)
                    ) {
                        prop.walk(tw);
                    }
                }
            }
            map_add(initializations, node_def.id, node);
            return true; // don't go in nested scopes
        }
        if (AST_SymbolFunarg.hasInstance(node) && scope === self) {
            map_add(var_defs_by_id, node.definition().id, node);
        }
        if (AST_Definitions.hasInstance(node) && scope === self) {
            const in_export = AST_Export.hasInstance(tw.parent());
            node.definitions.forEach(function(def) {
                if (AST_SymbolVar.hasInstance(def.name)) {
                    map_add(var_defs_by_id, def.name.definition().id, def);
                }
                if (in_export || !drop_vars) {
                    walk(def.name, node => {
                        if (AST_SymbolDeclaration.hasInstance(node)) {
                            const def = node.definition();
                            if (
                                (in_export || def.global)
                                && !in_use_ids.has(def.id)
                            ) {
                                in_use_ids.set(def.id, def);
                            }
                        }
                    });
                }
                if (def.value) {
                    if (AST_Destructuring.hasInstance(def.name)) {
                        def.walk(tw);
                    } else {
                        var node_def = def.name.definition();
                        map_add(initializations, node_def.id, def.value);
                        if (!node_def.chained && def.name.fixed_value() === def.value) {
                            fixed_ids.set(node_def.id, def);
                        }
                    }
                    if (def.value.has_side_effects(compressor)) {
                        def.value.walk(tw);
                    }
                }
            });
            return true;
        }
        return scan_ref_scoped(node, descend);
    });
    self.walk(tw);
    // pass 2: for every used symbol we need to walk its
    // initialization code to figure out if it uses other
    // symbols (that may not be in_use).
    tw = new TreeWalker(scan_ref_scoped);
    in_use_ids.forEach(function (def) {
        var init = initializations.get(def.id);
        if (init) init.forEach(function(init) {
            init.walk(tw);
        });
    });
    // pass 3: we should drop declarations not in_use
    var tt = new TreeTransformer(
        function before(node, descend, in_list) {
            var parent = tt.parent();
            if (drop_vars) {
                const sym = assign_as_unused(node);
                if (AST_SymbolRef.hasInstance(sym)) {
                    var def = sym.definition();
                    var in_use = in_use_ids.has(def.id);
                    if (AST_Assign.hasInstance(node)) {
                        if (!in_use || fixed_ids.has(def.id) && fixed_ids.get(def.id) !== node) {
                            return maintain_this_binding(parent, node, node.right.transform(tt));
                        }
                    } else if (!in_use) return in_list ? MAP.skip : make_node(AST_Number, node, {
                        value: 0
                    });
                }
            }
            if (scope !== self) return;
            var def;
            if (node.name
                && (AST_ClassExpression.hasInstance(node)
                    && !keep_name(compressor.option("keep_classnames"), (def = node.name.definition()).name)
                || AST_Function.hasInstance(node)
                    && !keep_name(compressor.option("keep_fnames"), (def = node.name.definition()).name))) {
                // any declarations with same name will overshadow
                // name of this anonymous function and can therefore
                // never be used anywhere
                if (!in_use_ids.has(def.id) || def.orig.length > 1) node.name = null;
            }
            if (AST_Lambda.hasInstance(node) && !AST_Accessor.hasInstance(node)) {
                var trim = !compressor.option("keep_fargs");
                for (var a = node.argnames, i = a.length; --i >= 0;) {
                    var sym = a[i];
                    if (AST_Expansion.hasInstance(sym)) {
                        sym = sym.expression;
                    }
                    if (AST_DefaultAssign.hasInstance(sym)) {
                        sym = sym.left;
                    }
                    // Do not drop destructuring arguments.
                    // They constitute a type assertion, so dropping
                    // them would stop that TypeError which would happen
                    // if someone called it with an incorrectly formatted
                    // parameter.
                    if (!AST_Destructuring.hasInstance(sym) && !in_use_ids.has(sym.definition().id)) {
                        set_flag(sym, UNUSED);
                        if (trim) {
                            a.pop();
                        }
                    } else {
                        trim = false;
                    }
                }
            }
            if ((AST_Defun.hasInstance(node) || AST_DefClass.hasInstance(node)) && node !== self) {
                const def = node.name.definition();
                let keep = def.global && !drop_funcs || in_use_ids.has(def.id);
                if (!keep) {
                    def.eliminated++;
                    if (AST_DefClass.hasInstance(node)) {
                        // Classes might have extends with side effects
                        const side_effects = node.drop_side_effect_free(compressor);
                        if (side_effects) {
                            return make_node(AST_SimpleStatement, node, {
                                body: side_effects
                            });
                        }
                    }
                    return in_list ? MAP.skip : make_node(AST_EmptyStatement, node);
                }
            }
            if (AST_Definitions.hasInstance(node) && !(AST_ForIn.hasInstance(parent) && parent.init === node)) {
                var drop_block = !AST_Toplevel.hasInstance(parent) && !AST_Var.hasInstance(node);
                // place uninitialized names at the start
                var body = [], head = [], tail = [];
                // for unused names whose initialization has
                // side effects, we can cascade the init. code
                // into the next one, or next statement.
                var side_effects = [];
                node.definitions.forEach(function(def) {
                    if (def.value) def.value = def.value.transform(tt);
                    var is_destructure = AST_Destructuring.hasInstance(def.name);
                    var sym = is_destructure
                        ? new SymbolDef(null, { name: "<destructure>" }) /* fake SymbolDef */
                        : def.name.definition();
                    if (drop_block && sym.global) return tail.push(def);
                    if (!(drop_vars || drop_block)
                        || is_destructure
                            && (def.name.names.length
                                || def.name.is_array
                                || compressor.option("pure_getters") != true)
                        || in_use_ids.has(sym.id)
                    ) {
                        if (def.value && fixed_ids.has(sym.id) && fixed_ids.get(sym.id) !== def) {
                            def.value = def.value.drop_side_effect_free(compressor);
                        }
                        if (AST_SymbolVar.hasInstance(def.name)) {
                            var var_defs = var_defs_by_id.get(sym.id);
                            if (var_defs.length > 1 && (!def.value || sym.orig.indexOf(def.name) > sym.eliminated)) {
                                if (def.value) {
                                    var ref = make_node(AST_SymbolRef, def.name, def.name);
                                    sym.references.push(ref);
                                    var assign = make_node(AST_Assign, def, {
                                        operator: "=",
                                        logical: false,
                                        left: ref,
                                        right: def.value
                                    });
                                    if (fixed_ids.get(sym.id) === def) {
                                        fixed_ids.set(sym.id, assign);
                                    }
                                    side_effects.push(assign.transform(tt));
                                }
                                remove(var_defs, def);
                                sym.eliminated++;
                                return;
                            }
                        }
                        if (def.value) {
                            if (side_effects.length > 0) {
                                if (tail.length > 0) {
                                    side_effects.push(def.value);
                                    def.value = make_sequence(def.value, side_effects);
                                } else {
                                    body.push(make_node(AST_SimpleStatement, node, {
                                        body: make_sequence(node, side_effects)
                                    }));
                                }
                                side_effects = [];
                            }
                            tail.push(def);
                        } else {
                            head.push(def);
                        }
                    } else if (AST_SymbolCatch.hasInstance(sym.orig[0])) {
                        var value = def.value && def.value.drop_side_effect_free(compressor);
                        if (value) side_effects.push(value);
                        def.value = null;
                        head.push(def);
                    } else {
                        var value = def.value && def.value.drop_side_effect_free(compressor);
                        if (value) {
                            side_effects.push(value);
                        }
                        sym.eliminated++;
                    }
                });
                if (head.length > 0 || tail.length > 0) {
                    node.definitions = head.concat(tail);
                    body.push(node);
                }
                if (side_effects.length > 0) {
                    body.push(make_node(AST_SimpleStatement, node, {
                        body: make_sequence(node, side_effects)
                    }));
                }
                switch (body.length) {
                  case 0:
                    return in_list ? MAP.skip : make_node(AST_EmptyStatement, node);
                  case 1:
                    return body[0];
                  default:
                    return in_list ? MAP.splice(body) : make_node(AST_BlockStatement, node, {
                        body: body
                    });
                }
            }
            // certain combination of unused name + side effect leads to:
            //    https://github.com/mishoo/UglifyJS2/issues/44
            //    https://github.com/mishoo/UglifyJS2/issues/1830
            //    https://github.com/mishoo/UglifyJS2/issues/1838
            // that's an invalid AST.
            // We fix it at this stage by moving the `var` outside the `for`.
            if (AST_For.hasInstance(node)) {
                descend(node, this);
                var block;
                if (AST_BlockStatement.hasInstance(node.init)) {
                    block = node.init;
                    node.init = block.body.pop();
                    block.body.push(node);
                }
                if (AST_SimpleStatement.hasInstance(node.init)) {
                    node.init = node.init.body;
                } else if (is_empty(node.init)) {
                    node.init = null;
                }
                return !block ? node : in_list ? MAP.splice(block.body) : block;
            }
            if (AST_LabeledStatement.hasInstance(node)
                && AST_For.hasInstance(node.body)
            ) {
                descend(node, this);
                if (AST_BlockStatement.hasInstance(node.body)) {
                    var block = node.body;
                    node.body = block.body.pop();
                    block.body.push(node);
                    return in_list ? MAP.splice(block.body) : block;
                }
                return node;
            }
            if (AST_BlockStatement.hasInstance(node)) {
                descend(node, this);
                if (in_list && node.body.every(can_be_evicted_from_block)) {
                    return MAP.splice(node.body);
                }
                return node;
            }
            if (AST_Scope.hasInstance(node)) {
                const save_scope = scope;
                scope = node;
                descend(node, this);
                scope = save_scope;
                return node;
            }
        }
    );

    self.transform(tt);

    function scan_ref_scoped(node, descend) {
        var node_def;
        const sym = assign_as_unused(node);
        if (AST_SymbolRef.hasInstance(sym)
            && !is_ref_of(node.left, AST_SymbolBlockDeclaration)
            && self.variables.get(sym.name) === (node_def = sym.definition())
        ) {
            if (AST_Assign.hasInstance(node)) {
                node.right.walk(tw);
                if (!node_def.chained && node.left.fixed_value() === node.right) {
                    fixed_ids.set(node_def.id, node);
                }
            }
            return true;
        }
        if (AST_SymbolRef.hasInstance(node)) {
            node_def = node.definition();
            if (!in_use_ids.has(node_def.id)) {
                in_use_ids.set(node_def.id, node_def);
                if (AST_SymbolCatch.hasInstance(node_def.orig[0])) {
                    const redef = node_def.scope.is_block_scope()
                        && node_def.scope.get_defun_scope().variables.get(node_def.name);
                    if (redef) in_use_ids.set(redef.id, redef);
                }
            }
            return true;
        }
        if (AST_Scope.hasInstance(node)) {
            var save_scope = scope;
            scope = node;
            descend();
            scope = save_scope;
            return true;
        }
    }
});

AST_Scope.DEFMETHOD("hoist_declarations", function(compressor) {
    var self = this;
    if (compressor.has_directive("use asm")) return self;
    // Hoisting makes no sense in an arrow func
    if (!Array.isArray(self.body)) return self;

    var hoist_funs = compressor.option("hoist_funs");
    var hoist_vars = compressor.option("hoist_vars");

    if (hoist_funs || hoist_vars) {
        var dirs = [];
        var hoisted = [];
        var vars = new Map(), vars_found = 0, var_decl = 0;
        // let's count var_decl first, we seem to waste a lot of
        // space if we hoist `var` when there's only one.
        walk(self, node => {
            if (AST_Scope.hasInstance(node) && node !== self)
                return true;
            if (AST_Var.hasInstance(node)) {
                ++var_decl;
                return true;
            }
        });
        hoist_vars = hoist_vars && var_decl > 1;
        var tt = new TreeTransformer(
            function before(node) {
                if (node !== self) {
                    if (AST_Directive.hasInstance(node)) {
                        dirs.push(node);
                        return make_node(AST_EmptyStatement, node);
                    }
                    if (hoist_funs && AST_Defun.hasInstance(node)
                        && !AST_Export.hasInstance(tt.parent())
                        && tt.parent() === self) {
                        hoisted.push(node);
                        return make_node(AST_EmptyStatement, node);
                    }
                    if (
                        hoist_vars
                        && AST_Var.hasInstance(node)
                        && !node.definitions.some(def => AST_Destructuring.hasInstance(def.name))
                    ) {
                        node.definitions.forEach(function(def) {
                            vars.set(def.name.name, def);
                            ++vars_found;
                        });
                        var seq = node.to_assignments(compressor);
                        var p = tt.parent();
                        if (AST_ForIn.hasInstance(p) && p.init === node) {
                            if (seq == null) {
                                var def = node.definitions[0].name;
                                return make_node(AST_SymbolRef, def, def);
                            }
                            return seq;
                        }
                        if (AST_For.hasInstance(p) && p.init === node) {
                            return seq;
                        }
                        if (!seq) return make_node(AST_EmptyStatement, node);
                        return make_node(AST_SimpleStatement, node, {
                            body: seq
                        });
                    }
                    if (AST_Scope.hasInstance(node))
                        return node; // to avoid descending in nested scopes
                }
            }
        );
        self = self.transform(tt);
        if (vars_found > 0) {
            // collect only vars which don't show up in self's arguments list
            var defs = [];
            const is_lambda = AST_Lambda.hasInstance(self);
            const args_as_names = is_lambda ? self.args_as_names() : null;
            vars.forEach((def, name) => {
                if (is_lambda && args_as_names.some((x) => x.name === def.name.name)) {
                    vars.delete(name);
                } else {
                    def = def.clone();
                    def.value = null;
                    defs.push(def);
                    vars.set(name, def);
                }
            });
            if (defs.length > 0) {
                // try to merge in assignments
                for (var i = 0; i < self.body.length;) {
                    if (AST_SimpleStatement.hasInstance(self.body[i])) {
                        var expr = self.body[i].body, sym, assign;
                        if (AST_Assign.hasInstance(expr)
                            && expr.operator == "="
                            && AST_Symbol.hasInstance(sym = expr.left)
                            && vars.has(sym.name)
                        ) {
                            var def = vars.get(sym.name);
                            if (def.value) break;
                            def.value = expr.right;
                            remove(defs, def);
                            defs.push(def);
                            self.body.splice(i, 1);
                            continue;
                        }
                        if (AST_Sequence.hasInstance(expr)
                            && AST_Assign.hasInstance(assign = expr.expressions[0])
                            && assign.operator == "="
                            && AST_Symbol.hasInstance(sym = assign.left)
                            && vars.has(sym.name)
                        ) {
                            var def = vars.get(sym.name);
                            if (def.value) break;
                            def.value = assign.right;
                            remove(defs, def);
                            defs.push(def);
                            self.body[i].body = make_sequence(expr, expr.expressions.slice(1));
                            continue;
                        }
                    }
                    if (AST_EmptyStatement.hasInstance(self.body[i])) {
                        self.body.splice(i, 1);
                        continue;
                    }
                    if (AST_BlockStatement.hasInstance(self.body[i])) {
                        self.body.splice(i, 1, ...self.body[i].body);
                        continue;
                    }
                    break;
                }
                defs = make_node(AST_Var, self, {
                    definitions: defs
                });
                hoisted.push(defs);
            }
        }
        self.body = dirs.concat(hoisted, self.body);
    }
    return self;
});

AST_Scope.DEFMETHOD("hoist_properties", function(compressor) {
    var self = this;
    if (!compressor.option("hoist_props") || compressor.has_directive("use asm")) return self;
    var top_retain = AST_Toplevel.hasInstance(self) && compressor.top_retain || return_false;
    var defs_by_id = new Map();
    var hoister = new TreeTransformer(function(node, descend) {
        if (AST_Definitions.hasInstance(node)
            && AST_Export.hasInstance(hoister.parent())) return node;
        if (AST_VarDef.hasInstance(node)) {
            const sym = node.name;
            let def;
            let value;
            if (sym.scope === self
                && (def = sym.definition()).escaped != 1
                && !def.assignments
                && !def.direct_access
                && !def.single_use
                && !compressor.exposed(def)
                && !top_retain(def)
                && (value = sym.fixed_value()) === node.value
                && AST_Object.hasInstance(value)
                && !value.properties.some(prop =>
                    AST_Expansion.hasInstance(prop) || prop.computed_key()
                )
            ) {
                descend(node, this);
                const defs = new Map();
                const assignments = [];
                value.properties.forEach(({ key, value }) => {
                    const scope = find_scope(hoister);
                    const symbol = self.create_symbol(sym.CTOR, {
                        source: sym,
                        scope,
                        conflict_scopes: new Set([
                            scope,
                            ...sym.definition().references.map(ref => ref.scope)
                        ]),
                        tentative_name: sym.name + "_" + key
                    });

                    defs.set(String(key), symbol.definition());

                    assignments.push(make_node(AST_VarDef, node, {
                        name: symbol,
                        value
                    }));
                });
                defs_by_id.set(def.id, defs);
                return MAP.splice(assignments);
            }
        } else if (AST_PropAccess.hasInstance(node)
            && AST_SymbolRef.hasInstance(node.expression)
        ) {
            const defs = defs_by_id.get(node.expression.definition().id);
            if (defs) {
                const def = defs.get(String(get_simple_key(node.property)));
                const sym = make_node(AST_SymbolRef, node, {
                    name: def.name,
                    scope: node.expression.scope,
                    thedef: def
                });
                sym.reference({});
                return sym;
            }
        }
    });
    return self.transform(hoister);
});

def_optimize(AST_SimpleStatement, function(self, compressor) {
    if (compressor.option("side_effects")) {
        var body = self.body;
        var node = body.drop_side_effect_free(compressor, true);
        if (!node) {
            return make_node(AST_EmptyStatement, self);
        }
        if (node !== body) {
            return make_node(AST_SimpleStatement, self, { body: node });
        }
    }
    return self;
});

def_optimize(AST_While, function(self, compressor) {
    return compressor.option("loops") ? make_node(AST_For, self, self).optimize(compressor) : self;
});

def_optimize(AST_Do, function(self, compressor) {
    if (!compressor.option("loops")) return self;
    var cond = self.condition.tail_node().evaluate(compressor);
    if (!AST_Node.hasInstance(cond)) {
        if (cond) return make_node(AST_For, self, {
            body: make_node(AST_BlockStatement, self.body, {
                body: [
                    self.body,
                    make_node(AST_SimpleStatement, self.condition, {
                        body: self.condition
                    })
                ]
            })
        }).optimize(compressor);
        if (!has_break_or_continue(self, compressor.parent())) {
            return make_node(AST_BlockStatement, self.body, {
                body: [
                    self.body,
                    make_node(AST_SimpleStatement, self.condition, {
                        body: self.condition
                    })
                ]
            }).optimize(compressor);
        }
    }
    return self;
});

function if_break_in_loop(self, compressor) {
    var first = AST_BlockStatement.hasInstance(self.body) ? self.body.body[0] : self.body;
    if (compressor.option("dead_code") && is_break(first)) {
        var body = [];
        if (AST_Statement.hasInstance(self.init)) {
            body.push(self.init);
        } else if (self.init) {
            body.push(make_node(AST_SimpleStatement, self.init, {
                body: self.init
            }));
        }
        if (self.condition) {
            body.push(make_node(AST_SimpleStatement, self.condition, {
                body: self.condition
            }));
        }
        trim_unreachable_code(compressor, self.body, body);
        return make_node(AST_BlockStatement, self, {
            body: body
        });
    }
    if (AST_If.hasInstance(first)) {
        if (is_break(first.body)) {
            if (self.condition) {
                self.condition = make_node(AST_Binary, self.condition, {
                    left: self.condition,
                    operator: "&&",
                    right: first.condition.negate(compressor),
                });
            } else {
                self.condition = first.condition.negate(compressor);
            }
            drop_it(first.alternative);
        } else if (is_break(first.alternative)) {
            if (self.condition) {
                self.condition = make_node(AST_Binary, self.condition, {
                    left: self.condition,
                    operator: "&&",
                    right: first.condition,
                });
            } else {
                self.condition = first.condition;
            }
            drop_it(first.body);
        }
    }
    return self;

    function is_break(node) {
        return AST_Break.hasInstance(node)
            && compressor.loopcontrol_target(node) === compressor.self();
    }

    function drop_it(rest) {
        rest = as_statement_array(rest);
        if (AST_BlockStatement.hasInstance(self.body)) {
            self.body = self.body.clone();
            self.body.body = rest.concat(self.body.body.slice(1));
            self.body = self.body.transform(compressor);
        } else {
            self.body = make_node(AST_BlockStatement, self.body, {
                body: rest
            }).transform(compressor);
        }
        self = if_break_in_loop(self, compressor);
    }
}

def_optimize(AST_For, function(self, compressor) {
    if (!compressor.option("loops")) return self;
    if (compressor.option("side_effects") && self.init) {
        self.init = self.init.drop_side_effect_free(compressor);
    }
    if (self.condition) {
        var cond = self.condition.evaluate(compressor);
        if (!AST_Node.hasInstance(cond)) {
            if (cond) self.condition = null;
            else if (!compressor.option("dead_code")) {
                var orig = self.condition;
                self.condition = make_node_from_constant(cond, self.condition);
                self.condition = best_of_expression(self.condition.transform(compressor), orig);
            }
        }
        if (compressor.option("dead_code")) {
            if (AST_Node.hasInstance(cond)) cond = self.condition.tail_node().evaluate(compressor);
            if (!cond) {
                var body = [];
                trim_unreachable_code(compressor, self.body, body);
                if (AST_Statement.hasInstance(self.init)) {
                    body.push(self.init);
                } else if (self.init) {
                    body.push(make_node(AST_SimpleStatement, self.init, {
                        body: self.init
                    }));
                }
                body.push(make_node(AST_SimpleStatement, self.condition, {
                    body: self.condition
                }));
                return make_node(AST_BlockStatement, self, { body: body }).optimize(compressor);
            }
        }
    }
    return if_break_in_loop(self, compressor);
});

def_optimize(AST_If, function(self, compressor) {
    if (is_empty(self.alternative)) self.alternative = null;

    if (!compressor.option("conditionals")) return self;
    // if condition can be statically determined, drop
    // one of the blocks.  note, statically determined implies
    // “has no side effects”; also it doesn't work for cases like
    // `x && true`, though it probably should.
    var cond = self.condition.evaluate(compressor);
    if (!compressor.option("dead_code") && !AST_Node.hasInstance(cond)) {
        var orig = self.condition;
        self.condition = make_node_from_constant(cond, orig);
        self.condition = best_of_expression(self.condition.transform(compressor), orig);
    }
    if (compressor.option("dead_code")) {
        if (AST_Node.hasInstance(cond)) cond = self.condition.tail_node().evaluate(compressor);
        if (!cond) {
            var body = [];
            trim_unreachable_code(compressor, self.body, body);
            body.push(make_node(AST_SimpleStatement, self.condition, {
                body: self.condition
            }));
            if (self.alternative) body.push(self.alternative);
            return make_node(AST_BlockStatement, self, { body: body }).optimize(compressor);
        } else if (!AST_Node.hasInstance(cond)) {
            var body = [];
            body.push(make_node(AST_SimpleStatement, self.condition, {
                body: self.condition
            }));
            body.push(self.body);
            if (self.alternative) {
                trim_unreachable_code(compressor, self.alternative, body);
            }
            return make_node(AST_BlockStatement, self, { body: body }).optimize(compressor);
        }
    }
    var negated = self.condition.negate(compressor);
    var self_condition_length = self.condition.size();
    var negated_length = negated.size();
    var negated_is_best = negated_length < self_condition_length;
    if (self.alternative && negated_is_best) {
        negated_is_best = false; // because we already do the switch here.
        // no need to swap values of self_condition_length and negated_length
        // here because they are only used in an equality comparison later on.
        self.condition = negated;
        var tmp = self.body;
        self.body = self.alternative || make_node(AST_EmptyStatement, self);
        self.alternative = tmp;
    }
    if (is_empty(self.body) && is_empty(self.alternative)) {
        return make_node(AST_SimpleStatement, self.condition, {
            body: self.condition.clone()
        }).optimize(compressor);
    }
    if (AST_SimpleStatement.hasInstance(self.body)
        && AST_SimpleStatement.hasInstance(self.alternative)) {
        return make_node(AST_SimpleStatement, self, {
            body: make_node(AST_Conditional, self, {
                condition   : self.condition,
                consequent  : self.body.body,
                alternative : self.alternative.body
            })
        }).optimize(compressor);
    }
    if (is_empty(self.alternative) && AST_SimpleStatement.hasInstance(self.body)) {
        if (self_condition_length === negated_length && !negated_is_best
            && AST_Binary.hasInstance(self.condition) && self.condition.operator == "||") {
            // although the code length of self.condition and negated are the same,
            // negated does not require additional surrounding parentheses.
            // see https://github.com/mishoo/UglifyJS2/issues/979
            negated_is_best = true;
        }
        if (negated_is_best) return make_node(AST_SimpleStatement, self, {
            body: make_node(AST_Binary, self, {
                operator : "||",
                left     : negated,
                right    : self.body.body
            })
        }).optimize(compressor);
        return make_node(AST_SimpleStatement, self, {
            body: make_node(AST_Binary, self, {
                operator : "&&",
                left     : self.condition,
                right    : self.body.body
            })
        }).optimize(compressor);
    }
    if (AST_EmptyStatement.hasInstance(self.body)
        && AST_SimpleStatement.hasInstance(self.alternative)) {
        return make_node(AST_SimpleStatement, self, {
            body: make_node(AST_Binary, self, {
                operator : "||",
                left     : self.condition,
                right    : self.alternative.body
            })
        }).optimize(compressor);
    }
    if (AST_Exit.hasInstance(self.body)
        && AST_Exit.hasInstance(self.alternative)
        && self.body.TYPE == self.alternative.TYPE) {
        return make_node(self.body.CTOR, self, {
            value: make_node(AST_Conditional, self, {
                condition   : self.condition,
                consequent  : self.body.value || make_node(AST_Undefined, self.body),
                alternative : self.alternative.value || make_node(AST_Undefined, self.alternative)
            }).transform(compressor)
        }).optimize(compressor);
    }
    if (AST_If.hasInstance(self.body)
        && !self.body.alternative
        && !self.alternative) {
        self = make_node(AST_If, self, {
            condition: make_node(AST_Binary, self.condition, {
                operator: "&&",
                left: self.condition,
                right: self.body.condition
            }),
            body: self.body.body,
            alternative: null
        });
    }
    if (aborts(self.body)) {
        if (self.alternative) {
            var alt = self.alternative;
            self.alternative = null;
            return make_node(AST_BlockStatement, self, {
                body: [ self, alt ]
            }).optimize(compressor);
        }
    }
    if (aborts(self.alternative)) {
        var body = self.body;
        self.body = self.alternative;
        self.condition = negated_is_best ? negated : self.condition.negate(compressor);
        self.alternative = null;
        return make_node(AST_BlockStatement, self, {
            body: [ self, body ]
        }).optimize(compressor);
    }
    return self;
});

def_optimize(AST_Switch, function(self, compressor) {
    if (!compressor.option("switches")) return self;
    var branch;
    var value = self.expression.evaluate(compressor);
    if (!AST_Node.hasInstance(value)) {
        var orig = self.expression;
        self.expression = make_node_from_constant(value, orig);
        self.expression = best_of_expression(self.expression.transform(compressor), orig);
    }
    if (!compressor.option("dead_code")) return self;
    if (AST_Node.hasInstance(value)) {
        value = self.expression.tail_node().evaluate(compressor);
    }
    var decl = [];
    var body = [];
    var default_branch;
    var exact_match;
    for (var i = 0, len = self.body.length; i < len && !exact_match; i++) {
        branch = self.body[i];
        if (AST_Default.hasInstance(branch)) {
            if (!default_branch) {
                default_branch = branch;
            } else {
                eliminate_branch(branch, body[body.length - 1]);
            }
        } else if (!AST_Node.hasInstance(value)) {
            var exp = branch.expression.evaluate(compressor);
            if (!AST_Node.hasInstance(exp) && exp !== value) {
                eliminate_branch(branch, body[body.length - 1]);
                continue;
            }
            if (AST_Node.hasInstance(exp)) exp = branch.expression.tail_node().evaluate(compressor);
            if (exp === value) {
                exact_match = branch;
                if (default_branch) {
                    var default_index = body.indexOf(default_branch);
                    body.splice(default_index, 1);
                    eliminate_branch(default_branch, body[default_index - 1]);
                    default_branch = null;
                }
            }
        }
        body.push(branch);
    }
    while (i < len) eliminate_branch(self.body[i++], body[body.length - 1]);
    self.body = body;

    for (let i = 0; i < body.length; i++) {
        let branch = body[i];
        if (branch.body.length === 0) continue;
        if (!aborts(branch)) continue;

        for (let j = i + 1; j < body.length; i++, j++) {
            let next = body[j];
            if (next.body.length === 0) continue;
            if (
                branches_equivalent(next, branch, false)
                || (j === body.length - 1 && branches_equivalent(next, branch, true))
            ) {
                branch.body = [];
                branch = next;
                continue;
            }
            break;
        }
    }

    let default_or_exact = default_branch || exact_match;
    default_branch = null;
    exact_match = null;

    // Prune any empty branches at the end of the switch statement.
    {
        let i = body.length - 1;
        for (; i >= 0; i--) {
            let bbody = body[i].body;
            if (is_break(bbody[bbody.length - 1], compressor)) bbody.pop();
            if (!is_inert_body(body[i])) break;
        }
        // i now points to the index of a branch that contains a body. By incrementing, it's
        // pointing to the first branch that's empty.
        i++;
        if (!default_or_exact || body.indexOf(default_or_exact) >= i) {
            // The default behavior is to do nothing. We can take advantage of that to
            // remove all case expressions that are side-effect free that also do
            // nothing, since they'll default to doing nothing. But we can't remove any
            // case expressions before one that would side-effect, since they may cause
            // the side-effect to be skipped.
            for (let j = body.length - 1; j >= i; j--) {
                let branch = body[j];
                if (branch === default_or_exact) {
                    default_or_exact = null;
                    body.pop();
                } else if (!branch.expression.has_side_effects(compressor)) {
                    body.pop();
                } else {
                    break;
                }
            }
        }
    }


    // Prune side-effect free branches that fall into default.
    if (default_or_exact) {
        let default_index = body.indexOf(default_or_exact);
        let default_body_index = default_index;
        for (; default_body_index < body.length - 1; default_body_index++) {
            if (!is_inert_body(body[default_body_index])) break;
        }
        let side_effect_index = body.length - 1;
        for (; side_effect_index >= 0; side_effect_index--) {
            let branch = body[side_effect_index];
            if (branch === default_or_exact) continue;
            if (branch.expression.has_side_effects(compressor)) break;
        }
        // If the default behavior comes after any side-effect case expressions,
        // then we can fold all side-effect free cases into the default branch.
        // If the side-effect case is after the default, then any side-effect
        // free cases could prevent the side-effect from occurring.
        if (default_body_index > side_effect_index) {
            let prev_body_index = default_index - 1;
            for (; prev_body_index >= 0; prev_body_index--) {
                if (!is_inert_body(body[prev_body_index])) break;
            }
            let before = Math.max(side_effect_index, prev_body_index) + 1;
            let after = default_index;
            if (side_effect_index > default_index) {
                // If the default falls into the same body as a side-effect
                // case, then we need preserve that case and only prune the
                // cases after it.
                after = side_effect_index;
                body[side_effect_index].body = body[default_body_index].body;
            } else {
                // The default will be the last branch.
                default_or_exact.body = body[default_body_index].body;
            }

            // Prune everything after the default (or last side-effect case)
            // until the next case with a body.
            body.splice(after + 1, default_body_index - after);
            // Prune everything before the default that falls into it.
            body.splice(before, default_index - before);
        }
    }

    // See if we can remove the switch entirely if all cases (the default) fall into the same case body.
    DEFAULT: if (default_or_exact) {
        let i = body.findIndex(branch => !is_inert_body(branch));
        let caseBody;
        // `i` is equal to one of the following:
        // - `-1`, there is no body in the switch statement.
        // - `body.length - 1`, all cases fall into the same body.
        // - anything else, there are multiple bodies in the switch.
        if (i === body.length - 1) {
            // All cases fall into the case body.
            let branch = body[i];
            if (has_nested_break(self)) break DEFAULT;

            // This is the last case body, and we've already pruned any breaks, so it's
            // safe to hoist.
            caseBody = make_node(AST_BlockStatement, branch, {
                body: branch.body
            });
            branch.body = [];
        } else if (i !== -1) {
            // If there are multiple bodies, then we cannot optimize anything.
            break DEFAULT;
        }

        let sideEffect = body.find(branch => {
            return (
                branch !== default_or_exact
                && branch.expression.has_side_effects(compressor)
            );
        });
        // If no cases cause a side-effect, we can eliminate the switch entirely.
        if (!sideEffect) {
            return make_node(AST_BlockStatement, self, {
                body: decl.concat(
                    statement(self.expression),
                    default_or_exact.expression ? statement(default_or_exact.expression) : [],
                    caseBody || []
                )
            }).optimize(compressor);
        }

        // If we're this far, either there was no body or all cases fell into the same body.
        // If there was no body, then we don't need a default branch (because the default is
        // do nothing). If there was a body, we'll extract it to after the switch, so the
        // switch's new default is to do nothing and we can still prune it.
        const default_index = body.indexOf(default_or_exact);
        body.splice(default_index, 1);
        default_or_exact = null;

        if (caseBody) {
            // Recurse into switch statement one more time so that we can append the case body
            // outside of the switch. This recursion will only happen once since we've pruned
            // the default case.
            return make_node(AST_BlockStatement, self, {
                body: decl.concat(self, caseBody)
            }).optimize(compressor);
        }
        // If we fall here, there is a default branch somewhere, there are no case bodies,
        // and there's a side-effect somewhere. Just let the below paths take care of it.
    }

    if (body.length > 0) {
        body[0].body = decl.concat(body[0].body);
    }

    if (body.length == 0) {
        return make_node(AST_BlockStatement, self, {
            body: decl.concat(statement(self.expression))
        }).optimize(compressor);
    }
    if (body.length == 1 && !has_nested_break(self)) {
        // This is the last case body, and we've already pruned any breaks, so it's
        // safe to hoist.
        let branch = body[0];
        return make_node(AST_If, self, {
            condition: make_node(AST_Binary, self, {
                operator: "===",
                left: self.expression,
                right: branch.expression,
            }),
            body: make_node(AST_BlockStatement, branch, {
                body: branch.body
            }),
            alternative: null
        }).optimize(compressor);
    }
    if (body.length === 2 && default_or_exact && !has_nested_break(self)) {
        let branch = body[0] === default_or_exact ? body[1] : body[0];
        let exact_exp = default_or_exact.expression && statement(default_or_exact.expression);
        if (aborts(body[0])) {
            // Only the first branch body could have a break (at the last statement)
            let first = body[0];
            if (is_break(first.body[first.body.length - 1], compressor)) {
                first.body.pop();
            }
            return make_node(AST_If, self, {
                condition: make_node(AST_Binary, self, {
                    operator: "===",
                    left: self.expression,
                    right: branch.expression,
                }),
                body: make_node(AST_BlockStatement, branch, {
                    body: branch.body
                }),
                alternative: make_node(AST_BlockStatement, default_or_exact, {
                    body: [].concat(
                        exact_exp || [],
                        default_or_exact.body
                    )
                })
            }).optimize(compressor);
        }
        let operator = "===";
        let consequent = make_node(AST_BlockStatement, branch, {
            body: branch.body,
        });
        let always = make_node(AST_BlockStatement, default_or_exact, {
            body: [].concat(
                exact_exp || [],
                default_or_exact.body
            )
        });
        if (body[0] === default_or_exact) {
            operator = "!==";
            let tmp = always;
            always = consequent;
            consequent = tmp;
        }
        return make_node(AST_BlockStatement, self, {
            body: [
                make_node(AST_If, self, {
                    condition: make_node(AST_Binary, self, {
                        operator: operator,
                        left: self.expression,
                        right: branch.expression,
                    }),
                    body: consequent,
                    alternative: null
                })
            ].concat(always)
        }).optimize(compressor);
    }
    return self;

    function eliminate_branch(branch, prev) {
        if (prev && !aborts(prev)) {
            prev.body = prev.body.concat(branch.body);
        } else {
            trim_unreachable_code(compressor, branch, decl);
        }
    }
    function branches_equivalent(branch, prev, insertBreak) {
        let bbody = branch.body;
        let pbody = prev.body;
        if (insertBreak) {
            bbody = bbody.concat(make_node(AST_Break));
        }
        if (bbody.length !== pbody.length) return false;
        let bblock = make_node(AST_BlockStatement, branch, { body: bbody });
        let pblock = make_node(AST_BlockStatement, prev, { body: pbody });
        return bblock.equivalent_to(pblock);
    }
    function statement(expression) {
        return make_node(AST_SimpleStatement, expression, {
            body: expression
        });
    }
    function has_nested_break(root) {
        let has_break = false;
        let tw = new TreeWalker(node => {
            if (has_break) return true;
            if (AST_Lambda.hasInstance(node)) return true;
            if (AST_SimpleStatement.hasInstance(node)) return true;
            if (!is_break(node, tw)) return;
            let parent = tw.parent();
            if (
                AST_SwitchBranch.hasInstance(parent)
                && parent.body[parent.body.length - 1] === node
            ) {
                return;
            }
            has_break = true;
        });
        root.walk(tw);
        return has_break;
    }
    function is_break(node, stack) {
        return AST_Break.hasInstance(node)
            && stack.loopcontrol_target(node) === self;
    }
    function is_inert_body(branch) {
        return !aborts(branch) && !make_node(AST_BlockStatement, branch, {
            body: branch.body
        }).has_side_effects(compressor);
    }
});

def_optimize(AST_Try, function(self, compressor) {
    tighten_body(self.body, compressor);
    if (self.bcatch && self.bfinally && self.bfinally.body.every(is_empty)) self.bfinally = null;
    if (compressor.option("dead_code") && self.body.every(is_empty)) {
        var body = [];
        if (self.bcatch) {
            trim_unreachable_code(compressor, self.bcatch, body);
        }
        if (self.bfinally) body.push(...self.bfinally.body);
        return make_node(AST_BlockStatement, self, {
            body: body
        }).optimize(compressor);
    }
    return self;
});

AST_Definitions.DEFMETHOD("remove_initializers", function() {
    var decls = [];
    this.definitions.forEach(function(def) {
        if (AST_SymbolDeclaration.hasInstance(def.name)) {
            def.value = null;
            decls.push(def);
        } else {
            walk(def.name, node => {
                if (AST_SymbolDeclaration.hasInstance(node)) {
                    decls.push(make_node(AST_VarDef, def, {
                        name: node,
                        value: null
                    }));
                }
            });
        }
    });
    this.definitions = decls;
});

AST_Definitions.DEFMETHOD("to_assignments", function(compressor) {
    var reduce_vars = compressor.option("reduce_vars");
    var assignments = [];

    for (const def of this.definitions) {
        if (def.value) {
            var name = make_node(AST_SymbolRef, def.name, def.name);
            assignments.push(make_node(AST_Assign, def, {
                operator : "=",
                logical: false,
                left     : name,
                right    : def.value
            }));
            if (reduce_vars) name.definition().fixed = false;
        } else if (def.value) {
            // Because it's a destructuring, do not turn into an assignment.
            var varDef = make_node(AST_VarDef, def, {
                name: def.name,
                value: def.value
            });
            var var_ = make_node(AST_Var, def, {
                definitions: [ varDef ]
            });
            assignments.push(var_);
        }
        const thedef = def.name.definition();
        thedef.eliminated++;
        thedef.replaced--;
    }

    if (assignments.length == 0) return null;
    return make_sequence(this, assignments);
});

def_optimize(AST_Definitions, function(self) {
    if (self.definitions.length == 0)
        return make_node(AST_EmptyStatement, self);
    return self;
});

def_optimize(AST_VarDef, function(self, compressor) {
    if (
        AST_SymbolLet.hasInstance(self.name)
        && self.value != null
        && is_undefined(self.value, compressor)
    ) {
        self.value = null;
    }
    return self;
});

def_optimize(AST_Import, function(self) {
    return self;
});

// TODO this only works with AST_Defun, shouldn't it work for other ways of defining functions?
function retain_top_func(fn, compressor) {
    return compressor.top_retain
        && AST_Defun.hasInstance(fn)
        && has_flag(fn, TOP)
        && fn.name
        && compressor.top_retain(fn.name);
}

def_optimize(AST_Call, function(self, compressor) {
    var exp = self.expression;
    var fn = exp;
    inline_array_like_spread(self.args);
    var simple_args = self.args.every((arg) =>
        !AST_Expansion.hasInstance(arg)
    );

    if (compressor.option("reduce_vars")
        && AST_SymbolRef.hasInstance(fn)
        && !has_annotation(self, _NOINLINE)
    ) {
        const fixed = fn.fixed_value();
        if (!retain_top_func(fixed, compressor)) {
            fn = fixed;
        }
    }

    if (self.optional && is_nullish(fn, compressor)) {
        return make_node(AST_Undefined, self);
    }

    var is_func = AST_Lambda.hasInstance(fn);

    if (is_func && fn.pinned()) return self;

    if (compressor.option("unused")
        && simple_args
        && is_func
        && !fn.uses_arguments) {
        var pos = 0, last = 0;
        for (var i = 0, len = self.args.length; i < len; i++) {
            if (AST_Expansion.hasInstance(fn.argnames[i])) {
                if (has_flag(fn.argnames[i].expression, UNUSED)) while (i < len) {
                    var node = self.args[i++].drop_side_effect_free(compressor);
                    if (node) {
                        self.args[pos++] = node;
                    }
                } else while (i < len) {
                    self.args[pos++] = self.args[i++];
                }
                last = pos;
                break;
            }
            var trim = i >= fn.argnames.length;
            if (trim || has_flag(fn.argnames[i], UNUSED)) {
                var node = self.args[i].drop_side_effect_free(compressor);
                if (node) {
                    self.args[pos++] = node;
                } else if (!trim) {
                    self.args[pos++] = make_node(AST_Number, self.args[i], {
                        value: 0
                    });
                    continue;
                }
            } else {
                self.args[pos++] = self.args[i];
            }
            last = pos;
        }
        self.args.length = last;
    }

    if (compressor.option("unsafe")) {
        if (AST_Dot.hasInstance(exp) && exp.start.value === "Array" && exp.property === "from" && self.args.length === 1) {
            const [argument] = self.args;
            if (AST_Array.hasInstance(argument)) {
                return make_node(AST_Array, argument, {
                    elements: argument.elements
                }).optimize(compressor);
            }
        }
        if (is_undeclared_ref(exp)) switch (exp.name) {
          case "Array":
            if (self.args.length != 1) {
                return make_node(AST_Array, self, {
                    elements: self.args
                }).optimize(compressor);
            } else if (AST_Number.hasInstance(self.args[0]) && self.args[0].value <= 11) {
                const elements = [];
                for (let i = 0; i < self.args[0].value; i++) elements.push(new AST_Hole);
                return new AST_Array({ elements });
            }
            break;
          case "Object":
            if (self.args.length == 0) {
                return make_node(AST_Object, self, {
                    properties: []
                });
            }
            break;
          case "String":
            if (self.args.length == 0) return make_node(AST_String, self, {
                value: ""
            });
            if (self.args.length <= 1) return make_node(AST_Binary, self, {
                left: self.args[0],
                operator: "+",
                right: make_node(AST_String, self, { value: "" })
            }).optimize(compressor);
            break;
          case "Number":
            if (self.args.length == 0) return make_node(AST_Number, self, {
                value: 0
            });
            if (self.args.length == 1 && compressor.option("unsafe_math")) {
                return make_node(AST_UnaryPrefix, self, {
                    expression: self.args[0],
                    operator: "+"
                }).optimize(compressor);
            }
            break;
          case "Symbol":
            if (self.args.length == 1 && AST_String.hasInstance(self.args[0]) && compressor.option("unsafe_symbols"))
                self.args.length = 0;
                break;
          case "Boolean":
            if (self.args.length == 0) return make_node(AST_False, self);
            if (self.args.length == 1) return make_node(AST_UnaryPrefix, self, {
                expression: make_node(AST_UnaryPrefix, self, {
                    expression: self.args[0],
                    operator: "!"
                }),
                operator: "!"
            }).optimize(compressor);
            break;
          case "RegExp":
            var params = [];
            if (self.args.length >= 1
                && self.args.length <= 2
                && self.args.every((arg) => {
                    var value = arg.evaluate(compressor);
                    params.push(value);
                    return arg !== value;
                })
            ) {
                let [ source, flags ] = params;
                source = regexp_source_fix(new RegExp(source).source);
                const rx = make_node(AST_RegExp, self, {
                    value: { source, flags }
                });
                if (rx._eval(compressor) !== rx) {
                    return rx;
                }
            }
            break;
        } else if (AST_Dot.hasInstance(exp)) switch(exp.property) {
          case "toString":
            if (self.args.length == 0 && !exp.expression.may_throw_on_access(compressor)) {
                return make_node(AST_Binary, self, {
                    left: make_node(AST_String, self, { value: "" }),
                    operator: "+",
                    right: exp.expression
                }).optimize(compressor);
            }
            break;
          case "join":
            if (AST_Array.hasInstance(exp.expression)) EXIT: {
                var separator;
                if (self.args.length > 0) {
                    separator = self.args[0].evaluate(compressor);
                    if (separator === self.args[0]) break EXIT; // not a constant
                }
                var elements = [];
                var consts = [];
                for (var i = 0, len = exp.expression.elements.length; i < len; i++) {
                    var el = exp.expression.elements[i];
                    if (AST_Expansion.hasInstance(el)) break EXIT;
                    var value = el.evaluate(compressor);
                    if (value !== el) {
                        consts.push(value);
                    } else {
                        if (consts.length > 0) {
                            elements.push(make_node(AST_String, self, {
                                value: consts.join(separator)
                            }));
                            consts.length = 0;
                        }
                        elements.push(el);
                    }
                }
                if (consts.length > 0) {
                    elements.push(make_node(AST_String, self, {
                        value: consts.join(separator)
                    }));
                }
                if (elements.length == 0) return make_node(AST_String, self, { value: "" });
                if (elements.length == 1) {
                    if (elements[0].is_string(compressor)) {
                        return elements[0];
                    }
                    return make_node(AST_Binary, elements[0], {
                        operator : "+",
                        left     : make_node(AST_String, self, { value: "" }),
                        right    : elements[0]
                    });
                }
                if (separator == "") {
                    var first;
                    if (elements[0].is_string(compressor)
                        || elements[1].is_string(compressor)) {
                        first = elements.shift();
                    } else {
                        first = make_node(AST_String, self, { value: "" });
                    }
                    return elements.reduce(function(prev, el) {
                        return make_node(AST_Binary, el, {
                            operator : "+",
                            left     : prev,
                            right    : el
                        });
                    }, first).optimize(compressor);
                }
                // need this awkward cloning to not affect original element
                // best_of will decide which one to get through.
                var node = self.clone();
                node.expression = node.expression.clone();
                node.expression.expression = node.expression.expression.clone();
                node.expression.expression.elements = elements;
                return best_of(compressor, self, node);
            }
            break;
          case "charAt":
            if (exp.expression.is_string(compressor)) {
                var arg = self.args[0];
                var index = arg ? arg.evaluate(compressor) : 0;
                if (index !== arg) {
                    return make_node(AST_Sub, exp, {
                        expression: exp.expression,
                        property: make_node_from_constant(index | 0, arg || exp)
                    }).optimize(compressor);
                }
            }
            break;
          case "apply":
            if (self.args.length == 2 && AST_Array.hasInstance(self.args[1])) {
                var args = self.args[1].elements.slice();
                args.unshift(self.args[0]);
                return make_node(AST_Call, self, {
                    expression: make_node(AST_Dot, exp, {
                        expression: exp.expression,
                        optional: false,
                        property: "call"
                    }),
                    args: args
                }).optimize(compressor);
            }
            break;
          case "call":
            var func = exp.expression;
            if (AST_SymbolRef.hasInstance(func)) {
                func = func.fixed_value();
            }
            if (AST_Lambda.hasInstance(func) && !func.contains_this()) {
                return (self.args.length ? make_sequence(this, [
                    self.args[0],
                    make_node(AST_Call, self, {
                        expression: exp.expression,
                        args: self.args.slice(1)
                    })
                ]) : make_node(AST_Call, self, {
                    expression: exp.expression,
                    args: []
                })).optimize(compressor);
            }
            break;
        }
    }

    if (compressor.option("unsafe_Function")
        && is_undeclared_ref(exp)
        && exp.name == "Function") {
        // new Function() => function(){}
        if (self.args.length == 0) return make_node(AST_Function, self, {
            argnames: [],
            body: []
        }).optimize(compressor);
        var nth_identifier = compressor.mangle_options && compressor.mangle_options.nth_identifier || base54;
        if (self.args.every((x) => AST_String.hasInstance(x))) {
            // quite a corner-case, but we can handle it:
            //   https://github.com/mishoo/UglifyJS2/issues/203
            // if the code argument is a constant, then we can minify it.
            try {
                var code = "n(function(" + self.args.slice(0, -1).map(function(arg) {
                    return arg.value;
                }).join(",") + "){" + self.args[self.args.length - 1].value + "})";
                var ast = parse(code);
                var mangle = { ie8: compressor.option("ie8"), nth_identifier: nth_identifier };
                ast.figure_out_scope(mangle);
                var comp = new Compressor(compressor.options, {
                    mangle_options: compressor.mangle_options
                });
                ast = ast.transform(comp);
                ast.figure_out_scope(mangle);
                ast.compute_char_frequency(mangle);
                ast.mangle_names(mangle);
                var fun;
                walk(ast, node => {
                    if (is_func_expr(node)) {
                        fun = node;
                        return walk_abort;
                    }
                });
                var code = OutputStream();
                AST_BlockStatement.prototype._codegen.call(fun, fun, code);
                self.args = [
                    make_node(AST_String, self, {
                        value: fun.argnames.map(function(arg) {
                            return arg.print_to_string();
                        }).join(",")
                    }),
                    make_node(AST_String, self.args[self.args.length - 1], {
                        value: code.get().replace(/^{|}$/g, "")
                    })
                ];
                return self;
            } catch (ex) {
                if (!(ex instanceof JS_Parse_Error)) {
                    throw ex;
                }

                // Otherwise, it crashes at runtime. Or maybe it's nonstandard syntax.
            }
        }
    }

    var stat = is_func && fn.body[0];
    var is_regular_func = is_func && !fn.is_generator && !fn.async;
    var can_inline = is_regular_func && compressor.option("inline") && !self.is_callee_pure(compressor);
    if (can_inline && AST_Return.hasInstance(stat)) {
        let returned = stat.value;
        if (!returned || returned.is_constant_expression()) {
            if (returned) {
                returned = returned.clone(true);
            } else {
                returned = make_node(AST_Undefined, self);
            }
            const args = self.args.concat(returned);
            return make_sequence(self, args).optimize(compressor);
        }

        // optimize identity function
        if (
            fn.argnames.length === 1
            && (AST_SymbolFunarg.hasInstance(fn.argnames[0]))
            && self.args.length < 2
            && AST_SymbolRef.hasInstance(returned)
            && returned.name === fn.argnames[0].name
        ) {
            const replacement =
                (self.args[0] || make_node(AST_Undefined)).optimize(compressor);

            let parent;
            if (
                AST_PropAccess.hasInstance(replacement)
                && AST_Call.hasInstance(parent = compressor.parent())
                && parent.expression === self
            ) {
                // identity function was being used to remove `this`, like in
                //
                // id(bag.no_this)(...)
                //
                // Replace with a larger but more effish (0, bag.no_this) wrapper.

                return make_sequence(self, [
                    make_node(AST_Number, self, { value: 0 }),
                    replacement
                ]);
            }
            // replace call with first argument or undefined if none passed
            return replacement;
        }
    }

    if (can_inline) {
        var scope, in_loop, level = -1;
        let def;
        let returned_value;
        let nearest_scope;
        if (simple_args
            && !fn.uses_arguments
            && !AST_Class.hasInstance(compressor.parent())
            && !(fn.name && AST_Function.hasInstance(fn))
            && (returned_value = can_flatten_body(stat))
            && (exp === fn
                || has_annotation(self, _INLINE)
                || compressor.option("unused")
                    && (def = exp.definition()).references.length == 1
                    && !is_recursive_ref(compressor, def)
                    && fn.is_constant_expression(exp.scope))
            && !has_annotation(self, _PURE | _NOINLINE)
            && !fn.contains_this()
            && can_inject_symbols()
            && (nearest_scope = find_scope(compressor))
            && !scope_encloses_variables_in_this_scope(nearest_scope, fn)
            && !(function in_default_assign() {
                    // Due to the fact function parameters have their own scope
                    // which can't use `var something` in the function body within,
                    // we simply don't inline into DefaultAssign.
                    let i = 0;
                    let p;
                    while ((p = compressor.parent(i++))) {
                        if (AST_DefaultAssign.hasInstance(p)) return true;
                        if (AST_Block.hasInstance(p)) break;
                    }
                    return false;
                })()
            && !AST_Class.hasInstance(scope)
        ) {
            set_flag(fn, SQUEEZED);
            nearest_scope.add_child_scope(fn);
            return make_sequence(self, flatten_fn(returned_value)).optimize(compressor);
        }
    }

    if (can_inline && has_annotation(self, _INLINE)) {
        set_flag(fn, SQUEEZED);
        fn = make_node(fn.CTOR === AST_Defun ? AST_Function : fn.CTOR, fn, fn);
        fn.figure_out_scope({}, {
            parent_scope: find_scope(compressor),
            toplevel: compressor.get_toplevel()
        });

        return make_node(AST_Call, self, {
            expression: fn,
            args: self.args,
        }).optimize(compressor);
    }

    const can_drop_this_call = is_regular_func && compressor.option("side_effects") && fn.body.every(is_empty);
    if (can_drop_this_call) {
        var args = self.args.concat(make_node(AST_Undefined, self));
        return make_sequence(self, args).optimize(compressor);
    }

    if (compressor.option("negate_iife")
        && AST_SimpleStatement.hasInstance(compressor.parent())
        && is_iife_call(self)) {
        return self.negate(compressor, true);
    }

    var ev = self.evaluate(compressor);
    if (ev !== self) {
        ev = make_node_from_constant(ev, self).optimize(compressor);
        return best_of(compressor, ev, self);
    }

    return self;

    function return_value(stat) {
        if (!stat) return make_node(AST_Undefined, self);
        if (AST_Return.hasInstance(stat)) {
            if (!stat.value) return make_node(AST_Undefined, self);
            return stat.value.clone(true);
        }
        if (AST_SimpleStatement.hasInstance(stat)) {
            return make_node(AST_UnaryPrefix, stat, {
                operator: "void",
                expression: stat.body.clone(true)
            });
        }
    }

    function can_flatten_body(stat) {
        var body = fn.body;
        var len = body.length;
        if (compressor.option("inline") < 3) {
            return len == 1 && return_value(stat);
        }
        stat = null;
        for (var i = 0; i < len; i++) {
            var line = body[i];
            if (AST_Var.hasInstance(line)) {
                if (stat && !line.definitions.every((var_def) =>
                    !var_def.value
                )) {
                    return false;
                }
            } else if (stat) {
                return false;
            } else if (!AST_EmptyStatement.hasInstance(line)) {
                stat = line;
            }
        }
        return return_value(stat);
    }

    function can_inject_args(block_scoped, safe_to_inject) {
        for (var i = 0, len = fn.argnames.length; i < len; i++) {
            var arg = fn.argnames[i];
            if (AST_DefaultAssign.hasInstance(arg)) {
                if (has_flag(arg.left, UNUSED)) continue;
                return false;
            }
            if (AST_Destructuring.hasInstance(arg)) return false;
            if (AST_Expansion.hasInstance(arg)) {
                if (has_flag(arg.expression, UNUSED)) continue;
                return false;
            }
            if (has_flag(arg, UNUSED)) continue;
            if (!safe_to_inject
                || block_scoped.has(arg.name)
                || identifier_atom.has(arg.name)
                || scope.conflicting_def(arg.name)) {
                return false;
            }
            if (in_loop) in_loop.push(arg.definition());
        }
        return true;
    }

    function can_inject_vars(block_scoped, safe_to_inject) {
        var len = fn.body.length;
        for (var i = 0; i < len; i++) {
            var stat = fn.body[i];
            if (!AST_Var.hasInstance(stat)) continue;
            if (!safe_to_inject) return false;
            for (var j = stat.definitions.length; --j >= 0;) {
                var name = stat.definitions[j].name;
                if (AST_Destructuring.hasInstance(name)
                    || block_scoped.has(name.name)
                    || identifier_atom.has(name.name)
                    || scope.conflicting_def(name.name)) {
                    return false;
                }
                if (in_loop) in_loop.push(name.definition());
            }
        }
        return true;
    }

    function can_inject_symbols() {
        var block_scoped = new Set();
        do {
            scope = compressor.parent(++level);
            if (scope.is_block_scope() && scope.block_scope) {
                // TODO this is sometimes undefined during compression.
                // But it should always have a value!
                scope.block_scope.variables.forEach(function (variable) {
                    block_scoped.add(variable.name);
                });
            }
            if (AST_Catch.hasInstance(scope)) {
                // TODO can we delete? AST_Catch is a block scope.
                if (scope.argname) {
                    block_scoped.add(scope.argname.name);
                }
            } else if (AST_IterationStatement.hasInstance(scope)) {
                in_loop = [];
            } else if (AST_SymbolRef.hasInstance(scope)) {
                if (AST_Scope.hasInstance(scope.fixed_value())) return false;
            }
        } while (!AST_Scope.hasInstance(scope));

        var safe_to_inject = !AST_Toplevel.hasInstance(scope) || compressor.toplevel.vars;
        var inline = compressor.option("inline");
        if (!can_inject_vars(block_scoped, inline >= 3 && safe_to_inject)) return false;
        if (!can_inject_args(block_scoped, inline >= 2 && safe_to_inject)) return false;
        return !in_loop || in_loop.length == 0 || !is_reachable(fn, in_loop);
    }

    function append_var(decls, expressions, name, value) {
        var def = name.definition();

        // Name already exists, only when a function argument had the same name
        const already_appended = scope.variables.has(name.name);
        if (!already_appended) {
            scope.variables.set(name.name, def);
            scope.enclosed.push(def);
            decls.push(make_node(AST_VarDef, name, {
                name: name,
                value: null
            }));
        }

        var sym = make_node(AST_SymbolRef, name, name);
        def.references.push(sym);
        if (value) expressions.push(make_node(AST_Assign, self, {
            operator: "=",
            logical: false,
            left: sym,
            right: value.clone()
        }));
    }

    function flatten_args(decls, expressions) {
        var len = fn.argnames.length;
        for (var i = self.args.length; --i >= len;) {
            expressions.push(self.args[i]);
        }
        for (i = len; --i >= 0;) {
            var name = fn.argnames[i];
            var value = self.args[i];
            if (has_flag(name, UNUSED) || !name.name || scope.conflicting_def(name.name)) {
                if (value) expressions.push(value);
            } else {
                var symbol = make_node(AST_SymbolVar, name, name);
                name.definition().orig.push(symbol);
                if (!value && in_loop) value = make_node(AST_Undefined, self);
                append_var(decls, expressions, symbol, value);
            }
        }
        decls.reverse();
        expressions.reverse();
    }

    function flatten_vars(decls, expressions) {
        var pos = expressions.length;
        for (var i = 0, lines = fn.body.length; i < lines; i++) {
            var stat = fn.body[i];
            if (!AST_Var.hasInstance(stat)) continue;
            for (var j = 0, defs = stat.definitions.length; j < defs; j++) {
                var var_def = stat.definitions[j];
                var name = var_def.name;
                append_var(decls, expressions, name, var_def.value);
                if (in_loop && fn.argnames.every((argname) =>
                    argname.name != name.name
                )) {
                    var def = fn.variables.get(name.name);
                    var sym = make_node(AST_SymbolRef, name, name);
                    def.references.push(sym);
                    expressions.splice(pos++, 0, make_node(AST_Assign, var_def, {
                        operator: "=",
                        logical: false,
                        left: sym,
                        right: make_node(AST_Undefined, name)
                    }));
                }
            }
        }
    }

    function flatten_fn(returned_value) {
        var decls = [];
        var expressions = [];
        flatten_args(decls, expressions);
        flatten_vars(decls, expressions);
        expressions.push(returned_value);

        if (decls.length) {
            const i = scope.body.indexOf(compressor.parent(level - 1)) + 1;
            scope.body.splice(i, 0, make_node(AST_Var, fn, {
                definitions: decls
            }));
        }

        return expressions.map(exp => exp.clone(true));
    }
});

def_optimize(AST_New, function(self, compressor) {
    if (
        compressor.option("unsafe") &&
        is_undeclared_ref(self.expression) &&
        ["Object", "RegExp", "Function", "Error", "Array"].includes(self.expression.name)
    ) return make_node(AST_Call, self, self).transform(compressor);
    return self;
});

def_optimize(AST_Sequence, function(self, compressor) {
    if (!compressor.option("side_effects")) return self;
    var expressions = [];
    filter_for_side_effects();
    var end = expressions.length - 1;
    trim_right_for_undefined();
    if (end == 0) {
        self = maintain_this_binding(compressor.parent(), compressor.self(), expressions[0]);
        if (!AST_Sequence.hasInstance(self)) self = self.optimize(compressor);
        return self;
    }
    self.expressions = expressions;
    return self;

    function filter_for_side_effects() {
        var first = first_in_statement(compressor);
        var last = self.expressions.length - 1;
        self.expressions.forEach(function(expr, index) {
            if (index < last) expr = expr.drop_side_effect_free(compressor, first);
            if (expr) {
                merge_sequence(expressions, expr);
                first = false;
            }
        });
    }

    function trim_right_for_undefined() {
        while (end > 0 && is_undefined(expressions[end], compressor)) end--;
        if (end < expressions.length - 1) {
            expressions[end] = make_node(AST_UnaryPrefix, self, {
                operator   : "void",
                expression : expressions[end]
            });
            expressions.length = end + 1;
        }
    }
});

AST_Unary.DEFMETHOD("lift_sequences", function(compressor) {
    if (compressor.option("sequences")) {
        if (AST_Sequence.hasInstance(this.expression)) {
            var x = this.expression.expressions.slice();
            var e = this.clone();
            e.expression = x.pop();
            x.push(e);
            return make_sequence(this, x).optimize(compressor);
        }
    }
    return this;
});

def_optimize(AST_UnaryPostfix, function(self, compressor) {
    return self.lift_sequences(compressor);
});

def_optimize(AST_UnaryPrefix, function(self, compressor) {
    var e = self.expression;
    if (self.operator == "delete"
        && !(AST_SymbolRef.hasInstance(e)
            || AST_PropAccess.hasInstance(e)
            || is_identifier_atom(e))) {
        if (AST_Sequence.hasInstance(e)) {
            const exprs = e.expressions.slice();
            exprs.push(make_node(AST_True, self));
            return make_sequence(self, exprs).optimize(compressor);
        }
        return make_sequence(self, [ e, make_node(AST_True, self) ]).optimize(compressor);
    }
    var seq = self.lift_sequences(compressor);
    if (seq !== self) {
        return seq;
    }
    if (compressor.option("side_effects") && self.operator == "void") {
        e = e.drop_side_effect_free(compressor);
        if (e) {
            self.expression = e;
            return self;
        } else {
            return make_node(AST_Undefined, self).optimize(compressor);
        }
    }
    if (compressor.in_boolean_context()) {
        switch (self.operator) {
          case "!":
            if (AST_UnaryPrefix.hasInstance(e) && e.operator == "!") {
                // !!foo ==> foo, if we're in boolean context
                return e.expression;
            }
            if (AST_Binary.hasInstance(e)) {
                self = best_of(compressor, self, e.negate(compressor, first_in_statement(compressor)));
            }
            break;
          case "typeof":
            // typeof always returns a non-empty string, thus it's
            // always true in booleans
            // And we don't need to check if it's undeclared, because in typeof, that's OK
            return (AST_SymbolRef.hasInstance(e) ? make_node(AST_True, self) : make_sequence(self, [
                e,
                make_node(AST_True, self)
            ])).optimize(compressor);
        }
    }
    if (self.operator == "-" && AST_Infinity.hasInstance(e)) {
        e = e.transform(compressor);
    }
    if (AST_Binary.hasInstance(e)
        && (self.operator == "+" || self.operator == "-")
        && (e.operator == "*" || e.operator == "/" || e.operator == "%")) {
        return make_node(AST_Binary, self, {
            operator: e.operator,
            left: make_node(AST_UnaryPrefix, e.left, {
                operator: self.operator,
                expression: e.left
            }),
            right: e.right
        });
    }
    // avoids infinite recursion of numerals
    if (self.operator != "-"
        || !(AST_Number.hasInstance(e) || AST_Infinity.hasInstance(e) || AST_BigInt.hasInstance(e))) {
        var ev = self.evaluate(compressor);
        if (ev !== self) {
            ev = make_node_from_constant(ev, self).optimize(compressor);
            return best_of(compressor, ev, self);
        }
    }
    return self;
});

AST_Binary.DEFMETHOD("lift_sequences", function(compressor) {
    if (compressor.option("sequences")) {
        if (AST_Sequence.hasInstance(this.left)) {
            var x = this.left.expressions.slice();
            var e = this.clone();
            e.left = x.pop();
            x.push(e);
            return make_sequence(this, x).optimize(compressor);
        }
        if (AST_Sequence.hasInstance(this.right) && !this.left.has_side_effects(compressor)) {
            var assign = this.operator == "=" && AST_SymbolRef.hasInstance(this.left);
            var x = this.right.expressions;
            var last = x.length - 1;
            for (var i = 0; i < last; i++) {
                if (!assign && x[i].has_side_effects(compressor)) break;
            }
            if (i == last) {
                x = x.slice();
                var e = this.clone();
                e.right = x.pop();
                x.push(e);
                return make_sequence(this, x).optimize(compressor);
            } else if (i > 0) {
                var e = this.clone();
                e.right = make_sequence(this.right, x.slice(i));
                x = x.slice(0, i);
                x.push(e);
                return make_sequence(this, x).optimize(compressor);
            }
        }
    }
    return this;
});

var commutativeOperators = makePredicate("== === != !== * & | ^");
function is_object(node) {
    return AST_Array.hasInstance(node)
        || AST_Lambda.hasInstance(node)
        || AST_Object.hasInstance(node)
        || AST_Class.hasInstance(node);
}

def_optimize(AST_Binary, function(self, compressor) {
    function reversible() {
        return self.left.is_constant()
            || self.right.is_constant()
            || !self.left.has_side_effects(compressor)
                && !self.right.has_side_effects(compressor);
    }
    function reverse(op) {
        if (reversible()) {
            if (op) self.operator = op;
            var tmp = self.left;
            self.left = self.right;
            self.right = tmp;
        }
    }
    if (commutativeOperators.has(self.operator)) {
        if (self.right.is_constant()
            && !self.left.is_constant()) {
            // if right is a constant, whatever side effects the
            // left side might have could not influence the
            // result.  hence, force switch.

            if (!(AST_Binary.hasInstance(self.left)
                  && PRECEDENCE[self.left.operator] >= PRECEDENCE[self.operator])) {
                reverse();
            }
        }
    }
    self = self.lift_sequences(compressor);
    if (compressor.option("comparisons")) switch (self.operator) {
      case "===":
      case "!==":
        var is_strict_comparison = true;
        if ((self.left.is_string(compressor) && self.right.is_string(compressor)) ||
            (self.left.is_number(compressor) && self.right.is_number(compressor)) ||
            (self.left.is_boolean() && self.right.is_boolean()) ||
            self.left.equivalent_to(self.right)) {
            self.operator = self.operator.substr(0, 2);
        }
        // XXX: intentionally falling down to the next case
      case "==":
      case "!=":
        // void 0 == x => null == x
        if (!is_strict_comparison && is_undefined(self.left, compressor)) {
            self.left = make_node(AST_Null, self.left);
        } else if (compressor.option("typeofs")
            // "undefined" == typeof x => undefined === x
            && AST_String.hasInstance(self.left)
            && self.left.value == "undefined"
            && AST_UnaryPrefix.hasInstance(self.right)
            && self.right.operator == "typeof") {
            var expr = self.right.expression;
            if (AST_SymbolRef.hasInstance(expr) ? expr.is_declared(compressor)
                : !(AST_PropAccess.hasInstance(expr) && compressor.option("ie8"))) {
                self.right = expr;
                self.left = make_node(AST_Undefined, self.left).optimize(compressor);
                if (self.operator.length == 2) self.operator += "=";
            }
        } else if (AST_SymbolRef.hasInstance(self.left)
            && AST_SymbolRef.hasInstance(self.right)
            && self.left.definition() === self.right.definition()
            && is_object(self.left.fixed_value())) {
            return make_node(self.operator[0] == "=" ? AST_True : AST_False, self);
        }
        break;
      case "&&":
      case "||":
        var lhs = self.left;
        if (lhs.operator == self.operator) {
            lhs = lhs.right;
        }
        if (AST_Binary.hasInstance(lhs)
            && lhs.operator == (self.operator == "&&" ? "!==" : "===")
            && AST_Binary.hasInstance(self.right)
            && lhs.operator == self.right.operator
            && (is_undefined(lhs.left, compressor) && AST_Null.hasInstance(self.right.left)
                || AST_Null.hasInstance(lhs.left) && is_undefined(self.right.left, compressor))
            && !lhs.right.has_side_effects(compressor)
            && lhs.right.equivalent_to(self.right.right)) {
            var combined = make_node(AST_Binary, self, {
                operator: lhs.operator.slice(0, -1),
                left: make_node(AST_Null, self),
                right: lhs.right
            });
            if (lhs !== self.left) {
                combined = make_node(AST_Binary, self, {
                    operator: self.operator,
                    left: self.left.left,
                    right: combined
                });
            }
            return combined;
        }
        break;
    }
    if (self.operator == "+" && compressor.in_boolean_context()) {
        var ll = self.left.evaluate(compressor);
        var rr = self.right.evaluate(compressor);
        if (ll && typeof ll == "string") {
            return make_sequence(self, [
                self.right,
                make_node(AST_True, self)
            ]).optimize(compressor);
        }
        if (rr && typeof rr == "string") {
            return make_sequence(self, [
                self.left,
                make_node(AST_True, self)
            ]).optimize(compressor);
        }
    }
    if (compressor.option("comparisons") && self.is_boolean()) {
        if (!AST_Binary.hasInstance(compressor.parent())
            || AST_Assign.hasInstance(compressor.parent())) {
            var negated = make_node(AST_UnaryPrefix, self, {
                operator: "!",
                expression: self.negate(compressor, first_in_statement(compressor))
            });
            self = best_of(compressor, self, negated);
        }
        if (compressor.option("unsafe_comps")) {
            switch (self.operator) {
              case "<": reverse(">"); break;
              case "<=": reverse(">="); break;
            }
        }
    }
    if (self.operator == "+") {
        if (AST_String.hasInstance(self.right)
            && self.right.getValue() == ""
            && self.left.is_string(compressor)) {
            return self.left;
        }
        if (AST_String.hasInstance(self.left)
            && self.left.getValue() == ""
            && self.right.is_string(compressor)) {
            return self.right;
        }
        if (AST_Binary.hasInstance(self.left)
            && self.left.operator == "+"
            && AST_String.hasInstance(self.left.left)
            && self.left.left.getValue() == ""
            && self.right.is_string(compressor)) {
            self.left = self.left.right;
            return self;
        }
    }
    if (compressor.option("evaluate")) {
        switch (self.operator) {
          case "&&":
            var ll = has_flag(self.left, TRUTHY)
                ? true
                : has_flag(self.left, FALSY)
                    ? false
                    : self.left.evaluate(compressor);
            if (!ll) {
                return maintain_this_binding(compressor.parent(), compressor.self(), self.left).optimize(compressor);
            } else if (!AST_Node.hasInstance(ll)) {
                return make_sequence(self, [ self.left, self.right ]).optimize(compressor);
            }
            var rr = self.right.evaluate(compressor);
            if (!rr) {
                if (compressor.in_boolean_context()) {
                    return make_sequence(self, [
                        self.left,
                        make_node(AST_False, self)
                    ]).optimize(compressor);
                } else {
                    set_flag(self, FALSY);
                }
            } else if (!AST_Node.hasInstance(rr)) {
                var parent = compressor.parent();
                if (parent.operator == "&&" && parent.left === compressor.self() || compressor.in_boolean_context()) {
                    return self.left.optimize(compressor);
                }
            }
            // x || false && y ---> x ? y : false
            if (self.left.operator == "||") {
                var lr = self.left.right.evaluate(compressor);
                if (!lr) return make_node(AST_Conditional, self, {
                    condition: self.left.left,
                    consequent: self.right,
                    alternative: self.left.right
                }).optimize(compressor);
            }
            break;
          case "||":
            var ll = has_flag(self.left, TRUTHY)
              ? true
              : has_flag(self.left, FALSY)
                ? false
                : self.left.evaluate(compressor);
            if (!ll) {
                return make_sequence(self, [ self.left, self.right ]).optimize(compressor);
            } else if (!AST_Node.hasInstance(ll)) {
                return maintain_this_binding(compressor.parent(), compressor.self(), self.left).optimize(compressor);
            }
            var rr = self.right.evaluate(compressor);
            if (!rr) {
                var parent = compressor.parent();
                if (parent.operator == "||" && parent.left === compressor.self() || compressor.in_boolean_context()) {
                    return self.left.optimize(compressor);
                }
            } else if (!AST_Node.hasInstance(rr)) {
                if (compressor.in_boolean_context()) {
                    return make_sequence(self, [
                        self.left,
                        make_node(AST_True, self)
                    ]).optimize(compressor);
                } else {
                    set_flag(self, TRUTHY);
                }
            }
            if (self.left.operator == "&&") {
                var lr = self.left.right.evaluate(compressor);
                if (lr && !AST_Node.hasInstance(lr)) return make_node(AST_Conditional, self, {
                    condition: self.left.left,
                    consequent: self.left.right,
                    alternative: self.right
                }).optimize(compressor);
            }
            break;
          case "??":
            if (is_nullish(self.left, compressor)) {
                return self.right;
            }

            var ll = self.left.evaluate(compressor);
            if (!AST_Node.hasInstance(ll)) {
                // if we know the value for sure we can simply compute right away.
                return ll == null ? self.right : self.left;
            }

            if (compressor.in_boolean_context()) {
                const rr = self.right.evaluate(compressor);
                if (!AST_Node.hasInstance(rr) && !rr) {
                    return self.left;
                }
            }
        }
        var associative = true;
        switch (self.operator) {
          case "+":
            // (x + "foo") + "bar" => x + "foobar"
            if (AST_Constant.hasInstance(self.right)
                && AST_Binary.hasInstance(self.left)
                && self.left.operator == "+"
                && self.left.is_string(compressor)) {
                var binary = make_node(AST_Binary, self, {
                    operator: "+",
                    left: self.left.right,
                    right: self.right,
                });
                var r = binary.optimize(compressor);
                if (binary !== r) {
                    self = make_node(AST_Binary, self, {
                        operator: "+",
                        left: self.left.left,
                        right: r
                    });
                }
            }
            // (x + "foo") + ("bar" + y) => (x + "foobar") + y
            if (AST_Binary.hasInstance(self.left)
                && self.left.operator == "+"
                && self.left.is_string(compressor)
                && AST_Binary.hasInstance(self.right)
                && self.right.operator == "+"
                && self.right.is_string(compressor)) {
                var binary = make_node(AST_Binary, self, {
                    operator: "+",
                    left: self.left.right,
                    right: self.right.left,
                });
                var m = binary.optimize(compressor);
                if (binary !== m) {
                    self = make_node(AST_Binary, self, {
                        operator: "+",
                        left: make_node(AST_Binary, self.left, {
                            operator: "+",
                            left: self.left.left,
                            right: m
                        }),
                        right: self.right.right
                    });
                }
            }
            // a + -b => a - b
            if (AST_UnaryPrefix.hasInstance(self.right)
                && self.right.operator == "-"
                && self.left.is_number(compressor)) {
                self = make_node(AST_Binary, self, {
                    operator: "-",
                    left: self.left,
                    right: self.right.expression
                });
                break;
            }
            // -a + b => b - a
            if (AST_UnaryPrefix.hasInstance(self.left)
                && self.left.operator == "-"
                && reversible()
                && self.right.is_number(compressor)) {
                self = make_node(AST_Binary, self, {
                    operator: "-",
                    left: self.right,
                    right: self.left.expression
                });
                break;
            }
            // `foo${bar}baz` + 1 => `foo${bar}baz1`
            if (AST_TemplateString.hasInstance(self.left)) {
                var l = self.left;
                var r = self.right.evaluate(compressor);
                if (r != self.right) {
                    l.segments[l.segments.length - 1].value += String(r);
                    return l;
                }
            }
            // 1 + `foo${bar}baz` => `1foo${bar}baz`
            if (AST_TemplateString.hasInstance(self.right)) {
                var r = self.right;
                var l = self.left.evaluate(compressor);
                if (l != self.left) {
                    r.segments[0].value = String(l) + r.segments[0].value;
                    return r;
                }
            }
            // `1${bar}2` + `foo${bar}baz` => `1${bar}2foo${bar}baz`
            if (AST_TemplateString.hasInstance(self.left)
                && AST_TemplateString.hasInstance(self.right)) {
                var l = self.left;
                var segments = l.segments;
                var r = self.right;
                segments[segments.length - 1].value += r.segments[0].value;
                for (var i = 1; i < r.segments.length; i++) {
                    segments.push(r.segments[i]);
                }
                return l;
            }
          case "*":
            associative = compressor.option("unsafe_math");
          case "&":
          case "|":
          case "^":
            // a + +b => +b + a
            if (self.left.is_number(compressor)
                && self.right.is_number(compressor)
                && reversible()
                && !(AST_Binary.hasInstance(self.left)
                    && self.left.operator != self.operator
                    && PRECEDENCE[self.left.operator] >= PRECEDENCE[self.operator])) {
                var reversed = make_node(AST_Binary, self, {
                    operator: self.operator,
                    left: self.right,
                    right: self.left
                });
                if (AST_Constant.hasInstance(self.right)
                    && !AST_Constant.hasInstance(self.left)) {
                    self = best_of(compressor, reversed, self);
                } else {
                    self = best_of(compressor, self, reversed);
                }
            }
            if (associative && self.is_number(compressor)) {
                // a + (b + c) => (a + b) + c
                if (AST_Binary.hasInstance(self.right)
                    && self.right.operator == self.operator) {
                    self = make_node(AST_Binary, self, {
                        operator: self.operator,
                        left: make_node(AST_Binary, self.left, {
                            operator: self.operator,
                            left: self.left,
                            right: self.right.left,
                            start: self.left.start,
                            end: self.right.left.end
                        }),
                        right: self.right.right
                    });
                }
                // (n + 2) + 3 => 5 + n
                // (2 * n) * 3 => 6 + n
                if (AST_Constant.hasInstance(self.right)
                    && AST_Binary.hasInstance(self.left)
                    && self.left.operator == self.operator) {
                    if (AST_Constant.hasInstance(self.left.left)) {
                        self = make_node(AST_Binary, self, {
                            operator: self.operator,
                            left: make_node(AST_Binary, self.left, {
                                operator: self.operator,
                                left: self.left.left,
                                right: self.right,
                                start: self.left.left.start,
                                end: self.right.end
                            }),
                            right: self.left.right
                        });
                    } else if (AST_Constant.hasInstance(self.left.right)) {
                        self = make_node(AST_Binary, self, {
                            operator: self.operator,
                            left: make_node(AST_Binary, self.left, {
                                operator: self.operator,
                                left: self.left.right,
                                right: self.right,
                                start: self.left.right.start,
                                end: self.right.end
                            }),
                            right: self.left.left
                        });
                    }
                }
                // (a | 1) | (2 | d) => (3 | a) | b
                if (AST_Binary.hasInstance(self.left)
                    && self.left.operator == self.operator
                    && AST_Constant.hasInstance(self.left.right)
                    && AST_Binary.hasInstance(self.right)
                    && self.right.operator == self.operator
                    && AST_Constant.hasInstance(self.right.left)) {
                    self = make_node(AST_Binary, self, {
                        operator: self.operator,
                        left: make_node(AST_Binary, self.left, {
                            operator: self.operator,
                            left: make_node(AST_Binary, self.left.left, {
                                operator: self.operator,
                                left: self.left.right,
                                right: self.right.left,
                                start: self.left.right.start,
                                end: self.right.left.end
                            }),
                            right: self.left.left
                        }),
                        right: self.right.right
                    });
                }
            }
        }
    }
    // x && (y && z)  ==>  x && y && z
    // x || (y || z)  ==>  x || y || z
    // x + ("y" + z)  ==>  x + "y" + z
    // "x" + (y + "z")==>  "x" + y + "z"
    if (AST_Binary.hasInstance(self.right)
        && self.right.operator == self.operator
        && (lazy_op.has(self.operator)
            || (self.operator == "+"
                && (self.right.left.is_string(compressor)
                    || (self.left.is_string(compressor)
                        && self.right.right.is_string(compressor)))))
    ) {
        self.left = make_node(AST_Binary, self.left, {
            operator : self.operator,
            left     : self.left.transform(compressor),
            right    : self.right.left.transform(compressor)
        });
        self.right = self.right.right.transform(compressor);
        return self.transform(compressor);
    }
    var ev = self.evaluate(compressor);
    if (ev !== self) {
        ev = make_node_from_constant(ev, self).optimize(compressor);
        return best_of(compressor, ev, self);
    }
    return self;
});

def_optimize(AST_SymbolExport, function(self) {
    return self;
});

function within_array_or_object_literal(compressor) {
    var node, level = 0;
    while (node = compressor.parent(level++)) {
        if (AST_Statement.hasInstance(node)) return false;
        if (AST_Array.hasInstance(node)
            || AST_ObjectKeyVal.hasInstance(node)
            || AST_Object.hasInstance(node)) {
            return true;
        }
    }
    return false;
}

def_optimize(AST_SymbolRef, function(self, compressor) {
    if (
        !compressor.option("ie8")
        && is_undeclared_ref(self)
        && !compressor.find_parent(AST_With)
    ) {
        switch (self.name) {
          case "undefined":
            return make_node(AST_Undefined, self).optimize(compressor);
          case "NaN":
            return make_node(AST_NaN, self).optimize(compressor);
          case "Infinity":
            return make_node(AST_Infinity, self).optimize(compressor);
        }
    }

    const parent = compressor.parent();
    if (compressor.option("reduce_vars") && is_lhs(self, parent) !== self) {
        const def = self.definition();
        const nearest_scope = find_scope(compressor);
        if (compressor.top_retain && def.global && compressor.top_retain(def)) {
            def.fixed = false;
            def.single_use = false;
            return self;
        }

        let fixed = self.fixed_value();
        let single_use = def.single_use
            && !(AST_Call.hasInstance(parent)
                && (parent.is_callee_pure(compressor))
                    || has_annotation(parent, _NOINLINE))
            && !(AST_Export.hasInstance(parent)
                && AST_Lambda.hasInstance(fixed)
                && fixed.name);

        if (single_use && AST_Node.hasInstance(fixed)) {
            single_use =
                !fixed.has_side_effects(compressor)
                && !fixed.may_throw(compressor);
        }

        if (single_use && (AST_Lambda.hasInstance(fixed) || AST_Class.hasInstance(fixed))) {
            if (retain_top_func(fixed, compressor)) {
                single_use = false;
            } else if (def.scope !== self.scope
                && (def.escaped == 1
                    || has_flag(fixed, INLINED)
                    || within_array_or_object_literal(compressor)
                    || !compressor.option("reduce_funcs"))) {
                single_use = false;
            } else if (is_recursive_ref(compressor, def)) {
                single_use = false;
            } else if (def.scope !== self.scope || AST_SymbolFunarg.hasInstance(def.orig[0])) {
                single_use = fixed.is_constant_expression(self.scope);
                if (single_use == "f") {
                    var scope = self.scope;
                    do {
                        if (AST_Defun.hasInstance(scope) || is_func_expr(scope)) {
                            set_flag(scope, INLINED);
                        }
                    } while (scope = scope.parent_scope);
                }
            }
        }

        if (single_use && AST_Lambda.hasInstance(fixed)) {
            single_use =
                def.scope === self.scope
                    && !scope_encloses_variables_in_this_scope(nearest_scope, fixed)
                || AST_Call.hasInstance(parent)
                    && parent.expression === self
                    && !scope_encloses_variables_in_this_scope(nearest_scope, fixed)
                    && !(fixed.name && fixed.name.definition().recursive_refs > 0);
        }

        if (single_use && fixed) {
            if (AST_DefClass.hasInstance(fixed)) {
                set_flag(fixed, SQUEEZED);
                fixed = make_node(AST_ClassExpression, fixed, fixed);
            }
            if (AST_Defun.hasInstance(fixed)) {
                set_flag(fixed, SQUEEZED);
                fixed = make_node(AST_Function, fixed, fixed);
            }
            if (def.recursive_refs > 0 && AST_SymbolDefun.hasInstance(fixed.name)) {
                const defun_def = fixed.name.definition();
                let lambda_def = fixed.variables.get(fixed.name.name);
                let name = lambda_def && lambda_def.orig[0];
                if (!AST_SymbolLambda.hasInstance(name)) {
                    name = make_node(AST_SymbolLambda, fixed.name, fixed.name);
                    name.scope = fixed;
                    fixed.name = name;
                    lambda_def = fixed.def_function(name);
                }
                walk(fixed, node => {
                    if (AST_SymbolRef.hasInstance(node) && node.definition() === defun_def) {
                        node.thedef = lambda_def;
                        lambda_def.references.push(node);
                    }
                });
            }
            if (
                (AST_Lambda.hasInstance(fixed) || AST_Class.hasInstance(fixed))
                && fixed.parent_scope !== nearest_scope
            ) {
                fixed = fixed.clone(true, compressor.get_toplevel());

                nearest_scope.add_child_scope(fixed);
            }
            return fixed.optimize(compressor);
        }

        // multiple uses
        if (fixed) {
            let replace;

            if (AST_This.hasInstance(fixed)) {
                if (!AST_SymbolFunarg.hasInstance(def.orig[0])
                    && def.references.every((ref) =>
                        def.scope === ref.scope
                    )) {
                    replace = fixed;
                }
            } else {
                var ev = fixed.evaluate(compressor);
                if (
                    ev !== fixed
                    && (compressor.option("unsafe_regexp") || !(ev instanceof RegExp))
                ) {
                    replace = make_node_from_constant(ev, fixed);
                }
            }

            if (replace) {
                const name_length = self.size(compressor);
                const replace_size = replace.size(compressor);

                let overhead = 0;
                if (compressor.option("unused") && !compressor.exposed(def)) {
                    overhead =
                        (name_length + 2 + replace_size) /
                        (def.references.length - def.assignments);
                }

                if (replace_size <= name_length + overhead) {
                    return replace;
                }
            }
        }
    }

    return self;
});

function scope_encloses_variables_in_this_scope(scope, pulled_scope) {
    for (const enclosed of pulled_scope.enclosed) {
        if (pulled_scope.variables.has(enclosed.name)) {
            continue;
        }
        const looked_up = scope.find_variable(enclosed.name);
        if (looked_up) {
            if (looked_up === enclosed) continue;
            return true;
        }
    }
    return false;
}

function is_atomic(lhs, self) {
    return AST_SymbolRef.hasInstance(lhs) || lhs.TYPE === self.TYPE;
}

def_optimize(AST_Undefined, function(self, compressor) {
    if (compressor.option("unsafe_undefined")) {
        var undef = find_variable(compressor, "undefined");
        if (undef) {
            var ref = make_node(AST_SymbolRef, self, {
                name   : "undefined",
                scope  : undef.scope,
                thedef : undef
            });
            set_flag(ref, UNDEFINED);
            return ref;
        }
    }
    var lhs = is_lhs(compressor.self(), compressor.parent());
    if (lhs && is_atomic(lhs, self)) return self;
    return make_node(AST_UnaryPrefix, self, {
        operator: "void",
        expression: make_node(AST_Number, self, {
            value: 0
        })
    });
});

def_optimize(AST_Infinity, function(self, compressor) {
    var lhs = is_lhs(compressor.self(), compressor.parent());
    if (lhs && is_atomic(lhs, self)) return self;
    if (
        compressor.option("keep_infinity")
        && !(lhs && !is_atomic(lhs, self))
        && !find_variable(compressor, "Infinity")
    ) {
        return self;
    }
    return make_node(AST_Binary, self, {
        operator: "/",
        left: make_node(AST_Number, self, {
            value: 1
        }),
        right: make_node(AST_Number, self, {
            value: 0
        })
    });
});

def_optimize(AST_NaN, function(self, compressor) {
    var lhs = is_lhs(compressor.self(), compressor.parent());
    if (lhs && !is_atomic(lhs, self)
        || find_variable(compressor, "NaN")) {
        return make_node(AST_Binary, self, {
            operator: "/",
            left: make_node(AST_Number, self, {
                value: 0
            }),
            right: make_node(AST_Number, self, {
                value: 0
            })
        });
    }
    return self;
});

function is_reachable(self, defs) {
    const find_ref = node => {
        if (AST_SymbolRef.hasInstance(node) && member(node.definition(), defs)) {
            return walk_abort;
        }
    };

    return walk_parent(self, (node, info) => {
        if (AST_Scope.hasInstance(node) && node !== self) {
            var parent = info.parent();

            if (AST_Call.hasInstance(parent) && parent.expression === node) return;

            if (walk(node, find_ref)) return walk_abort;

            return true;
        }
    });
}

const ASSIGN_OPS = makePredicate("+ - / * % >> << >>> | ^ &");
const ASSIGN_OPS_COMMUTATIVE = makePredicate("* | ^ &");
def_optimize(AST_Assign, function(self, compressor) {
    if (self.logical) {
        return self.lift_sequences(compressor);
    }

    var def;
    if (compressor.option("dead_code")
        && AST_SymbolRef.hasInstance(self.left)
        && (def = self.left.definition()).scope === compressor.find_parent(AST_Lambda)) {
        var level = 0, node, parent = self;
        do {
            node = parent;
            parent = compressor.parent(level++);
            if (AST_Exit.hasInstance(parent)) {
                if (in_try(level, parent)) break;
                if (is_reachable(def.scope, [ def ])) break;
                if (self.operator == "=") return self.right;
                def.fixed = false;
                return make_node(AST_Binary, self, {
                    operator: self.operator.slice(0, -1),
                    left: self.left,
                    right: self.right
                }).optimize(compressor);
            }
        } while (AST_Binary.hasInstance(parent) && parent.right === node
            || AST_Sequence.hasInstance(parent) && parent.tail_node() === node);
    }
    self = self.lift_sequences(compressor);
    if (self.operator == "=" && AST_SymbolRef.hasInstance(self.left) && AST_Binary.hasInstance(self.right)) {
        // x = expr1 OP expr2
        if (AST_SymbolRef.hasInstance(self.right.left)
            && self.right.left.name == self.left.name
            && ASSIGN_OPS.has(self.right.operator)) {
            // x = x - 2  --->  x -= 2
            self.operator = self.right.operator + "=";
            self.right = self.right.right;
        } else if (AST_SymbolRef.hasInstance(self.right.right)
            && self.right.right.name == self.left.name
            && ASSIGN_OPS_COMMUTATIVE.has(self.right.operator)
            && !self.right.left.has_side_effects(compressor)) {
            // x = 2 & x  --->  x &= 2
            self.operator = self.right.operator + "=";
            self.right = self.right.left;
        }
    }
    return self;

    function in_try(level, node) {
        var right = self.right;
        self.right = make_node(AST_Null, right);
        var may_throw = node.may_throw(compressor);
        self.right = right;
        var scope = self.left.definition().scope;
        var parent;
        while ((parent = compressor.parent(level++)) !== scope) {
            if (AST_Try.hasInstance(parent)) {
                if (parent.bfinally) return true;
                if (may_throw && parent.bcatch) return true;
            }
        }
    }
});

def_optimize(AST_DefaultAssign, function(self, compressor) {
    if (!compressor.option("evaluate")) {
        return self;
    }
    var evaluateRight = self.right.evaluate(compressor);

    // `[x = undefined] = foo` ---> `[x] = foo`
    if (evaluateRight === undefined) {
        self = self.left;
    } else if (evaluateRight !== self.right) {
        evaluateRight = make_node_from_constant(evaluateRight, self.right);
        self.right = best_of_expression(evaluateRight, self.right);
    }

    return self;
});

function is_nullish_check(check, check_subject, compressor) {
    if (check_subject.may_throw(compressor)) return false;

    let nullish_side;

    // foo == null
    if (
        AST_Binary.hasInstance(check)
        && check.operator === "=="
        // which side is nullish?
        && (
            (nullish_side = is_nullish(check.left, compressor) && check.left)
            || (nullish_side = is_nullish(check.right, compressor) && check.right)
        )
        // is the other side the same as the check_subject
        && (
            nullish_side === check.left
                ? check.right
                : check.left
        ).equivalent_to(check_subject)
    ) {
        return true;
    }

    // foo === null || foo === undefined
    if (AST_Binary.hasInstance(check) && check.operator === "||") {
        let null_cmp;
        let undefined_cmp;

        const find_comparison = cmp => {
            if (!(
                AST_Binary.hasInstance(cmp)
                && (cmp.operator === "===" || cmp.operator === "==")
            )) {
                return false;
            }

            let found = 0;
            let defined_side;

            if (AST_Null.hasInstance(cmp.left)) {
                found++;
                null_cmp = cmp;
                defined_side = cmp.right;
            }
            if (AST_Null.hasInstance(cmp.right)) {
                found++;
                null_cmp = cmp;
                defined_side = cmp.left;
            }
            if (is_undefined(cmp.left, compressor)) {
                found++;
                undefined_cmp = cmp;
                defined_side = cmp.right;
            }
            if (is_undefined(cmp.right, compressor)) {
                found++;
                undefined_cmp = cmp;
                defined_side = cmp.left;
            }

            if (found !== 1) {
                return false;
            }

            if (!defined_side.equivalent_to(check_subject)) {
                return false;
            }

            return true;
        };

        if (!find_comparison(check.left)) return false;
        if (!find_comparison(check.right)) return false;

        if (null_cmp && undefined_cmp && null_cmp !== undefined_cmp) {
            return true;
        }
    }

    return false;
}

def_optimize(AST_Conditional, function(self, compressor) {
    if (!compressor.option("conditionals")) return self;
    // This looks like lift_sequences(), should probably be under "sequences"
    if (AST_Sequence.hasInstance(self.condition)) {
        var expressions = self.condition.expressions.slice();
        self.condition = expressions.pop();
        expressions.push(self);
        return make_sequence(self, expressions);
    }
    var cond = self.condition.evaluate(compressor);
    if (cond !== self.condition) {
        if (cond) {
            return maintain_this_binding(compressor.parent(), compressor.self(), self.consequent);
        } else {
            return maintain_this_binding(compressor.parent(), compressor.self(), self.alternative);
        }
    }
    var negated = cond.negate(compressor, first_in_statement(compressor));
    if (best_of(compressor, cond, negated) === negated) {
        self = make_node(AST_Conditional, self, {
            condition: negated,
            consequent: self.alternative,
            alternative: self.consequent
        });
    }
    var condition = self.condition;
    var consequent = self.consequent;
    var alternative = self.alternative;
    // x?x:y --> x||y
    if (AST_SymbolRef.hasInstance(condition)
        && AST_SymbolRef.hasInstance(consequent)
        && condition.definition() === consequent.definition()) {
        return make_node(AST_Binary, self, {
            operator: "||",
            left: condition,
            right: alternative
        });
    }
    // if (foo) exp = something; else exp = something_else;
    //                   |
    //                   v
    // exp = foo ? something : something_else;
    if (
        AST_Assign.hasInstance(consequent)
        && AST_Assign.hasInstance(alternative)
        && consequent.operator === alternative.operator
        && consequent.logical === alternative.logical
        && consequent.left.equivalent_to(alternative.left)
        && (!self.condition.has_side_effects(compressor)
            || consequent.operator == "="
                && !consequent.left.has_side_effects(compressor))
    ) {
        return make_node(AST_Assign, self, {
            operator: consequent.operator,
            left: consequent.left,
            logical: consequent.logical,
            right: make_node(AST_Conditional, self, {
                condition: self.condition,
                consequent: consequent.right,
                alternative: alternative.right
            })
        });
    }
    // x ? y(a) : y(b) --> y(x ? a : b)
    var arg_index;
    if (AST_Call.hasInstance(consequent)
        && alternative.TYPE === consequent.TYPE
        && consequent.args.length > 0
        && consequent.args.length == alternative.args.length
        && consequent.expression.equivalent_to(alternative.expression)
        && !self.condition.has_side_effects(compressor)
        && !consequent.expression.has_side_effects(compressor)
        && typeof (arg_index = single_arg_diff()) == "number") {
        var node = consequent.clone();
        node.args[arg_index] = make_node(AST_Conditional, self, {
            condition: self.condition,
            consequent: consequent.args[arg_index],
            alternative: alternative.args[arg_index]
        });
        return node;
    }
    // a ? b : c ? b : d --> (a || c) ? b : d
    if (AST_Conditional.hasInstance(alternative)
        && consequent.equivalent_to(alternative.consequent)) {
        return make_node(AST_Conditional, self, {
            condition: make_node(AST_Binary, self, {
                operator: "||",
                left: condition,
                right: alternative.condition
            }),
            consequent: consequent,
            alternative: alternative.alternative
        }).optimize(compressor);
    }

    // a == null ? b : a -> a ?? b
    if (
        compressor.option("ecma") >= 2020 &&
        is_nullish_check(condition, alternative, compressor)
    ) {
        return make_node(AST_Binary, self, {
            operator: "??",
            left: alternative,
            right: consequent
        }).optimize(compressor);
    }

    // a ? b : (c, b) --> (a || c), b
    if (AST_Sequence.hasInstance(alternative)
        && consequent.equivalent_to(alternative.expressions[alternative.expressions.length - 1])) {
        return make_sequence(self, [
            make_node(AST_Binary, self, {
                operator: "||",
                left: condition,
                right: make_sequence(self, alternative.expressions.slice(0, -1))
            }),
            consequent
        ]).optimize(compressor);
    }
    // a ? b : (c && b) --> (a || c) && b
    if (AST_Binary.hasInstance(alternative)
        && alternative.operator == "&&"
        && consequent.equivalent_to(alternative.right)) {
        return make_node(AST_Binary, self, {
            operator: "&&",
            left: make_node(AST_Binary, self, {
                operator: "||",
                left: condition,
                right: alternative.left
            }),
            right: consequent
        }).optimize(compressor);
    }
    // x?y?z:a:a --> x&&y?z:a
    if (AST_Conditional.hasInstance(consequent)
        && consequent.alternative.equivalent_to(alternative)) {
        return make_node(AST_Conditional, self, {
            condition: make_node(AST_Binary, self, {
                left: self.condition,
                operator: "&&",
                right: consequent.condition
            }),
            consequent: consequent.consequent,
            alternative: alternative
        });
    }
    // x ? y : y --> x, y
    if (consequent.equivalent_to(alternative)) {
        return make_sequence(self, [
            self.condition,
            consequent
        ]).optimize(compressor);
    }
    // x ? y || z : z --> x && y || z
    if (AST_Binary.hasInstance(consequent)
        && consequent.operator == "||"
        && consequent.right.equivalent_to(alternative)) {
        return make_node(AST_Binary, self, {
            operator: "||",
            left: make_node(AST_Binary, self, {
                operator: "&&",
                left: self.condition,
                right: consequent.left
            }),
            right: alternative
        }).optimize(compressor);
    }

    const in_bool = compressor.in_boolean_context();
    if (is_true(self.consequent)) {
        if (is_false(self.alternative)) {
            // c ? true : false ---> !!c
            return booleanize(self.condition);
        }
        // c ? true : x ---> !!c || x
        return make_node(AST_Binary, self, {
            operator: "||",
            left: booleanize(self.condition),
            right: self.alternative
        });
    }
    if (is_false(self.consequent)) {
        if (is_true(self.alternative)) {
            // c ? false : true ---> !c
            return booleanize(self.condition.negate(compressor));
        }
        // c ? false : x ---> !c && x
        return make_node(AST_Binary, self, {
            operator: "&&",
            left: booleanize(self.condition.negate(compressor)),
            right: self.alternative
        });
    }
    if (is_true(self.alternative)) {
        // c ? x : true ---> !c || x
        return make_node(AST_Binary, self, {
            operator: "||",
            left: booleanize(self.condition.negate(compressor)),
            right: self.consequent
        });
    }
    if (is_false(self.alternative)) {
        // c ? x : false ---> !!c && x
        return make_node(AST_Binary, self, {
            operator: "&&",
            left: booleanize(self.condition),
            right: self.consequent
        });
    }

    return self;

    function booleanize(node) {
        if (node.is_boolean()) return node;
        // !!expression
        return make_node(AST_UnaryPrefix, node, {
            operator: "!",
            expression: node.negate(compressor)
        });
    }

    // AST_True or !0
    function is_true(node) {
        return AST_True.hasInstance(node)
            || in_bool
                && AST_Constant.hasInstance(node)
                && node.getValue()
            || (AST_UnaryPrefix.hasInstance(node)
                && node.operator == "!"
                && AST_Constant.hasInstance(node.expression)
                && !node.expression.getValue());
    }
    // AST_False or !1
    function is_false(node) {
        return AST_False.hasInstance(node)
            || in_bool
                && AST_Constant.hasInstance(node)
                && !node.getValue()
            || (AST_UnaryPrefix.hasInstance(node)
                && node.operator == "!"
                && AST_Constant.hasInstance(node.expression)
                && node.expression.getValue());
    }

    function single_arg_diff() {
        var a = consequent.args;
        var b = alternative.args;
        for (var i = 0, len = a.length; i < len; i++) {
            if (AST_Expansion.hasInstance(a[i])) return;
            if (!a[i].equivalent_to(b[i])) {
                if (AST_Expansion.hasInstance(b[i])) return;
                for (var j = i + 1; j < len; j++) {
                    if (AST_Expansion.hasInstance(a[j])) return;
                    if (!a[j].equivalent_to(b[j])) return;
                }
                return i;
            }
        }
    }
});

def_optimize(AST_Boolean, function(self, compressor) {
    if (compressor.in_boolean_context()) return make_node(AST_Number, self, {
        value: +self.value
    });
    var p = compressor.parent();
    if (compressor.option("booleans_as_integers")) {
        if (AST_Binary.hasInstance(p) && (p.operator == "===" || p.operator == "!==")) {
            p.operator = p.operator.replace(/=$/, "");
        }
        return make_node(AST_Number, self, {
            value: +self.value
        });
    }
    if (compressor.option("booleans")) {
        if (AST_Binary.hasInstance(p) && (p.operator == "=="
                                        || p.operator == "!=")) {
            return make_node(AST_Number, self, {
                value: +self.value
            });
        }
        return make_node(AST_UnaryPrefix, self, {
            operator: "!",
            expression: make_node(AST_Number, self, {
                value: 1 - self.value
            })
        });
    }
    return self;
});

function safe_to_flatten(value, compressor) {
    if (AST_SymbolRef.hasInstance(value)) {
        value = value.fixed_value();
    }
    if (!value) return false;
    if (!(AST_Lambda.hasInstance(value) || AST_Class.hasInstance(value))) return true;
    if (!(AST_Lambda.hasInstance(value) && value.contains_this())) return true;
    return AST_New.hasInstance(compressor.parent());
}

AST_PropAccess.DEFMETHOD("flatten_object", function(key, compressor) {
    if (!compressor.option("properties")) return;
    if (key === "__proto__") return;

    var arrows = compressor.option("unsafe_arrows") && compressor.option("ecma") >= 2015;
    var expr = this.expression;
    if (AST_Object.hasInstance(expr)) {
        var props = expr.properties;

        for (var i = props.length; --i >= 0;) {
            var prop = props[i];

            if ("" + (AST_ConciseMethod.hasInstance(prop) ? prop.key.name : prop.key) == key) {
                const all_props_flattenable = props.every((p) =>
                    (AST_ObjectKeyVal.hasInstance(p)
                        || arrows && AST_ConciseMethod.hasInstance(p) && !p.is_generator
                    )
                    && !p.computed_key()
                );

                if (!all_props_flattenable) return;
                if (!safe_to_flatten(prop.value, compressor)) return;

                return make_node(AST_Sub, this, {
                    expression: make_node(AST_Array, expr, {
                        elements: props.map(function(prop) {
                            var v = prop.value;
                            if (AST_Accessor.hasInstance(v)) {
                                v = make_node(AST_Function, v, v);
                            }

                            var k = prop.key;
                            if (AST_Node.hasInstance(k) && !AST_SymbolMethod.hasInstance(k)) {
                                return make_sequence(prop, [ k, v ]);
                            }

                            return v;
                        })
                    }),
                    property: make_node(AST_Number, this, {
                        value: i
                    })
                });
            }
        }
    }
});

def_optimize(AST_Sub, function(self, compressor) {
    var expr = self.expression;
    var prop = self.property;
    if (compressor.option("properties")) {
        var key = prop.evaluate(compressor);
        if (key !== prop) {
            if (typeof key == "string") {
                if (key == "undefined") {
                    key = undefined;
                } else {
                    var value = parseFloat(key);
                    if (value.toString() == key) {
                        key = value;
                    }
                }
            }
            prop = self.property = best_of_expression(prop, make_node_from_constant(key, prop).transform(compressor));
            var property = "" + key;
            if (is_basic_identifier_string(property)
                && property.length <= prop.size() + 1) {
                return make_node(AST_Dot, self, {
                    expression: expr,
                    optional: self.optional,
                    property: property,
                    quote: prop.quote,
                }).optimize(compressor);
            }
        }
    }
    var fn;
    OPT_ARGUMENTS: if (compressor.option("arguments")
        && AST_SymbolRef.hasInstance(expr)
        && expr.name == "arguments"
        && expr.definition().orig.length == 1
        && AST_Lambda.hasInstance(fn = expr.scope)
        && fn.uses_arguments
        && !AST_Arrow.hasInstance(fn)
        && AST_Number.hasInstance(prop)) {
        var index = prop.getValue();
        var params = new Set();
        var argnames = fn.argnames;
        for (var n = 0; n < argnames.length; n++) {
            if (!AST_SymbolFunarg.hasInstance(argnames[n])) {
                break OPT_ARGUMENTS; // destructuring parameter - bail
            }
            var param = argnames[n].name;
            if (params.has(param)) {
                break OPT_ARGUMENTS; // duplicate parameter - bail
            }
            params.add(param);
        }
        var argname = fn.argnames[index];
        if (argname && compressor.has_directive("use strict")) {
            var def = argname.definition();
            if (!compressor.option("reduce_vars") || def.assignments || def.orig.length > 1) {
                argname = null;
            }
        } else if (!argname && !compressor.option("keep_fargs") && index < fn.argnames.length + 5) {
            while (index >= fn.argnames.length) {
                argname = fn.create_symbol(AST_SymbolFunarg, {
                    source: fn,
                    scope: fn,
                    tentative_name: "argument_" + fn.argnames.length,
                });
                fn.argnames.push(argname);
            }
        }
        if (argname) {
            var sym = make_node(AST_SymbolRef, self, argname);
            sym.reference({});
            clear_flag(argname, UNUSED);
            return sym;
        }
    }
    if (is_lhs(self, compressor.parent())) return self;
    if (key !== prop) {
        var sub = self.flatten_object(property, compressor);
        if (sub) {
            expr = self.expression = sub.expression;
            prop = self.property = sub.property;
        }
    }
    if (compressor.option("properties") && compressor.option("side_effects")
        && AST_Number.hasInstance(prop) && AST_Array.hasInstance(expr)) {
        var index = prop.getValue();
        var elements = expr.elements;
        var retValue = elements[index];
        FLATTEN: if (safe_to_flatten(retValue, compressor)) {
            var flatten = true;
            var values = [];
            for (var i = elements.length; --i > index;) {
                var value = elements[i].drop_side_effect_free(compressor);
                if (value) {
                    values.unshift(value);
                    if (flatten && value.has_side_effects(compressor)) flatten = false;
                }
            }
            if (AST_Expansion.hasInstance(retValue)) break FLATTEN;
            retValue = AST_Hole.hasInstance(retValue) ? make_node(AST_Undefined, retValue) : retValue;
            if (!flatten) values.unshift(retValue);
            while (--i >= 0) {
                var value = elements[i];
                if (AST_Expansion.hasInstance(value)) break FLATTEN;
                value = value.drop_side_effect_free(compressor);
                if (value) values.unshift(value);
                else index--;
            }
            if (flatten) {
                values.push(retValue);
                return make_sequence(self, values).optimize(compressor);
            } else return make_node(AST_Sub, self, {
                expression: make_node(AST_Array, expr, {
                    elements: values
                }),
                property: make_node(AST_Number, prop, {
                    value: index
                })
            });
        }
    }
    var ev = self.evaluate(compressor);
    if (ev !== self) {
        ev = make_node_from_constant(ev, self).optimize(compressor);
        return best_of(compressor, ev, self);
    }
    if (self.optional && is_nullish(self.expression, compressor)) {
        return make_node(AST_Undefined, self);
    }
    return self;
});

def_optimize(AST_Chain, function (self, compressor) {
    self.expression = self.expression.optimize(compressor);
    return self;
});

AST_Lambda.DEFMETHOD("contains_this", function() {
    return walk(this, node => {
        if (AST_This.hasInstance(node)) return walk_abort;
        if (
            node !== this
            && AST_Scope.hasInstance(node)
            && !AST_Arrow.hasInstance(node)
        ) {
            return true;
        }
    });
});

def_optimize(AST_Dot, function(self, compressor) {
    const parent = compressor.parent();
    if (is_lhs(self, parent)) return self;
    if (compressor.option("unsafe_proto")
        && AST_Dot.hasInstance(self.expression)
        && self.expression.property == "prototype") {
        var exp = self.expression.expression;
        if (is_undeclared_ref(exp)) switch (exp.name) {
          case "Array":
            self.expression = make_node(AST_Array, self.expression, {
                elements: []
            });
            break;
          case "Function":
            self.expression = make_node(AST_Function, self.expression, {
                argnames: [],
                body: []
            });
            break;
          case "Number":
            self.expression = make_node(AST_Number, self.expression, {
                value: 0
            });
            break;
          case "Object":
            self.expression = make_node(AST_Object, self.expression, {
                properties: []
            });
            break;
          case "RegExp":
            self.expression = make_node(AST_RegExp, self.expression, {
                value: { source: "t", flags: "" }
            });
            break;
          case "String":
            self.expression = make_node(AST_String, self.expression, {
                value: ""
            });
            break;
        }
    }
    if (!AST_Call.hasInstance(parent) || !has_annotation(parent, _NOINLINE)) {
        const sub = self.flatten_object(self.property, compressor);
        if (sub) return sub.optimize(compressor);
    }
    let ev = self.evaluate(compressor);
    if (ev !== self) {
        ev = make_node_from_constant(ev, self).optimize(compressor);
        return best_of(compressor, ev, self);
    }
    if (self.optional && is_nullish(self.expression, compressor)) {
        return make_node(AST_Undefined, self);
    }
    return self;
});

function literals_in_boolean_context(self, compressor) {
    if (compressor.in_boolean_context()) {
        return best_of(compressor, self, make_sequence(self, [
            self,
            make_node(AST_True, self)
        ]).optimize(compressor));
    }
    return self;
}

function inline_array_like_spread(elements) {
    for (var i = 0; i < elements.length; i++) {
        var el = elements[i];
        if (AST_Expansion.hasInstance(el)) {
            var expr = el.expression;
            if (
                AST_Array.hasInstance(expr)
                && !expr.elements.some(elm => AST_Hole.hasInstance(elm))
            ) {
                elements.splice(i, 1, ...expr.elements);
                // Step back one, as the element at i is now new.
                i--;
            }
            // In array-like spread, spreading a non-iterable value is TypeError.
            // We therefore can’t optimize anything else, unlike with object spread.
        }
    }
}

def_optimize(AST_Array, function(self, compressor) {
    var optimized = literals_in_boolean_context(self, compressor);
    if (optimized !== self) {
        return optimized;
    }
    inline_array_like_spread(self.elements);
    return self;
});

function inline_object_prop_spread(props, compressor) {
    for (var i = 0; i < props.length; i++) {
        var prop = props[i];
        if (AST_Expansion.hasInstance(prop)) {
            const expr = prop.expression;
            if (
                AST_Object.hasInstance(expr)
                && expr.properties.every(prop => AST_ObjectKeyVal.hasInstance(prop))
            ) {
                props.splice(i, 1, ...expr.properties);
                // Step back one, as the property at i is now new.
                i--;
            } else if (AST_Constant.hasInstance(expr)
                && !AST_String.hasInstance(expr)) {
                // Unlike array-like spread, in object spread, spreading a
                // non-iterable value silently does nothing; it is thus safe
                // to remove. AST_String is the only iterable AST_Constant.
                props.splice(i, 1);
            } else if (is_nullish(expr, compressor)) {
                // Likewise, null and undefined can be silently removed.
                props.splice(i, 1);
            }
        }
    }
}

def_optimize(AST_Object, function(self, compressor) {
    var optimized = literals_in_boolean_context(self, compressor);
    if (optimized !== self) {
        return optimized;
    }
    inline_object_prop_spread(self.properties, compressor);
    return self;
});

def_optimize(AST_RegExp, literals_in_boolean_context);

def_optimize(AST_Return, function(self, compressor) {
    if (self.value && is_undefined(self.value, compressor)) {
        self.value = null;
    }
    return self;
});

def_optimize(AST_Arrow, opt_AST_Lambda);

def_optimize(AST_Function, function(self, compressor) {
    self = opt_AST_Lambda(self, compressor);
    if (compressor.option("unsafe_arrows")
        && compressor.option("ecma") >= 2015
        && !self.name
        && !self.is_generator
        && !self.uses_arguments
        && !self.pinned()) {
        const uses_this = walk(self, node => {
            if (AST_This.hasInstance(node)) return walk_abort;
        });
        if (!uses_this) return make_node(AST_Arrow, self, self).optimize(compressor);
    }
    return self;
});

def_optimize(AST_Class, function(self) {
    // HACK to avoid compress failure.
    // AST_Class is not really an AST_Scope/AST_Block as it lacks a body.
    return self;
});

def_optimize(AST_Yield, function(self, compressor) {
    if (self.expression && !self.is_star && is_undefined(self.expression, compressor)) {
        self.expression = null;
    }
    return self;
});

def_optimize(AST_TemplateString, function(self, compressor) {
    if (
        !compressor.option("evaluate")
        || AST_PrefixedTemplateString.hasInstance(compressor.parent())
    ) {
        return self;
    }

    var segments = [];
    for (var i = 0; i < self.segments.length; i++) {
        var segment = self.segments[i];
        if (AST_Node.hasInstance(segment)) {
            var result = segment.evaluate(compressor);
            // Evaluate to constant value
            // Constant value shorter than ${segment}
            if (result !== segment && (result + "").length <= segment.size() + "${}".length) {
                // There should always be a previous and next segment if segment is a node
                segments[segments.length - 1].value = segments[segments.length - 1].value + result + self.segments[++i].value;
                continue;
            }
            // `before ${`innerBefore ${any} innerAfter`} after` => `before innerBefore ${any} innerAfter after`
            // TODO:
            // `before ${'test' + foo} after` => `before innerBefore ${any} innerAfter after`
            // `before ${foo + 'test} after` => `before innerBefore ${any} innerAfter after`
            if (AST_TemplateString.hasInstance(segment)) {
                var inners = segment.segments;
                segments[segments.length - 1].value += inners[0].value;
                for (var j = 1; j < inners.length; j++) {
                    segment = inners[j];
                    segments.push(segment);
                }
                continue;
            }
        }
        segments.push(segment);
    }
    self.segments = segments;

    // `foo` => "foo"
    if (segments.length == 1) {
        return make_node(AST_String, self, segments[0]);
    }

    if (
        segments.length === 3
        && AST_Node.hasInstance(segments[1])
        && (
            segments[1].is_string(compressor)
            || segments[1].is_number(compressor)
            || is_nullish(segments[1], compressor)
            || compressor.option("unsafe")
        )
    ) {
        // `foo${bar}` => "foo" + bar
        if (segments[2].value === "") {
            return make_node(AST_Binary, self, {
                operator: "+",
                left: make_node(AST_String, self, {
                    value: segments[0].value,
                }),
                right: segments[1],
            });
        }
        // `${bar}baz` => bar + "baz"
        if (segments[0].value === "") {
            return make_node(AST_Binary, self, {
                operator: "+",
                left: segments[1],
                right: make_node(AST_String, self, {
                    value: segments[2].value,
                }),
            });
        }
    }
    return self;
});

def_optimize(AST_PrefixedTemplateString, function(self) {
    return self;
});

// ["p"]:1 ---> p:1
// [42]:1 ---> 42:1
function lift_key(self, compressor) {
    if (!compressor.option("computed_props")) return self;
    // save a comparison in the typical case
    if (!AST_Constant.hasInstance(self.key)) return self;
    // allow certain acceptable props as not all AST_Constants are true constants
    if (AST_String.hasInstance(self.key) || AST_Number.hasInstance(self.key)) {
        if (self.key.value === "__proto__") return self;
        if (self.key.value == "constructor"
            && AST_Class.hasInstance(compressor.parent())) return self;
        if (AST_ObjectKeyVal.hasInstance(self)) {
            self.key = self.key.value;
        } else if (AST_ClassProperty.hasInstance(self)) {
            self.key = make_node(AST_SymbolClassProperty, self.key, {
                name: self.key.value
            });
        } else {
            self.key = make_node(AST_SymbolMethod, self.key, {
                name: self.key.value
            });
        }
    }
    return self;
}

def_optimize(AST_ObjectProperty, lift_key);

def_optimize(AST_ConciseMethod, function(self, compressor) {
    lift_key(self, compressor);
    // p(){return x;} ---> p:()=>x
    if (compressor.option("arrows")
        && AST_Object.hasInstance(compressor.parent())
        && !self.is_generator
        && !self.value.uses_arguments
        && !self.value.pinned()
        && self.value.body.length == 1
        && AST_Return.hasInstance(self.value.body[0])
        && self.value.body[0].value
        && !self.value.contains_this()) {
        var arrow = make_node(AST_Arrow, self.value, self.value);
        arrow.async = self.async;
        arrow.is_generator = self.is_generator;
        return make_node(AST_ObjectKeyVal, self, {
            key: AST_SymbolMethod.hasInstance(self.key) ? self.key.name : self.key,
            value: arrow,
            quote: self.quote,
        });
    }
    return self;
});

def_optimize(AST_ObjectKeyVal, function(self, compressor) {
    lift_key(self, compressor);
    // p:function(){} ---> p(){}
    // p:function*(){} ---> *p(){}
    // p:async function(){} ---> async p(){}
    // p:()=>{} ---> p(){}
    // p:async()=>{} ---> async p(){}
    var unsafe_methods = compressor.option("unsafe_methods");
    if (unsafe_methods
        && compressor.option("ecma") >= 2015
        && (!(unsafe_methods instanceof RegExp) || unsafe_methods.test(self.key + ""))) {
        var key = self.key;
        var value = self.value;
        var is_arrow_with_block = AST_Arrow.hasInstance(value)
            && Array.isArray(value.body)
            && !value.contains_this();
        if ((is_arrow_with_block || AST_Function.hasInstance(value)) && !value.name) {
            return make_node(AST_ConciseMethod, self, {
                async: value.async,
                is_generator: value.is_generator,
                key: AST_Node.hasInstance(key) ? key : make_node(AST_SymbolMethod, self, {
                    name: key,
                }),
                value: make_node(AST_Accessor, value, value),
                quote: self.quote,
            });
        }
    }
    return self;
});

def_optimize(AST_Destructuring, function(self, compressor) {
    if (compressor.option("pure_getters") == true
        && compressor.option("unused")
        && !self.is_array
        && Array.isArray(self.names)
        && !is_destructuring_export_decl(compressor)
        && !AST_Expansion.hasInstance(self.names[self.names.length - 1])) {
        var keep = [];
        for (var i = 0; i < self.names.length; i++) {
            var elem = self.names[i];
            if (!(AST_ObjectKeyVal.hasInstance(elem)
                && typeof elem.key == "string"
                && AST_SymbolDeclaration.hasInstance(elem.value)
                && !should_retain(compressor, elem.value.definition()))) {
                keep.push(elem);
            }
        }
        if (keep.length != self.names.length) {
            self.names = keep;
        }
    }
    return self;

    function is_destructuring_export_decl(compressor) {
        var ancestors = [/^VarDef$/, /^(Const|Let|Var)$/, /^Export$/];
        for (var a = 0, p = 0, len = ancestors.length; a < len; p++) {
            var parent = compressor.parent(p);
            if (!parent) return false;
            if (a === 0 && parent.TYPE == "Destructuring") continue;
            if (!ancestors[a].test(parent.TYPE)) {
                return false;
            }
            a++;
        }
        return true;
    }

    function should_retain(compressor, def) {
        if (def.references.length) return true;
        if (!def.global) return false;
        if (compressor.toplevel.vars) {
             if (compressor.top_retain) {
                 return compressor.top_retain(def);
             }
             return false;
        }
        return true;
    }
});

export {
    Compressor,
};
