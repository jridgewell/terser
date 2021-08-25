import {
    AST_Binary,
    AST_Conditional,
    AST_Dot,
    AST_Object,
    AST_Sequence,
    AST_Statement,
    AST_Sub,
    AST_UnaryPostfix,
    AST_PrefixedTemplateString
} from "../ast.js";

// return true if the node at the top of the stack (that means the
// innermost node in the current output) is lexically the first in
// a statement.
function first_in_statement(stack) {
    let node = stack.parent(-1);
    for (let i = 0, p; p = stack.parent(i); i++) {
        if (AST_Statement.hasInstance(p) && p.body === node)
            return true;
        if ((AST_Sequence.hasInstance(p) && p.expressions[0] === node) ||
            (p.TYPE === "Call" && p.expression === node) ||
            (AST_PrefixedTemplateString.hasInstance(p) && p.prefix === node) ||
            (AST_Dot.hasInstance(p) && p.expression === node) ||
            (AST_Sub.hasInstance(p) && p.expression === node) ||
            (AST_Conditional.hasInstance(p) && p.condition === node) ||
            (AST_Binary.hasInstance(p) && p.left === node) ||
            (AST_UnaryPostfix.hasInstance(p) && p.expression === node)
        ) {
            node = p;
        } else {
            return false;
        }
    }
}

// Returns whether the leftmost item in the expression is an object
function left_is_object(node) {
    if (AST_Object.hasInstance(node)) return true;
    if (AST_Sequence.hasInstance(node)) return left_is_object(node.expressions[0]);
    if (node.TYPE === "Call") return left_is_object(node.expression);
    if (AST_PrefixedTemplateString.hasInstance(node)) return left_is_object(node.prefix);
    if (AST_Dot.hasInstance(node) || AST_Sub.hasInstance(node)) return left_is_object(node.expression);
    if (AST_Conditional.hasInstance(node)) return left_is_object(node.condition);
    if (AST_Binary.hasInstance(node)) return left_is_object(node.left);
    if (AST_UnaryPostfix.hasInstance(node)) return left_is_object(node.expression);
    return false;
}

export { first_in_statement, left_is_object };
