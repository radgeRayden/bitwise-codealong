using import struct
using import enum
using import String
using import Array
using import Box

spice prefix:c (str)
    str as:= string
    let c = (str @ 0)
    `c

run-stage;

enum TokenKind
    UnMinus
    UnBitNeg
    Mul
    Div
    Mod
    LShift
    RShift
    BitAnd
    BitOr
    BitXor
    Plus
    Minus
    Literal : i32
    Undefined

    fn __tostring (self)
        dispatch self
        case UnMinus ()
            "-"
        case UnBitNeg ()
            "~"
        case Mul ()
            "*"
        case Div ()
            "/"
        case Mod ()
            "%"
        case LShift ()
            "<<"
        case RShift ()
            ">>"
        case BitAnd ()
            "&"
        case BitOr ()
            "|"
        case BitXor ()
            "^"
        case Plus ()
            "+"
        case Minus ()
            "-"
        case Literal (value)
            tostring value
        default
            repr self

    fn precedence (self)
        'apply self
            inline (T self)
                static-if (T.Name == 'Undefined)
                    1000
                else
                    if (T.Literal < 2)
                        3
                    elseif (T.Literal < 8)
                        2
                    elseif (T.Literal < 12)
                        1
                    else
                        0

enum TokenizerState plain
    Whitespace
    SeenMinus # has to decide whether unary minus or subtraction expr
    SeenShl
    SeenShr
    MultiCharOp
    Literal

fn tokenize (input)
    let expr-length = (countof input)
    local tokens : (Array TokenKind)
    local current-literal : i32
    fold (state = TokenizerState.Whitespace) for idx in (range (expr-length + 1))
        inline close-literal ()
            if (state == TokenizerState.Literal)
                'append tokens (TokenKind.Literal current-literal)
                current-literal = 0

        inline simple-op (op)
            close-literal;
            'append tokens (op)
            TokenizerState.Whitespace

        if (idx == expr-length)
            close-literal;
            break state

        let c = (input @ idx)

        switch c
        case c" "
            if (state == TokenizerState.SeenMinus)
                # just a regular binary minus
                'append tokens (TokenKind.Minus)
            close-literal;
            TokenizerState.Whitespace
        pass c"0"
        pass c"1"
        pass c"2"
        pass c"3"
        pass c"4"
        pass c"5"
        pass c"6"
        pass c"7"
        pass c"8"
        pass c"9"
        do
            if (state == TokenizerState.SeenMinus)
                'append tokens (TokenKind.UnMinus)
            current-literal *= 10
            current-literal += (c - 48:i8)
            TokenizerState.Literal
        case c"-"
            if (state == TokenizerState.Whitespace)
                TokenizerState.SeenMinus
            else
                close-literal;
                'append tokens (TokenKind.Minus)
                TokenizerState.Whitespace
        case c"+"
            simple-op TokenKind.Plus
        case c"*"
            simple-op TokenKind.Mul
        case c"/"
            simple-op TokenKind.Div
        case c"%"
            simple-op TokenKind.Mod
        case c"~"
            simple-op TokenKind.UnBitNeg
        case c"<"
            if (state == TokenizerState.SeenShl)
                'append tokens (TokenKind.LShift)
                TokenizerState.Whitespace
            else
                TokenizerState.SeenShl

        case c">"
            if (state == TokenizerState.SeenShr)
                'append tokens (TokenKind.RShift)
                TokenizerState.Whitespace
            else
                TokenizerState.SeenShr
        case c"&"
            simple-op TokenKind.BitAnd
        case c"|"
            simple-op TokenKind.BitOr
        case c"^"
            simple-op TokenKind.BitXor
        default
            hide-traceback;
            error (.. "invalid character at position " (tostring idx) ": " (repr (string &c 1)))
    tokens

struct ASTNode
enum NodeKind
    Token : TokenKind
    SubExpr : (Box ASTNode)

struct ASTNode
    leaves : (Array NodeKind)

    fn __repr (self)
        returning string
        fold (result = "") for idx leaf in (enumerate self.leaves)
            .. result
                dispatch leaf
                case SubExpr (node)
                    .. "(" (tostring node) ")"
                case Token (tk)
                    tostring tk
                default
                    unreachable;
                if (idx < ((countof self.leaves) - 1))
                    " "
                else
                    ""

typedef+ (Box ASTNode)
    inline __repr (self)
        ASTNode.__repr self

fn build-AST (tokens)
    returning (uniqueof NodeKind -1)

    # note the TokenKind enum is sorted by precedence rules
    # find lowest precedence operator
    let idx lowest =
        fold (lowest-idx lowest-op = 0 (TokenKind.Undefined)) for idx tk in (enumerate tokens)
            let prec = ('precedence tk)
            let prev-prec = ('precedence lowest-op)
            # because of left associativity
            if (prec == prev-prec)
                _ idx (dupe (deref tk))
            if (and
                    (('precedence tk) < ('precedence lowest-op))
                    (('literal tk) != TokenKind.Literal.Literal))

                _ idx (dupe (deref tk))
            else
                _ lowest-idx lowest-op

    if (idx == 0)
        dispatch lowest
        # for the unary case, it assumes the op is first on the list and there's
        # a single postfix, ie. the expr is well formed.
        case UnMinus ()
            local expr : ASTNode
            'append expr.leaves (NodeKind.Token lowest)
            'append expr.leaves (NodeKind.Token (dupe (deref (tokens @ (idx + 1)))))
            NodeKind.SubExpr (Box.wrap (deref expr))
        case UnBitNeg ()
            local expr : ASTNode
            'append expr.leaves (NodeKind.Token lowest)
            'append expr.leaves (NodeKind.Token (dupe (deref (tokens @ (idx + 1)))))
            NodeKind.SubExpr (Box.wrap (deref expr))
        default
            # literal
            NodeKind.Token (dupe (deref (tokens @ 0)))
    elseif (idx == ((countof tokens) - 1))
        local AST : ASTNode
        for tk in tokens
            'append AST.leaves (NodeKind.Token (dupe tk))
        NodeKind.SubExpr (Box.wrap (deref AST))
    else
        local root : ASTNode
        local lhs : (Array TokenKind)
        local rhs : (Array TokenKind)
        'append root.leaves (NodeKind.Token lowest)
        for i in (range idx)
            'append lhs (dupe (deref (tokens @ i)))
        for i in (range (idx + 1) (countof tokens))
            'append rhs (dupe (deref (tokens @ i)))
        'append root.leaves (this-function lhs)
        'append root.leaves (this-function rhs)
        NodeKind.SubExpr (Box.wrap (deref root))

fn parse (input)
    print input
    build-AST (tokenize input)

do
    let AST = (parse (String "12*34 + -45/~56 + 25 * 28 >> 4 - 324 << 8"))
    'apply AST
        (T self) -> (print (.. "(" (repr self) ")"))
    let AST = (parse (String "12*34 + 45/56 + ~25"))
    'apply AST
        (T self) -> (print (.. "(" (repr self) ")"))
    ;
