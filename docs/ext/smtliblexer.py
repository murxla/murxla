from pygments.lexer import RegexLexer
from pygments import token


class SmtLibLexer(RegexLexer):
    """A lexer for SMT-LIBv2.
    """

    name = 'smtlib'

    COMMANDS = [
        'assert', 'check-sat', 'check-sat-assuming', 'declare-const',
        'declare-datatype', 'declare-datatypes', 'declare-codatatypes',
        'declare-fun', 'declare-sort', 'define-fun', 'define-fun-rec',
        'define-funs-rec', 'define-sort', 'echo', 'exit', 'get-info',
        'get-model', 'get-option', 'get-proof', 'get-unsat-assumptions',
        'get-unsat-core', 'get-value', 'pop', 'push', 'reset',
        'reset-assertions', 'set-info', 'set-logic', 'set-option',
    ]
    SORTS = [
        'Array', 'Bag', 'BitVec', 'Bool', 'FloatingPoint', 'Float[0-9]+',
        'Int', 'Real', 'RegLan', 'RoundingMode', 'Set', 'String'
    ]
    OPERATORS = [
        # array
        'select', 'store',
        # bv
        'concat', 'extract', 'repeat', 'zero_extend', 'sign_extend',
        'rotate_left', 'rotate_right', 'bvnot', 'bvand', 'bvor', 'bvneg',
        'bvadd', 'bvmul', 'bvudiv', 'bvurem', 'bvshl', 'bvlshr', 'bvult',
        'bvnand', 'bvnor', 'bvxor', 'bvxnor', 'bvcomp', 'bvsub', 'bvsdiv',
        'bvsrem', 'bvsmod', 'bvashr', 'bvule', 'bvugt', 'bvuge', 'bvslt',
        'bvsle', 'bvsgt', 'bvsge',
        # core
        '=>', '=', 'true', 'false', 'not', 'and', 'or', 'xor', 'distinct',
        'ite',
        # fp
        'RNE', 'RNA', 'RTP', 'RTN', 'RTZ', 'fp', 'NaN', 'fp\.abs', 'fp\.neg',
        'fp\.add', 'fp\.sub', 'fp\.mul', 'fp\.div', 'fp\.fma', 'fp\.sqrt',
        'fp\.rem', 'fp\.roundToIntegral', 'fp\.min', 'fp\.max', 'fp\.leq',
        'fp\.lt', 'fp\.geq', 'fp\.gt', 'fp\.eq', 'fp\.isNormal',
        'fp\.isSubnormal', 'fp\.isZero', 'fp\.isInfinite', 'fp\.isNaN',
        'fp\.isNegative', 'fp\.isPositive', 'to_fp', 'to_fp_unsigned',
        'fp\.to_ubv', 'fp\.to_sbv', 'fp\.to_real', '\+oo', '-oo', '\+zero',
        '-zero',
        # int / real
        '<', '>', '<=', '>=', '!=', '\+', '-', '\*', '/', 'div', 'mod', 'abs',
        'divisible', 'to_real', 'to_int', 'is_int',
        # string
        'char', 'str\.\+\+', 'str\.len', 'str\.<', 'str\.to_re', 'str\.in_re',
        're\.none', 're\.all', 're\.allchar', 're\.comp', 're\.concat',
        're\.\^', 're\.\+\+', 're\.union', 're\.inter', 're\.\*', 'str\.<=',
        'str\.at', 'str\.substr',
        'str\.prefixof', 'str\.suffixof', 'str\.contains', 'str\.indexof',
        'str\.replace', 'str\.replace_all', 'str\.replace_re',
        'str\.replace_re_all', 're\.comp', 're\.diff', 're\.\+', 're\.opt',
        're\.range', 're\.^', 're\.loop', 'str\.is_digit', 'str\.to_code',
        'str\.from_code', 'str\.to_int', 'str\.from_int',
    ]

    tokens = {
        'root': [
            # comment (see lexicon)
            (r';.*$', token.Comment),
            # whitespace
            (r'\s+', token.Text),
            # numeral (decimal, hexadecimal, binary, see lexicon)
            (r'[0-9]+', token.Number),
            (r'#x[0-9a-fA-F]+', token.Number),
            (r'#b[01]+', token.Number),
            # bv constant (see BV theory specification)
            (r'bv[0-9]+', token.Number),
            # string constant (including escaped "", see lexicon)
            (r'".*?"', token.String),
            # reserved words (non-word and regular, see lexicon)
            (r'[!_](?=\s)', token.Name.Attribute),
            ('(as|let|exists|forall|match|per)\\b', token.Keyword),
            # Keywords (:foo, see lexicon)
            (r':[a-zA-Z~!@$%^&*_+=<>.?/-][a-zA-Z0-9~!@$%^&*_+=<>.?/-]*',
             token.Name.Attribute),
            # parentheses
            (r'\(', token.Text),
            (r'\)', token.Text),
            (r'\{', token.Text),
            (r'\}', token.Text),
            # commands (terminated by whitespace or ")")
            ('(' + '|'.join(COMMANDS) + ')(?=(\s|\)))', token.Keyword),
            # sorts (terminated by whitespace or ")")
            ('(' + '|'.join(SORTS) + ')(?=(\s|\)))', token.Name.Attribute),
            # operators (terminated by whitespace or ")")
            ('(' + '|'.join(OPERATORS) + ')(?=(\s|\)))', token.Operator),
            # symbols (regular and quoted, see lexicon)
            (r'[a-zA-Z~!@$%^&*_+=<>.?/-][a-zA-Z0-9~!@$%^&*_+=<>.?/-]*', token.Name),
            (r'\|[^|\\]*\|', token.Name),
        ],
    }
