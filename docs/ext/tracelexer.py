from pygments.lexer import RegexLexer
from pygments import token


class TraceLexer(RegexLexer):
    """A lexer for Murxla's trace format.
    """

    name = 'trace'

    COMMANDS = [
        'check-sat', 'check-sat-assuming', 'get-unsat-assumptions',
        'get-unsat-core', 'get-value', 'mk-const', 'mk-sort', 'mk-term',
        'mk-value', 'mk-special-value', 'new', 'pop', 'push', 'reset',
        'reset-assertions', 'return', 'set-logic', 'set-murxla-options',
        'set-option',
    ]

    tokens = {
        'root': [
            # comment (see lexicon)
            (r';.*$', token.Comment),
            # whitespace
            (r'\s+', token.Text),
            # numeral (decimal, hexadecimal, binary, see lexicon)
            (r'[0-9]+', token.Number),
            # string constant (including escaped "", see lexicon)
            (r'".*?"', token.String),
            # reserved words (non-word and regular, see lexicon)
            (r'[!_](?=\s)', token.Name.Attribute),
            # commands (terminated by whitespace)
            ('(' + '|'.join(COMMANDS) + ')(?=\s)', token.Keyword),
            # sorts
            (r'SORT_.*?\s', token.Name.Attribute),
            # operators
            (r'OP_.*?\s', token.Operator),
            # symbols (regular and quoted, see lexicon)
            (r'[a-zA-Z~!@$%^&*_+=<>.?/-][a-zA-Z0-9~!@$%^&*_+=<>.?/-]*', token.Name),
            (r'\|[^|\\]*\|', token.Name),
            # text
            (r'(\(.*\))', token.Text),
            (r'(\[.*\].*$)', token.Text),
        ],
    }
