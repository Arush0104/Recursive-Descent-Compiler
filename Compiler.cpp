            return {t, o.type};
        }
        return primary();
    }
 
    // Parses literals, variable references, or parenthesized expressions—the basic units of an expression.
    Opd primary() {
        Scope sc(*this, "primary");
        const Token& t = cur();
        switch (t.type) {
            case T::INT_LIT:   p++; return constInt(strtoll(t.lexeme.c_str(), nullptr, 10));
            case T::FLOAT_LIT: p++; return constFloat(strtod(t.lexeme.c_str(), nullptr));
            case T::ID: {
                Token id = toks[p++];
                auto it = sym.find(id.lexeme);
                if (it == sym.end()) { reportUndeclared(id); return {id.lexeme, Type::Int}; }
                it->second.used = true;
                if (!it->second.initialized && !it->second.warnedInit) {
                    semantic("Warning", "'" + id.lexeme + "' may be used before it is initialized", id);
                    it->second.warnedInit = true;
                }
                return {id.lexeme, it->second.type};
            }
            case T::LPAREN: {
                p++;
                Opd e = expr();
                expect(T::RPAREN, "')'");
                return e;
            }
            default:
                throw SyntaxError{"expected an expression, found " + desc(t), t.line, t.col, false, ""};
        }
    }
};
 
// ------------------------------------------------------------------- main ---
// Splits the original source into lines so diagnostics can print the relevant line and caret.
static vector<string> splitLines(const string& s) {
    vector<string> v; string cur;
    for (char c : s) { if (c == '\n') { v.push_back(cur); cur.clear(); } else if (c != '\r') cur += c; }
    v.push_back(cur);
    return v;
}
 
// MAIN: reads options and source code, runs lexing and parsing, then prints diagnostics and compiler results.
int main(int argc, char** argv) {
    string path; bool showTokens = false, trace = false, fold = true;
    for (int i = 1; i < argc; i++) {
        string a = argv[i];
        if (a == "--tokens") showTokens = true;
        else if (a == "--trace") trace = true;
        else if (a == "--no-fold") fold = false;
        else path = a;
    }
 
    string src;
    if (!path.empty()) {
        ifstream f(path);
        if (!f) { cerr << "Cannot open file: " << path << "\n"; return 2; }
        stringstream ss; ss << f.rdbuf(); src = ss.str();
    } else {
        cerr << "(no file given - type source, finish with Ctrl+D on Linux/Mac or Ctrl+Z then Enter on Windows)\n";
        stringstream ss; ss << cin.rdbuf(); src = ss.str();
    }
 
    vector<Diag> diags;
    vector<Token> toks = lex(src, diags);
 
    if (showTokens) {
        cout << "---- TOKENS ----\n";
        for (auto& t : toks)
            cout << left << setw(6) << (to_string(t.line) + ":" + to_string(t.col))
                 << setw(11) << tokName(t.type) << t.lexeme << "\n";
        cout << "\n";
    }
    if (trace) cout << "---- PARSE TRACE ----\n";
 
    Parser parser(toks, diags, trace, fold);
    bool lexicalErrors = !diags.empty();                 // only lexical errors exist at this point
    parser.parseProgram();
    parser.finish(lexicalErrors);
    if (trace) cout << "\n";
 
    {   // a syntax error on the same line as a lexical error is usually caused by it
        vector<int> lexLines;
        for (auto& d : diags) if (d.kind == "Lexical error") lexLines.push_back(d.line);
        diags.erase(remove_if(diags.begin(), diags.end(), [&](const Diag& d) {
            return d.kind == "Syntax error" && find(lexLines.begin(), lexLines.end(), d.line) != lexLines.end();
        }), diags.end());
    }
    stable_sort(diags.begin(), diags.end(), [](const Diag& a, const Diag& b) {
        return a.line != b.line ? a.line < b.line : a.col < b.col;
    });
 
    vector<string> lines = splitLines(src);
    int errors = 0, warnings = 0;
    for (auto& d : diags) {
        (d.kind == "Warning" ? warnings : errors)++;
        cout << d.kind << " [" << d.line << ":" << d.col << "]: " << d.msg << "\n";
        if (d.line >= 1 && d.line <= (int)lines.size()) {
            cout << "  " << setw(4) << d.line << " | " << lines[d.line - 1] << "\n";
            cout << "       | " << string(max(0, d.col - 1), ' ') << "^\n";
        }
        if (!d.hint.empty()) cout << "       = hint: " << d.hint << "\n";
    }
 
    if (errors == 0) {
        cout << "\nCompilation successful (" << warnings << " warning(s)).\n";
        cout << "\n---- SYMBOL TABLE ----\n";
        cout << left << setw(12) << "Name" << setw(8) << "Type" << "Declared (line)\n";
        for (auto& n : parser.symbolOrder()) {
            const Symbol& s = parser.symbols().at(n);
            cout << left << setw(12) << n << setw(8) << typeName(s.type) << s.line << "\n";
        }
        cout << "\n---- THREE-ADDRESS CODE ----\n";
        int k = 1;
        for (auto& l : parser.code()) cout << right << setw(3) << k++ << ": " << l << "\n";
        cout << "\nStatements: " << parser.statementsOk() << "   Constant expressions folded: "
             << parser.foldedCount() << "\n";
        return 0;
    }
    cout << "\nCompilation failed: " << errors << " error(s), " << warnings << " warning(s).\n";
    cout << "Statements: " << parser.statementsOk() << " parsed, " << parser.statementsFailed()
         << " skipped after a syntax error.\n";
    return 1;
}
