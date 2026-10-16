//  Recursive-Descent Compiler - PROJECT REVIEW 2  (BCSE307P Compiler Design Lab)
//
//  Phases   : lexical analysis -> recursive-descent parsing (with syntax-directed
//             semantic checks and three-address code) in a single pass
//  Features : panic-mode error recovery, symbol table, semantic checks,
//             type inference, constant folding, warnings, parse trace,
//             "did you mean" suggestions (novelty)
//
//  Grammar (LL(1), unchanged from Review 1)
//  ----------------------------------------
//    program    -> { statement } EOF
//    statement  -> declaration | assignment
//    declaration-> type declarator { ',' declarator } ';'
//    declarator -> ID [ '=' expr ]
//    type       -> 'int' | 'float'
//    assignment -> ID '=' expr ';'
//    expr       -> term   { ('+' | '-') term }
//    term       -> factor { ('*' | '/' | '%') factor }
//    factor     -> ('+' | '-') factor | primary
//    primary    -> INT_LIT | FLOAT_LIT | ID | '(' expr ')'
//
//  Build : g++ -std=c++17 -Wall -Wextra -o compiler compiler.cpp
//  Run   : ./compiler file.txt [--tokens] [--trace] [--no-fold]
// ============================================================================
#include <algorithm>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
 
// ----------------------------------------------------------------- tokens ---
enum class T {
    KW_INT, KW_FLOAT, ID, INT_LIT, FLOAT_LIT,
    ASSIGN, PLUS, MINUS, STAR, SLASH, PERCENT,
    LPAREN, RPAREN, SEMI, COMMA, END
};
enum class Type { Int, Float };
 
struct Token { T type; string lexeme; int line, col; };
struct Diag  { string kind; string msg; int line, col; string hint; };
 
static const char* tokName(T t) {
    static const char* n[] = {"KW_INT","KW_FLOAT","ID","INT_LIT","FLOAT_LIT","ASSIGN","PLUS","MINUS",
                              "STAR","SLASH","PERCENT","LPAREN","RPAREN","SEMI","COMMA","EOF"};
    return n[(int)t];
}
static const char* typeName(Type t) { return t == Type::Int ? "int" : "float"; }
 
// ----------------------------------------------- "did you mean" (novelty) ---
static string lower(string s) { for (auto& c : s) c = (char)tolower((unsigned char)c); return s; }
 
// Optimal-string-alignment distance: insert, delete, substitute, and swap of two
// adjacent characters each cost 1 (so "flaot" -> "float" has distance 1).
static int editDistance(const string& a, const string& b) {
    size_t n = a.size(), m = b.size();
    vector<vector<int>> d(n + 1, vector<int>(m + 1));
    for (size_t i = 0; i <= n; i++) d[i][0] = (int)i;
    for (size_t j = 0; j <= m; j++) d[0][j] = (int)j;
    for (size_t i = 1; i <= n; i++)
        for (size_t j = 1; j <= m; j++) {
            int cost = a[i - 1] == b[j - 1] ? 0 : 1;
            d[i][j] = min({d[i - 1][j] + 1, d[i][j - 1] + 1, d[i - 1][j - 1] + cost});
            if (i > 1 && j > 1 && a[i - 1] == b[j - 2] && a[i - 2] == b[j - 1])
                d[i][j] = min(d[i][j], d[i - 2][j - 2] + 1);
        }
    return d[n][m];
}
 
// Best candidate within the threshold, or "" if nothing is close enough.
// Threshold: 1 edit for names of up to 3 letters, otherwise 2; the distance must also
// be smaller than the name length, so one-letter names never get suggestions.
// Ties are resolved in favour of the candidate that comes first in the list.
static string closestMatch(const string& name, const vector<string>& candidates) {
    string best; int bestD = 1000;
    string ln = lower(name);
    int limit = name.size() <= 3 ? 1 : 2;
    for (auto& c : candidates) {
        if (c == name) continue;
        int d = editDistance(ln, lower(c));
        if (d <= limit && d < (int)name.size() && d < bestD) { bestD = d; best = c; }
    }
    return best;
}
 
// ------------------------------------------------------------------ lexer ---
static vector<Token> lex(const string& src, vector<Diag>& diags) {
    vector<Token> out;
    size_t i = 0;
    int line = 1, col = 1;
    auto peek = [&](size_t k = 0) -> char { return i + k < src.size() ? src[i + k] : '\0'; };
    auto adv  = [&]() { if (src[i] == '\n') { line++; col = 1; } else col++; i++; };
    auto isIdStart = [](char c) { return isalpha((unsigned char)c) || c == '_'; };
    auto isIdChar  = [](char c) { return isalnum((unsigned char)c) || c == '_'; };
 
    while (i < src.size()) {
        char c = peek();
        if (isspace((unsigned char)c)) { adv(); continue; }
 
        if (c == '/' && peek(1) == '/') { while (i < src.size() && peek() != '\n') adv(); continue; }
        if (c == '/' && peek(1) == '*') {
            int sl = line, sc = col; adv(); adv();
            bool closed = false;
            while (i < src.size()) {
                if (peek() == '*' && peek(1) == '/') { adv(); adv(); closed = true; break; }
                adv();
            }
            if (!closed) diags.push_back({"Lexical error", "unterminated comment", sl, sc, ""});
            continue;
        }
 
        int sl = line, sc = col;
        if (isIdStart(c)) {
            string s;
            while (isIdChar(peek())) { s += peek(); adv(); }
            T t = s == "int" ? T::KW_INT : s == "float" ? T::KW_FLOAT : T::ID;
            out.push_back({t, s, sl, sc});
            continue;
        }
        if (isdigit((unsigned char)c)) {
            string s; bool isFloat = false, bad = false;
            while (isdigit((unsigned char)peek())) { s += peek(); adv(); }
            if (peek() == '.') {
                isFloat = true; s += '.'; adv();
                if (!isdigit((unsigned char)peek())) bad = true;
                while (isdigit((unsigned char)peek())) { s += peek(); adv(); }
            }
            if (isIdStart(peek())) { while (isIdChar(peek())) { s += peek(); adv(); } bad = true; }
            if (bad) diags.push_back({"Lexical error", "malformed number '" + s + "'", sl, sc, ""});
            out.push_back({isFloat ? T::FLOAT_LIT : T::INT_LIT, s, sl, sc});   // keep going after a bad number
            continue;
        }
        T t; bool ok = true;
        switch (c) {
            case '=': t = T::ASSIGN;  break;
            case '+': t = T::PLUS;    break;
            case '-': t = T::MINUS;   break;
            case '*': t = T::STAR;    break;
            case '/': t = T::SLASH;   break;
            case '%': t = T::PERCENT; break;
            case '(': t = T::LPAREN;  break;
            case ')': t = T::RPAREN;  break;
            case ';': t = T::SEMI;    break;
            case ',': t = T::COMMA;   break;
            default:  t = T::END; ok = false;
        }
        if (ok) out.push_back({t, string(1, c), sl, sc});
        else diags.push_back({"Lexical error", string("unexpected character '") + c + "'", sl, sc, ""});
        adv();
    }
    out.push_back({T::END, "<EOF>", line, col});
    return out;
}
 
// ----------------------------------------------------------------- parser ---
struct SyntaxError { string msg; int line, col; bool missingSemi; string hint; };
 
struct Symbol {
    Type type; bool initialized; int line, col;
    bool used = false;          // read or assigned after its declaration
    bool warnedInit = false;    // "may be uninitialized" reported once
};
 
struct Opd {                    // result of parsing an expression
    string place; Type type;
    bool isConst = false; long long iv = 0; double dv = 0.0;
};
 
static string fmtFloat(double v) {
    char b[64]; snprintf(b, sizeof b, "%.10g", v);
    string s = b;
    if (s.find_first_of(".eEn") == string::npos) s += ".0";
    return s;
}
static Opd constInt(long long v)  { Opd o{to_string(v), Type::Int};  o.isConst = true; o.iv = v; o.dv = (double)v; return o; }
static Opd constFloat(double v)   { Opd o{fmtFloat(v), Type::Float}; o.isConst = true; o.dv = v; o.iv = (long long)v; return o; }
 
class Parser {
public:
    Parser(vector<Token> t, vector<Diag>& d, bool trace, bool fold)
        : toks(std::move(t)), diags(d), tracing(trace), folding(fold) {}
 
    void parseProgram() {
        while (cur().type != T::END) {
            size_t start = p;
            buf.clear();
            try {
                statement();
                for (auto& l : buf) tac.push_back(l);
                okStmts++;
            } catch (SyntaxError& e) {
                errStmts++;
                diags.push_back({"Syntax error", e.msg, e.line, e.col, e.hint});
                bool keepGoing = e.missingSemi && (isStmtStart(cur()) || cur().type == T::END);
                if (!keepGoing) synchronize(start);
            }
        }
    }
    // after parsing: variables that were declared but never referenced.
    // Skipped when earlier errors may have hidden the uses (avoids misleading warnings).
    void finish(bool lexicalErrors) {
        if (lexicalErrors || errStmts > 0) return;
        for (auto& n : order)
            if (!sym[n].used)
                diags.push_back({"Warning", "'" + n + "' is declared but never used", sym[n].line, sym[n].col, ""});
    }
 
    const vector<string>& code() const { return tac; }
    const map<string, Symbol>& symbols() const { return sym; }
    const vector<string>& symbolOrder() const { return order; }
    int statementsOk() const { return okStmts; }
    int statementsFailed() const { return errStmts; }
    int foldedCount() const { return folded; }
 
private:
    vector<Token> toks;
    size_t p = 0;
    vector<Diag>& diags;
    map<string, Symbol> sym;
    vector<string> order;
    vector<string> tac, buf;
    int tmpN = 0, okStmts = 0, errStmts = 0, folded = 0;
    bool tracing, folding;
    int depth = 0;
 
    // ---- trace support: prints each grammar rule as it is entered
    struct Scope {
        Parser& P;
        Scope(Parser& parser, const char* rule) : P(parser) {
            if (P.tracing) cout << string(P.depth * 2, ' ') << rule << "   [next: " << desc(P.cur()) << "]\n";
            P.depth++;
        }
        ~Scope() { P.depth--; }
    };
 
    // ---- helpers
    const Token& cur() const { return toks[p]; }
    static bool isStmtStart(const Token& t) {
        return t.type == T::KW_INT || t.type == T::KW_FLOAT || t.type == T::ID;
    }
    static string desc(const Token& t) {
        return t.type == T::END ? "end of file" : "'" + t.lexeme + "'";
    }
    bool accept(T t) { if (cur().type == t) { p++; return true; } return false; }
 
    Token expect(T t, const string& what) {
        if (cur().type == t) return toks[p++];
        if (t == T::SEMI && p > 0) {                 // report at end of previous token
            const Token& pv = toks[p - 1];
            throw SyntaxError{"expected ';' after '" + pv.lexeme + "', found " + desc(cur()),
                              pv.line, pv.col + (int)pv.lexeme.size(), true, ""};
        }
        throw SyntaxError{"expected " + what + ", found " + desc(cur()), cur().line, cur().col, false, ""};
    }
 
    // Panic-mode recovery: skip to just after ';' or to the next type keyword.
    // 'start' guarantees progress: a keyword only stops the skip if we already moved past it.
    void synchronize(size_t start) {
        while (cur().type != T::END) {
            if (cur().type == T::SEMI) { p++; return; }
            if ((cur().type == T::KW_INT || cur().type == T::KW_FLOAT) && p > start) return;
            p++;
        }
    }
 
    void semantic(const string& kind, const string& msg, const Token& at, const string& hint = "") {
        diags.push_back({kind, msg, at.line, at.col, hint});
    }
    string newTemp() { return "t" + to_string(++tmpN); }
 
    // ---- "did you mean" helpers
    string suggestType(const string& name) { return closestMatch(name, {"int", "float"}); }
    void reportUndeclared(const Token& id) {
        string s = closestMatch(id.lexeme, order);
        semantic("Semantic error", "'" + id.lexeme + "' is not declared", id,
                 s.empty() ? "" : "did you mean '" + s + "'?");
    }
 
    // ---- grammar rules
    void statement() {
        Scope sc(*this, "statement");
        if (cur().type == T::KW_INT || cur().type == T::KW_FLOAT) { declaration(); return; }
        if (cur().type == T::ID) {
            // Two identifiers in a row ("flaot x") can only be a misspelt type name.
            if (toks[p + 1].type == T::ID) {
                string s = suggestType(cur().lexeme);
                if (!s.empty()) {
                    // report it, then carry on as if the type had been spelt correctly,
                    // so the rest of the statement is still checked (no cascade of errors)
                    diags.push_back({"Syntax error", "unknown type '" + cur().lexeme + "'",
                                     cur().line, cur().col, "did you mean '" + s + "'?"});
                    p++;
                    declarationRest(s == "int" ? Type::Int : Type::Float);
                    return;
                }
            }
            assignment();
            return;
        }
        throw SyntaxError{"expected a declaration or assignment, found " + desc(cur()),
                          cur().line, cur().col, false, ""};
    }
 
    void declaration() {
        Scope sc(*this, "declaration");
        Type ty = cur().type == T::KW_INT ? Type::Int : Type::Float;
        p++;
        declarationRest(ty);
    }
 
    void declarationRest(Type ty) {
        do {
            Token id = expect(T::ID, "identifier");
            Opd init; bool has = false;
            if (accept(T::ASSIGN)) { init = expr(); has = true; }
 
            if (sym.count(id.lexeme))
                semantic("Semantic error", "redeclaration of '" + id.lexeme + "' (first declared on line " +
                                               to_string(sym[id.lexeme].line) + ")", id);
            else {
                sym[id.lexeme] = {ty, has, id.line, id.col};
                order.push_back(id.lexeme);
            }
            if (has) {
                if (ty == Type::Int && init.type == Type::Float)
                    semantic("Warning", "implicit float -> int conversion in initializer of '" + id.lexeme + "'", id);
                buf.push_back(id.lexeme + " = " + init.place);
            }
        } while (accept(T::COMMA));
        expect(T::SEMI, "';'");
    }
 
    void assignment() {
        Scope sc(*this, "assignment");
        Token id = toks[p++];
        expect(T::ASSIGN, "'='");
        Opd v = expr();
        auto it = sym.find(id.lexeme);
        if (it == sym.end())
            reportUndeclared(id);
        else {
            if (it->second.type == Type::Int && v.type == Type::Float)
                semantic("Warning", "implicit float -> int conversion when assigning to '" + id.lexeme + "'", id);
            it->second.initialized = true;
            it->second.used = true;
        }
        buf.push_back(id.lexeme + " = " + v.place);
        expect(T::SEMI, "';'");
    }
 
    static bool isZero(const Opd& o) { return o.type == Type::Int ? o.iv == 0 : o.dv == 0.0; }
 
    Opd binary(const Token& op, const Opd& l, const Opd& r) {
        Type rt = (l.type == Type::Float || r.type == Type::Float) ? Type::Float : Type::Int;
        bool bad = false;
        if (op.type == T::PERCENT && rt == Type::Float) {
            semantic("Semantic error", "operator '%' requires integer operands", op); bad = true;
        }
        if (!bad && r.isConst && isZero(r) && (op.type == T::SLASH || op.type == T::PERCENT)) {
            semantic("Semantic error", op.type == T::SLASH ? "division by zero" : "modulo by zero", op); bad = true;
        }
        if (folding && !bad && l.isConst && r.isConst) {      // constant folding
            folded++;
            if (rt == Type::Int) {
                long long a = l.iv, b = r.iv, v = 0;
                switch (op.type) {
                    case T::PLUS: v = a + b; break;   case T::MINUS: v = a - b; break;
                    case T::STAR: v = a * b; break;   case T::SLASH: v = a / b; break;
                    default:      v = a % b; break;
                }
                return constInt(v);
            }
            double a = l.type == Type::Float ? l.dv : (double)l.iv;
            double b = r.type == Type::Float ? r.dv : (double)r.iv, v = 0;
            switch (op.type) {
                case T::PLUS: v = a + b; break;   case T::MINUS: v = a - b; break;
                case T::STAR: v = a * b; break;   default: v = a / b; break;
            }
            return constFloat(v);
        }
        string t = newTemp();
        buf.push_back(t + " = " + l.place + " " + op.lexeme + " " + r.place);
        return {t, rt};
    }
 
    Opd expr() {                               // expr -> term { (+|-) term }
        Scope sc(*this, "expr");
        Opd l = term();
        while (cur().type == T::PLUS || cur().type == T::MINUS) {
            Token op = toks[p++];
            Opd r = term();
            l = binary(op, l, r);
        }
        return l;
    }
 
    Opd term() {                               // term -> factor { (*|/|%) factor }
        Scope sc(*this, "term");
        Opd l = factor();
        while (cur().type == T::STAR || cur().type == T::SLASH || cur().type == T::PERCENT) {
            Token op = toks[p++];
            Opd r = factor();
            l = binary(op, l, r);
        }
        return l;
    }
 
    Opd factor() {                             // factor -> (+|-) factor | primary
        Scope sc(*this, "factor");
        if (cur().type == T::PLUS || cur().type == T::MINUS) {
            Token op = toks[p++];
            Opd o = factor();
            if (op.type != T::MINUS) return o;
            if (folding && o.isConst) { folded++; return o.type == Type::Int ? constInt(-o.iv) : constFloat(-o.dv); }
            string t = newTemp();
            buf.push_back(t + " = -" + o.place);
            return {t, o.type};
        }
        return primary();
    }
 
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
static vector<string> splitLines(const string& s) {
    vector<string> v; string cur;
    for (char c : s) { if (c == '\n') { v.push_back(cur); cur.clear(); } else if (c != '\r') cur += c; }
    v.push_back(cur);
    return v;
}
 
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
