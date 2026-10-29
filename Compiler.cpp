// ============================================================================
//  Recursive-Descent Compiler - FINAL REVIEW  (BCSE307P Compiler Design Lab)
//
//  Phases   : lexical analysis -> recursive-descent parsing (with syntax-directed
//             semantic checks and three-address code) in a single pass -> TAC Interpreter
//  Features : panic-mode error recovery, symbol table, semantic checks,
//             type inference, constant folding, warnings, parse trace,
//             "did you mean" suggestions (novelty), control flow (if/else, while, blocks),
//             and a Three-Address Code (TAC) execution engine with infinite-loop protection
//  Earlier  : * one-dimensional arrays (declaration, initializer lists, indexing,
//               compile-time and run-time bounds checking)
//             * functions (int / float / void, parameters, return, calls, recursion)
//               with a function table and arity / type checks
//             * block scoping: a stack of symbol tables (global -> function -> block),
//               shadowing allowed, inner names get unique TAC names (x, x#2, ...)
//  NEW      : * boolean expressions: '&&', '||', '!' with SHORT-CIRCUIT evaluation
//               (jumps in the TAC), constant folding of boolean expressions, and
//               dead-code removal of operands that can never be evaluated
//             * comparisons are ordinary expressions that produce 0 / 1, so they can
//               be stored (int b = x < 3;), passed, returned and indexed with
//             * a condition is any expression, so if ((x < 3)) and a < b < c parse
//               (comparisons are left-associative, exactly as in C: (a < b) < c)
//             * new TAC instruction  if_true x goto L  (used by '||')
//
//  Precedence (lowest -> highest):  ||   &&   == !=   < <= > >=   + -   * / %   unary + - !
//
//  Grammar (LL(1) extended for Final Review):
//  ------------------------------------------
//    program    -> { top_item } EOF
//    top_item   -> func_def | statement
//    func_def   -> ret_type ID '(' [ param { ',' param } ] ')' '{' { statement } '}'
//    ret_type   -> 'int' | 'float' | 'void'
//    param      -> type ID
//    statement  -> declaration | assignment | call_stmt | return_stmt
//                | if_stmt | while_stmt | block_stmt
//    declaration-> type declarator { ',' declarator } ';'
//    declarator -> ID [ '[' [ INT_LIT ] ']' ] [ '=' ( expr | '{' [ expr { ',' expr } ] '}' ) ]
//    type       -> 'int' | 'float'
//    assignment -> ID [ '[' expr ']' ] '=' expr ';'
//    call_stmt  -> ID '(' [ expr { ',' expr } ] ')' ';'
//    return_stmt-> 'return' [ expr ] ';'
//    block_stmt -> '{' { statement } '}'
//    if_stmt    -> 'if' '(' cond ')' statement [ 'else' statement ]
//    while_stmt -> 'while' '(' cond ')' statement
//    cond       -> expr
//    expr       -> or_expr
//    or_expr    -> and_expr { '||' and_expr }
//    and_expr   -> eq_expr  { '&&' eq_expr }
//    eq_expr    -> rel_expr { ('==' | '!=') rel_expr }
//    rel_expr   -> add_expr { ('<' | '<=' | '>' | '>=') add_expr }
//    add_expr   -> term     { ('+' | '-') term }
//    term       -> factor   { ('*' | '/' | '%') factor }
//    factor     -> ('+' | '-' | '!') factor | primary
//    primary    -> INT_LIT | FLOAT_LIT | ID | ID '[' expr ']'
//                | ID '(' [ expr { ',' expr } ] ')' | '(' expr ')'
//
//  Still not supported: ++, --, +=, -=, bitwise operators.
//
//  Build : g++ -std=c++17 -Wall -Wextra -o compiler compiler.cpp
//  Run   : ./compiler file.txt [--tokens] [--trace] [--no-fold] [--run]
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
    KW_INT, KW_FLOAT, KW_VOID, KW_IF, KW_ELSE, KW_WHILE, KW_RETURN,
    ID, INT_LIT, FLOAT_LIT,
    ASSIGN, PLUS, MINUS, STAR, SLASH, PERCENT,
    EQ, NEQ, LT, LTE, GT, GTE,
    AND, OR, NOT,
    LPAREN, RPAREN, LBRACE, RBRACE, LBRACKET, RBRACKET, SEMI, COMMA, END
};
enum class Type { Int, Float, Void };

struct Token { T type; string lexeme; int line, col; };
struct Diag  { string kind; string msg; int line, col; string hint; };

static const char* tokName(T t) {
    static const char* n[] = {
        "KW_INT","KW_FLOAT","KW_VOID","KW_IF","KW_ELSE","KW_WHILE","KW_RETURN",
        "ID","INT_LIT","FLOAT_LIT",
        "ASSIGN","PLUS","MINUS","STAR","SLASH","PERCENT",
        "EQ","NEQ","LT","LTE","GT","GTE",
        "AND","OR","NOT",
        "LPAREN","RPAREN","LBRACE","RBRACE","LBRACKET","RBRACKET","SEMI","COMMA","EOF"
    };
    return n[(int)t];
}
static const char* typeName(Type t) {
    return t == Type::Int ? "int" : t == Type::Float ? "float" : "void";
}

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
            T t = T::ID;
            if (s == "int") t = T::KW_INT;
            else if (s == "float") t = T::KW_FLOAT;
            else if (s == "void") t = T::KW_VOID;
            else if (s == "if") t = T::KW_IF;
            else if (s == "else") t = T::KW_ELSE;
            else if (s == "while") t = T::KW_WHILE;
            else if (s == "return") t = T::KW_RETURN;
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
            out.push_back({isFloat ? T::FLOAT_LIT : T::INT_LIT, s, sl, sc});
            continue;
        }

        T t = T::END; bool ok = true; string lexeme;
        if (c == '=' && peek(1) == '=') { t = T::EQ; lexeme = "=="; adv(); }
        else if (c == '!' && peek(1) == '=') { t = T::NEQ; lexeme = "!="; adv(); }
        else if (c == '<' && peek(1) == '=') { t = T::LTE; lexeme = "<="; adv(); }
        else if (c == '>' && peek(1) == '=') { t = T::GTE; lexeme = ">="; adv(); }
        else if (c == '&' && peek(1) == '&') { t = T::AND; lexeme = "&&"; adv(); }
        else if (c == '|' && peek(1) == '|') { t = T::OR;  lexeme = "||"; adv(); }
        else {
            lexeme = string(1, c);
            switch (c) {
                case '=': t = T::ASSIGN;   break;
                case '<': t = T::LT;       break;
                case '>': t = T::GT;       break;
                case '!': t = T::NOT;      break;
                case '+': t = T::PLUS;     break;
                case '-': t = T::MINUS;    break;
                case '*': t = T::STAR;     break;
                case '/': t = T::SLASH;    break;
                case '%': t = T::PERCENT;  break;
                case '(': t = T::LPAREN;   break;
                case ')': t = T::RPAREN;   break;
                case '{': t = T::LBRACE;   break;
                case '}': t = T::RBRACE;   break;
                case '[': t = T::LBRACKET; break;
                case ']': t = T::RBRACKET; break;
                case ';': t = T::SEMI;     break;
                case ',': t = T::COMMA;    break;
                default:  t = T::END; ok = false;
            }
        }
        if (ok) out.push_back({t, lexeme, sl, sc});
        else {
            string hint;
            if (c == '&') hint = "did you mean '&&'?";
            else if (c == '|') hint = "did you mean '||'?";
            diags.push_back({"Lexical error", string("unexpected character '") + c + "'", sl, sc, hint});
        }
        adv();
    }
    out.push_back({T::END, "<EOF>", line, col});
    return out;
}

// ----------------------------------------------------------------- parser ---
struct SyntaxError { string msg; int line, col; bool missingSemi; string hint; };

struct Symbol {
    Type type = Type::Int; bool initialized = false; int line = 0, col = 0;
    bool used = false;          // read or assigned after its declaration
    bool warnedInit = false;    // "may be uninitialized" reported once
    string name;                // name as written in the source
    string uname;               // unique name used in the TAC (x, x#2, ...)
    string scope;               // "global", "global/block", "f", "f/block"
    string fn;                  // owning function ("" = main program)
    bool isArray = false; int size = 0;
    bool isParam = false;
};

struct FuncInfo {
    string name; Type ret = Type::Int;
    vector<Type> ptypes; vector<string> pnames, puniq;
    int line = 0, col = 0;
    bool hasReturn = false;
    vector<string> code;        // TAC of the body
    vector<int> locals;         // indices (into the parser's symbol list) of params + locals
};

struct Opd {                    // result of parsing an expression
    string place; Type type = Type::Int;
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
        : toks(std::move(t)), diags(d), tracing(trace), folding(fold) {
        scopes.emplace_back();      // global scope
    }

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

    void finish(bool lexicalErrors) {
        if (lexicalErrors || errStmts > 0) return;
        for (auto& s : all)
            if (!s.used && !s.isParam)
                diags.push_back({"Warning", string(s.isArray ? "array " : "") + "'" + s.name +
                                 "' is declared but never used", s.line, s.col, ""});
    }

    const vector<string>& code() const { return tac; }
    const vector<Symbol>& allSymbols() const { return all; }
    const map<string, FuncInfo>& functions() const { return funcs; }
    const vector<string>& functionOrder() const { return funcOrder; }
    int statementsOk() const { return okStmts; }
    int statementsFailed() const { return errStmts; }
    int foldedCount() const { return folded; }

private:
    vector<Token> toks;
    size_t p = 0;
    vector<Diag>& diags;
    vector<Symbol> all;                     // every symbol ever declared, in order
    vector<map<string, int>> scopes;        // scope stack: name -> index into 'all'
    map<string, int> nameCount;             // for unique TAC names
    map<string, FuncInfo> funcs;            // function table
    vector<string> funcOrder;
    FuncInfo* curFn = nullptr;              // function being parsed (nullptr = main program)
    vector<string> tac, buf;
    int tmpN = 0, labelN = 0, okStmts = 0, errStmts = 0, folded = 0;
    vector<string> readLog, writeLog;   // variables read / assigned (used by the infinite-loop check)
    bool tracing, folding;
    int depth = 0;

    struct Scope {                      // parse-trace helper
        Parser& P;
        Scope(Parser& parser, const char* rule) : P(parser) {
            if (P.tracing) cout << string(P.depth * 2, ' ') << rule << "   [next: " << desc(P.cur()) << "]\n";
            P.depth++;
        }
        ~Scope() { P.depth--; }
    };
    struct SymScope {                   // pushes / pops one symbol-table scope (exception safe)
        Parser& P;
        explicit SymScope(Parser& parser) : P(parser) { P.scopes.emplace_back(); }
        ~SymScope() { P.scopes.pop_back(); }
    };
    struct FnGuard {                    // switches to a function's own TAC buffer and back
        Parser& P; FuncInfo* savedFn; vector<string> savedBuf;
        FnGuard(Parser& parser, FuncInfo* f) : P(parser), savedFn(parser.curFn) {
            savedBuf.swap(P.buf); P.curFn = f;
        }
        ~FnGuard() { P.curFn = savedFn; P.buf.swap(savedBuf); }
    };

    const Token& cur() const { return toks[p]; }
    static bool isStmtStart(const Token& t) {
        return t.type == T::KW_INT || t.type == T::KW_FLOAT || t.type == T::KW_VOID || t.type == T::ID ||
               t.type == T::KW_IF || t.type == T::KW_WHILE || t.type == T::KW_RETURN || t.type == T::LBRACE;
    }
    static string desc(const Token& t) {
        return t.type == T::END ? "end of file" : "'" + t.lexeme + "'";
    }
    bool accept(T t) { if (cur().type == t) { p++; return true; } return false; }

    Token expect(T t, const string& what) {
        if (cur().type == t) return toks[p++];
        if (t == T::SEMI && p > 0) {
            const Token& pv = toks[p - 1];
            throw SyntaxError{"expected ';' after '" + pv.lexeme + "', found " + desc(cur()),
                              pv.line, pv.col + (int)pv.lexeme.size(), true, ""};
        }
        throw SyntaxError{"expected " + what + ", found " + desc(cur()), cur().line, cur().col, false, ""};
    }

    void synchronize(size_t start) {
        while (cur().type != T::END) {
            if (cur().type == T::SEMI || cur().type == T::RBRACE) { p++; return; }
            if (isStmtStart(cur()) && p > start) return;
            p++;
        }
    }

    void semantic(const string& kind, const string& msg, const Token& at, const string& hint = "") {
        diags.push_back({kind, msg, at.line, at.col, hint});
    }
    string newTemp() { return "t" + to_string(++tmpN); }
    string newLabel() { return "L" + to_string(++labelN); }

    // ---- symbol table (scope stack) -----------------------------------------
    int lookup(const string& name) const {
        for (int i = (int)scopes.size() - 1; i >= 0; i--) {
            auto it = scopes[i].find(name);
            if (it != scopes[i].end()) return it->second;
        }
        return -1;
    }
    vector<string> visibleNames() const {
        vector<string> v;
        for (auto& sc : scopes) for (auto& kv : sc) v.push_back(kv.first);
        return v;
    }
    string uniqueName(const string& n) {
        int c = ++nameCount[n];
        return c == 1 ? n : n + "#" + to_string(c);
    }
    // Declares a name in the innermost scope. Returns its index, or -1 on redeclaration.
    int declare(const Token& id, Type ty, bool init, bool isArr, int size, bool isParam) {
        auto& sc = scopes.back();
        auto it = sc.find(id.lexeme);
        if (it != sc.end()) {
            semantic("Semantic error", "redeclaration of '" + id.lexeme + "' (first declared on line " +
                                           to_string(all[it->second].line) + ")", id);
            return -1;
        }
        Symbol s;
        s.type = ty; s.initialized = init; s.line = id.line; s.col = id.col;
        s.name = id.lexeme; s.uname = uniqueName(id.lexeme);
        s.fn = curFn ? curFn->name : "";
        int base = curFn ? 1 : 0;
        s.scope = (curFn ? curFn->name : string("global")) + ((int)scopes.size() - 1 > base ? "/block" : "");
        s.isArray = isArr; s.size = size; s.isParam = isParam;
        all.push_back(s);
        int idx = (int)all.size() - 1;
        sc[id.lexeme] = idx;
        if (curFn) curFn->locals.push_back(idx);
        return idx;
    }

    string suggestType(const string& name) { return closestMatch(name, {"int", "float", "void"}); }
    void reportUndeclared(const Token& id) {
        string s = closestMatch(id.lexeme, visibleNames());
        semantic("Semantic error", "'" + id.lexeme + "' is not declared", id,
                 s.empty() ? "" : "did you mean '" + s + "'?");
    }
    void checkIndex(const Token& id, const Symbol& s, const Opd& idx) {
        if (idx.type == Type::Float)
            semantic("Semantic error", "index of array '" + s.name + "' must be an integer", id);
        else if (idx.isConst && (idx.iv < 0 || idx.iv >= s.size))
            semantic("Semantic error", "index " + to_string(idx.iv) + " is out of bounds for array '" +
                                           s.name + "' of size " + to_string(s.size), id);
    }

    // ---- grammar rules
    void statement() {
        Scope sc(*this, "statement");
        T k = cur().type;
        if (k == T::KW_INT || k == T::KW_FLOAT || k == T::KW_VOID) {
            if (p + 2 < toks.size() && toks[p + 1].type == T::ID && toks[p + 2].type == T::LPAREN) {
                funcDef();
                return;
            }
            declaration();
            return;
        }
        if (k == T::KW_IF)     { ifStmt(); return; }
        if (k == T::KW_WHILE)  { whileStmt(); return; }
        if (k == T::KW_RETURN) { returnStmt(); return; }
        if (k == T::LBRACE)    { blockStmt(); return; }
        if (k == T::ID) {
            if (p + 1 < toks.size() && toks[p + 1].type == T::ID) {
                string s = suggestType(cur().lexeme);
                if (!s.empty()) {
                    diags.push_back({"Syntax error", "unknown type '" + cur().lexeme + "'",
                                     cur().line, cur().col, "did you mean '" + s + "'?"});
                    p++;
                    declarationRest(s == "int" ? Type::Int : s == "float" ? Type::Float : Type::Void);
                    return;
                }
            }
            if (p + 1 < toks.size() && toks[p + 1].type == T::LPAREN) { callStmt(); return; }
            assignment();
            return;
        }
        throw SyntaxError{"expected a declaration or statement, found " + desc(cur()),
                          cur().line, cur().col, false, ""};
    }

    void declaration() {
        Scope sc(*this, "declaration");
        Type ty = cur().type == T::KW_INT ? Type::Int : cur().type == T::KW_FLOAT ? Type::Float : Type::Void;
        p++;
        declarationRest(ty);
    }

    void declarationRest(Type ty) {
        do {
            Token id = expect(T::ID, "identifier");
            if (isReserved(id.lexeme))
                semantic("Semantic error", "'" + id.lexeme + "' is reserved for compiler temporaries, labels and jump words", id);
            if (ty == Type::Void)
                semantic("Semantic error", "variable '" + id.lexeme + "' cannot have type void", id);
            Type vt = ty == Type::Void ? Type::Int : ty;

            // optional array suffix: '[' [INT_LIT] ']'
            bool isArr = false, sizeGiven = false; long long size = 0;
            if (accept(T::LBRACKET)) {
                isArr = true;
                if (cur().type == T::INT_LIT) {
                    size = strtoll(cur().lexeme.c_str(), nullptr, 10); sizeGiven = true; p++;
                } else if (cur().type != T::RBRACKET) {
                    throw SyntaxError{"array size must be an integer literal, found " + desc(cur()),
                                      cur().line, cur().col, false, ""};
                }
                expect(T::RBRACKET, "']'");
                if (sizeGiven && (size <= 0 || size > 100000)) {
                    semantic("Semantic error", "array '" + id.lexeme + "' must have a size between 1 and 100000", id);
                    size = 1;
                }
            }

            Opd init; bool has = false; vector<Opd> inits;
            if (accept(T::ASSIGN)) {
                has = true;
                if (isArr) {
                    expect(T::LBRACE, "'{'");
                    if (cur().type != T::RBRACE) do { inits.push_back(expr()); } while (accept(T::COMMA));
                    expect(T::RBRACE, "'}'");
                } else {
                    init = expr();
                }
            }
            if (isArr) {
                if (!sizeGiven) {
                    if (!has) {
                        semantic("Semantic error", "array '" + id.lexeme + "' needs a size or an initializer list", id);
                        size = 1;
                    } else if (inits.empty()) {
                        semantic("Semantic error", "cannot infer the size of array '" + id.lexeme + "' from an empty initializer list", id);
                        size = 1;
                    } else size = (long long)inits.size();
                } else if ((long long)inits.size() > size) {
                    semantic("Semantic error", "too many initializers for array '" + id.lexeme + "' (size " +
                                                   to_string(size) + ", given " + to_string(inits.size()) + ")", id);
                }
            }

            int si = declare(id, vt, has, isArr, (int)size, false);
            if (si >= 0) {
                string un = all[si].uname;
                if (isArr) {
                    buf.push_back("array " + un + " " + to_string(size));
                    for (size_t k = 0; k < inits.size() && (long long)k < size; k++) {
                        if (vt == Type::Int && inits[k].type == Type::Float)
                            semantic("Warning", "implicit float -> int conversion in initializer of '" + id.lexeme + "'", id);
                        writeLog.push_back(un);
                        buf.push_back(un + "[" + to_string(k) + "] = " + inits[k].place);
                    }
                } else if (has) {
                    if (vt == Type::Int && init.type == Type::Float)
                        semantic("Warning", "implicit float -> int conversion in initializer of '" + id.lexeme + "'", id);
                    writeLog.push_back(un);
                    buf.push_back(un + " = " + init.place);
                }
            }
        } while (accept(T::COMMA));
        expect(T::SEMI, "';'");
    }

    void assignment() {
        Scope sc(*this, "assignment");
        Token id = toks[p++];
        bool indexed = false; Opd idx;
        if (accept(T::LBRACKET)) { idx = expr(); expect(T::RBRACKET, "']'"); indexed = true; }
        expect(T::ASSIGN, "'='");
        Opd v = expr();
        int si = lookup(id.lexeme);
        string target = id.lexeme;
        if (si < 0)
            reportUndeclared(id);
        else {
            Symbol& s = all[si];
            target = s.uname;
            if (indexed && !s.isArray)
                semantic("Semantic error", "'" + id.lexeme + "' is not an array", id);
            else if (!indexed && s.isArray)
                semantic("Semantic error", "cannot assign to array '" + id.lexeme + "' as a whole; use an index", id);
            else if (indexed)
                checkIndex(id, s, idx);
            if (s.type == Type::Int && v.type == Type::Float)
                semantic("Warning", "implicit float -> int conversion when assigning to '" + id.lexeme + "'", id);
            s.initialized = true;
            s.used = true;
        }
        writeLog.push_back(target);
        buf.push_back((indexed ? target + "[" + idx.place + "]" : target) + " = " + v.place);
        expect(T::SEMI, "';'");
    }

    void callStmt() {
        Scope sc(*this, "call_stmt");
        Token id = toks[p++];
        call(id, true);
        expect(T::SEMI, "';'");
    }

    void returnStmt() {
        Scope sc(*this, "return_stmt");
        Token kw = toks[p++];
        if (!curFn) semantic("Semantic error", "'return' outside of a function", kw);
        if (cur().type != T::SEMI) {
            Opd v = expr();
            if (curFn) {
                if (curFn->ret == Type::Void)
                    semantic("Semantic error", "void function '" + curFn->name + "' cannot return a value", kw);
                else if (curFn->ret == Type::Int && v.type == Type::Float)
                    semantic("Warning", "implicit float -> int conversion in return of '" + curFn->name + "'", kw);
            }
            buf.push_back("return " + v.place);
        } else {
            if (curFn && curFn->ret != Type::Void)
                semantic("Semantic error", "non-void function '" + curFn->name + "' must return a value", kw);
            buf.push_back("return");
        }
        if (curFn) curFn->hasReturn = true;
        expect(T::SEMI, "';'");
    }

    void funcDef() {
        Scope sc(*this, "func_def");
        Type ret = cur().type == T::KW_INT ? Type::Int : cur().type == T::KW_FLOAT ? Type::Float : Type::Void;
        p++;
        Token id = toks[p++];
        expect(T::LPAREN, "'('");
        vector<Type> pt; vector<Token> pn;
        if (cur().type == T::KW_VOID && p + 1 < toks.size() && toks[p + 1].type == T::RPAREN) {
            p++;                                    // f(void)
        } else if (cur().type != T::RPAREN) {
            do {
                Type t;
                if (cur().type == T::KW_INT) t = Type::Int;
                else if (cur().type == T::KW_FLOAT) t = Type::Float;
                else throw SyntaxError{"expected a parameter type ('int' or 'float'), found " + desc(cur()),
                                       cur().line, cur().col, false, ""};
                p++;
                pn.push_back(expect(T::ID, "parameter name"));
                pt.push_back(t);
            } while (accept(T::COMMA));
        }
        expect(T::RPAREN, "')'");

        if (curFn || scopes.size() > 1)
            semantic("Semantic error", "function '" + id.lexeme + "' must be defined at the top level", id);
        if (isReserved(id.lexeme))
            semantic("Semantic error", "'" + id.lexeme + "' is reserved for compiler temporaries, labels and jump words", id);
        int vi = lookup(id.lexeme);
        if (vi >= 0)
            semantic("Semantic error", "'" + id.lexeme + "' is already declared as a variable (line " +
                                           to_string(all[vi].line) + ")", id);

        FuncInfo scratch;                           // used when the name is a redefinition
        FuncInfo* fi;
        auto prev = funcs.find(id.lexeme);
        if (prev != funcs.end()) {
            semantic("Semantic error", "redefinition of function '" + id.lexeme + "' (first defined on line " +
                                           to_string(prev->second.line) + ")", id);
            fi = &scratch;
        } else {
            fi = &funcs[id.lexeme];
            funcOrder.push_back(id.lexeme);
        }
        fi->name = id.lexeme; fi->ret = ret; fi->ptypes = pt; fi->line = id.line; fi->col = id.col;

        FnGuard fg(*this, fi);                      // own TAC buffer; restores on exit/exception
        SymScope ss(*this);                         // parameters + body share one scope
        for (size_t i = 0; i < pn.size(); i++) {
            int si = declare(pn[i], pt[i], true, false, 0, true);
            fi->pnames.push_back(pn[i].lexeme);
            fi->puniq.push_back(si >= 0 ? all[si].uname : pn[i].lexeme + "#dup");
        }
        expect(T::LBRACE, "'{'");
        blockInner();
        if (ret != Type::Void && !fi->hasReturn)
            semantic("Warning", "non-void function '" + id.lexeme + "' has no return statement", id);
        buf.push_back("return");                    // implicit return at the end
        fi->code = buf;
    }

    // Parses a function call (after the name has been consumed). 'asStmt' allows void results.
    Opd call(const Token& id, bool asStmt) {
        Scope sc(*this, "call");
        expect(T::LPAREN, "'('");
        vector<Opd> args;
        if (cur().type != T::RPAREN) do { args.push_back(expr()); } while (accept(T::COMMA));
        expect(T::RPAREN, "')'");
        writeLog.push_back("*call*");               // a call may change any global

        auto it = funcs.find(id.lexeme);
        if (it == funcs.end()) {
            if (lookup(id.lexeme) >= 0)
                semantic("Semantic error", "'" + id.lexeme + "' is a variable, not a function", id);
            else {
                string s = closestMatch(id.lexeme, funcOrder);
                semantic("Semantic error", "function '" + id.lexeme + "' is not declared", id,
                         s.empty() ? "" : "did you mean '" + s + "'?");
            }
            return {"0", Type::Int};
        }
        const FuncInfo& f = it->second;
        Type rt = f.ret == Type::Void ? Type::Int : f.ret;
        if (args.size() != f.ptypes.size()) {
            semantic("Semantic error", "function '" + f.name + "' expects " + to_string(f.ptypes.size()) +
                                           " argument(s) but " + to_string(args.size()) + " given", id);
            return {"0", rt};
        }
        for (size_t i = 0; i < args.size(); i++)
            if (f.ptypes[i] == Type::Int && args[i].type == Type::Float)
                semantic("Warning", "implicit float -> int conversion in argument " + to_string(i + 1) +
                                        " of call to '" + f.name + "'", id);
        if (f.ret == Type::Void && !asStmt) {
            semantic("Semantic error", "void function '" + f.name + "' used as a value", id);
            return {"0", Type::Int};
        }
        for (auto& a : args) buf.push_back("param " + a.place);
        string callText = "call " + f.name + " " + to_string(args.size());
        if (f.ret == Type::Void) { buf.push_back(callText); return {"", Type::Void}; }
        string t = newTemp();
        buf.push_back(t + " = " + callText);
        return {t, f.ret};
    }

    void ifStmt() {
        Scope sc(*this, "if_stmt");
        expect(T::KW_IF, "'if'");
        expect(T::LPAREN, "'('");
        Opd c = cond();
        expect(T::RPAREN, "')'");

        string elseLabel = newLabel();
        string endLabel = newLabel();

        buf.push_back("if_false " + c.place + " goto " + elseLabel);
        statement();
        if (cur().type == T::KW_ELSE) {
            expect(T::KW_ELSE, "'else'");
            buf.push_back("goto " + endLabel);
            buf.push_back(elseLabel + ":");
            statement();
            buf.push_back(endLabel + ":");
        } else {
            buf.push_back(elseLabel + ":");
        }
    }

    void whileStmt() {
        Scope sc(*this, "while_stmt");
        Token kw = cur();                       // kept for warning positions
        expect(T::KW_WHILE, "'while'");
        string startLabel = newLabel();
        string endLabel = newLabel();

        buf.push_back(startLabel + ":");
        expect(T::LPAREN, "'('");
        size_t readsBefore = readLog.size();
        Opd c = cond();
        size_t readsAfter = readLog.size();
        expect(T::RPAREN, "')'");

        buf.push_back("if_false " + c.place + " goto " + endLabel);
        size_t writesBefore = writeLog.size();
        statement();
        checkInfiniteLoop(kw, c, readsBefore, readsAfter, writesBefore);
        buf.push_back("goto " + startLabel);
        buf.push_back(endLabel + ":");
    }

    // ---- infinite-loop detection (compile time) ----------------------------
    // The language has no break, so a loop can only stop when its condition
    // becomes false. Three cases are reported as warnings:
    //   1. constant non-zero condition  -> the loop can never terminate
    //   2. constant zero condition      -> the body can never execute
    //   3. condition reads variables, but the body assigns none of them
    //      -> the condition can never change (possible infinite loop)
    // A function call in the body is assumed to possibly change anything, so it
    // suppresses case 3. Loops that do change their variables but still never end
    // (for example i = i + 1 while i > 0) cannot be decided here; the --run step
    // limit catches them.
    void checkInfiniteLoop(const Token& kw, const Opd& c, size_t readsBefore,
                           size_t readsAfter, size_t writesBefore) {
        if (c.isConst) {
            if (!isZero(c))
                semantic("Warning", "infinite loop: the condition is always true and the loop has no way to exit", kw);
            else
                semantic("Warning", "the loop condition is always false, so the body never executes", kw);
            return;
        }
        if (readsAfter == readsBefore) return;                  // no variables in the condition
        for (size_t j = writesBefore; j < writeLog.size(); j++)
            if (writeLog[j] == "*call*") return;                // a call might modify it
        for (size_t i = readsBefore; i < readsAfter; i++)
            for (size_t j = writesBefore; j < writeLog.size(); j++)
                if (readLog[i] == writeLog[j]) return;          // body changes a condition variable
        semantic("Warning", "possible infinite loop: no variable used in the condition is modified in the loop body", kw);
    }

    void blockStmt() {
        Scope sc(*this, "block_stmt");
        expect(T::LBRACE, "'{'");
        SymScope ss(*this);                     // new symbol-table scope for the block
        blockInner();
    }

    // statements up to and including the closing '}' (the '{' is already consumed)
    void blockInner() {
        while (cur().type != T::RBRACE && cur().type != T::END) {
            size_t start = p;
            try {
                statement();
            } catch (SyntaxError& e) {
                errStmts++;
                diags.push_back({"Syntax error", e.msg, e.line, e.col, e.hint});
                bool keepGoing = e.missingSemi && (isStmtStart(cur()) || cur().type == T::RBRACE || cur().type == T::END);
                if (!keepGoing) synchronize(start);
            }
        }
        expect(T::RBRACE, "'}'");
    }

    // A condition is simply an expression: zero is false, anything else is true.
    Opd cond() {
        Scope sc(*this, "cond");
        return expr();
    }

    static bool isReserved(const string& n) {
        if (n == "goto" || n == "if_false" || n == "if_true" || n == "param" || n == "call" || n == "array") return true;
        if (n.size() >= 2 && (n[0] == 't' || n[0] == 'L')) {
            for (size_t i = 1; i < n.size(); i++) if (!isdigit((unsigned char)n[i])) return false;
            return true;
        }
        return false;
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
        if (folding && !bad && l.isConst && r.isConst) {
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

    // Comparison: always yields an int (0 or 1).
    Opd compare(const Token& op, const Opd& l, const Opd& r) {
        if (folding && l.isConst && r.isConst) {
            folded++;
            double a = l.type == Type::Float ? l.dv : (double)l.iv;
            double b = r.type == Type::Float ? r.dv : (double)r.iv;
            long long res = 0;
            if (op.type == T::EQ)       res = (a == b);
            else if (op.type == T::NEQ) res = (a != b);
            else if (op.type == T::LT)  res = (a < b);
            else if (op.type == T::LTE) res = (a <= b);
            else if (op.type == T::GT)  res = (a > b);
            else if (op.type == T::GTE) res = (a >= b);
            return constInt(res);
        }
        string t = newTemp();
        buf.push_back(t + " = " + l.place + " " + op.lexeme + " " + r.place);
        return {t, Type::Int};
    }

    // ---- expressions, lowest precedence first --------------------------------
    Opd expr() {
        Scope sc(*this, "expr");
        return orExpr();
    }

    // a || b || c   with short-circuit evaluation:
    //     <code a>   if_true a goto Ltrue
    //     <code b>   if_true b goto Ltrue
    //     <code c>   if_true c goto Ltrue
    //     res = 0    goto Lend
    //   Ltrue:  res = 1
    //   Lend:
    // While every operand so far is a constant 0 no code is needed. A constant non-zero
    // operand decides the whole expression: the operands after it are parsed and
    // checked, but their code is thrown away because it can never run.
    Opd orExpr() {
        Scope sc(*this, "or_expr");
        Opd l = andExpr();
        if (cur().type != T::OR) return l;

        enum { ALLFALSE, DEAD, JUMPING } st = ALLFALSE;
        string res, lt, le;
        auto isK = [&](const Opd& o) { return folding && o.isConst; };
        auto consume = [&](const Opd& o) {          // called right after operand 'o' was parsed
            if (st == DEAD) return;
            if (st == ALLFALSE && isK(o)) { if (!isZero(o)) st = DEAD; return; }
            if (st == ALLFALSE) { res = newTemp(); lt = newLabel(); le = newLabel(); st = JUMPING; }
            buf.push_back("if_true " + o.place + " goto " + lt);
        };
        consume(l);
        while (cur().type == T::OR) {
            p++;
            size_t cut = buf.size();
            Opd r = andExpr();
            if (st == DEAD) buf.resize(cut);        // short-circuited away
            else consume(r);
        }
        if (st == ALLFALSE) { folded++; return constInt(0); }
        if (st == DEAD)     { folded++; return constInt(1); }
        buf.push_back(res + " = 0");
        buf.push_back("goto " + le);
        buf.push_back(lt + ":");
        buf.push_back(res + " = 1");
        buf.push_back(le + ":");
        return {res, Type::Int};
    }

    // a && b && c   with short-circuit evaluation:
    //     <code a>   if_false a goto Lfalse
    //     <code b>   if_false b goto Lfalse
    //     <code c>   if_false c goto Lfalse
    //     res = 1    goto Lend
    //   Lfalse: res = 0
    //   Lend:
    Opd andExpr() {
        Scope sc(*this, "and_expr");
        Opd l = eqExpr();
        if (cur().type != T::AND) return l;

        enum { ALLTRUE, DEAD, JUMPING } st = ALLTRUE;
        string res, lf, le;
        auto isK = [&](const Opd& o) { return folding && o.isConst; };
        auto consume = [&](const Opd& o) {
            if (st == DEAD) return;
            if (st == ALLTRUE && isK(o)) { if (isZero(o)) st = DEAD; return; }
            if (st == ALLTRUE) { res = newTemp(); lf = newLabel(); le = newLabel(); st = JUMPING; }
            buf.push_back("if_false " + o.place + " goto " + lf);
        };
        consume(l);
        while (cur().type == T::AND) {
            p++;
            size_t cut = buf.size();
            Opd r = eqExpr();
            if (st == DEAD) buf.resize(cut);        // short-circuited away
            else consume(r);
        }
        if (st == ALLTRUE) { folded++; return constInt(1); }
        if (st == DEAD)    { folded++; return constInt(0); }
        buf.push_back(res + " = 1");
        buf.push_back("goto " + le);
        buf.push_back(lf + ":");
        buf.push_back(res + " = 0");
        buf.push_back(le + ":");
        return {res, Type::Int};
    }

    Opd eqExpr() {
        Scope sc(*this, "eq_expr");
        Opd l = relExpr();
        while (cur().type == T::EQ || cur().type == T::NEQ) {
            Token op = toks[p++];
            Opd r = relExpr();
            l = compare(op, l, r);
        }
        return l;
    }

    Opd relExpr() {
        Scope sc(*this, "rel_expr");
        Opd l = addExpr();
        while (cur().type == T::LT || cur().type == T::LTE || cur().type == T::GT || cur().type == T::GTE) {
            Token op = toks[p++];
            Opd r = addExpr();
            l = compare(op, l, r);
        }
        return l;
    }

    Opd addExpr() {
        Scope sc(*this, "add_expr");
        Opd l = term();
        while (cur().type == T::PLUS || cur().type == T::MINUS) {
            Token op = toks[p++];
            Opd r = term();
            l = binary(op, l, r);
        }
        return l;
    }

    Opd term() {
        Scope sc(*this, "term");
        Opd l = factor();
        while (cur().type == T::STAR || cur().type == T::SLASH || cur().type == T::PERCENT) {
            Token op = toks[p++];
            Opd r = factor();
            l = binary(op, l, r);
        }
        return l;
    }

    Opd factor() {
        Scope sc(*this, "factor");
        if (cur().type == T::NOT) {
            p++;
            Opd o = factor();
            if (folding && o.isConst) { folded++; return constInt(isZero(o) ? 1 : 0); }
            string t = newTemp();
            buf.push_back(t + " = !" + o.place);
            return {t, Type::Int};
        }
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
                if (cur().type == T::LPAREN) return call(id, false);
                int si = lookup(id.lexeme);
                if (si < 0) {
                    reportUndeclared(id);
                    if (accept(T::LBRACKET)) { expr(); expect(T::RBRACKET, "']'"); }   // keep parsing
                    return {id.lexeme, Type::Int};
                }
                all[si].used = true;
                if (accept(T::LBRACKET)) {                      // array element read
                    Opd idx = expr();
                    expect(T::RBRACKET, "']'");
                    if (!all[si].isArray) {
                        semantic("Semantic error", "'" + id.lexeme + "' is not an array", id);
                        return {all[si].uname, all[si].type};
                    }
                    checkIndex(id, all[si], idx);
                    readLog.push_back(all[si].uname);
                    string tmp = newTemp();
                    buf.push_back(tmp + " = " + all[si].uname + "[" + idx.place + "]");
                    return {tmp, all[si].type};
                }
                if (all[si].isArray) {
                    semantic("Semantic error", "array '" + id.lexeme + "' used without an index", id);
                    return {all[si].uname, all[si].type};
                }
                readLog.push_back(all[si].uname);
                if (!all[si].initialized && !all[si].warnedInit) {
                    semantic("Warning", "'" + id.lexeme + "' may be used before it is initialized", id);
                    all[si].warnedInit = true;
                }
                return {all[si].uname, all[si].type};
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

// ---------------------------------------------------- TAC Interpreter (VM) ---
class Interpreter {
public:
    struct Value {
        bool isFloat = false;
        long long iv = 0;
        double dv = 0.0;

        Value() : isFloat(false), iv(0), dv(0.0) {}
        Value(long long v) : isFloat(false), iv(v), dv((double)v) {}
        Value(double v) : isFloat(true), iv((long long)v), dv(v) {}

        double asDouble() const { return isFloat ? dv : (double)iv; }
        long long asInt() const { return isFloat ? (long long)dv : iv; }
        string str() const { return isFloat ? fmtFloat(dv) : to_string(iv); }
        bool isTruthy() const { return isFloat ? (dv != 0.0) : (iv != 0); }
    };

    struct Frame {                              // one activation record
        map<string, Value> vars;
        map<string, vector<Value>> arrays;
    };

    Interpreter(const vector<string>& code, const map<string, FuncInfo>& fns, const vector<Symbol>& syms)
        : mainCode(code), funcs(fns), symbols(syms) {
        for (const auto& s : symbols) info[s.uname] = &s;
    }

    bool run() {
        for (const auto& s : symbols)
            if (s.fn.empty()) initVar(s, glob);     // main-program variables live in the global frame
        Value ret;
        if (!exec(mainCode, glob, ret, 0)) return false;

        cout << "\n---- TAC INTERPRETER EXECUTION ----\n";
        cout << "Execution completed in " << stepCount << " instruction steps.\n";
        cout << "\nFinal Variable Values:\n";
        cout << left << setw(12) << "Variable" << setw(12) << "Type" << "Runtime Value\n";
        for (const auto& s : symbols) {
            if (!s.fn.empty()) continue;
            string t = typeName(s.type);
            if (s.isArray) t += "[" + to_string(s.size) + "]";
            cout << left << setw(12) << s.uname << setw(12) << t;
            if (s.isArray) {
                const auto& arr = glob.arrays[s.uname];
                cout << "[";
                for (size_t i = 0; i < arr.size(); i++) cout << (i ? ", " : "") << arr[i].str();
                cout << "]\n";
            } else cout << glob.vars[s.uname].str() << "\n";
        }
        return true;
    }

private:
    vector<string> mainCode;
    const map<string, FuncInfo>& funcs;
    const vector<Symbol>& symbols;
    map<string, const Symbol*> info;
    Frame glob;
    vector<Value> argStack;
    long long stepCount = 0;
    const long long maxSteps = 1000000;
    const int maxDepth = 500;

    static string trim(const string& s) {
        size_t b = s.find_first_not_of(" \t\r\n");
        if (b == string::npos) return "";
        size_t e = s.find_last_not_of(" \t\r\n");
        return s.substr(b, e - b + 1);
    }

    static bool splitIndex(const string& t, string& name, string& idx) {
        size_t b = t.find('[');
        if (b == string::npos || t.empty() || t.back() != ']') return false;
        name = t.substr(0, b);
        idx = t.substr(b + 1, t.size() - b - 2);
        return true;
    }

    static void initVar(const Symbol& s, Frame& f) {
        Value z = s.type == Type::Float ? Value(0.0) : Value(0LL);
        if (s.isArray) f.arrays[s.uname] = vector<Value>((size_t)s.size, z);
        else f.vars[s.uname] = z;
    }

    Value coerce(const string& name, const Value& v) const {
        auto it = info.find(name);
        if (it == info.end()) return v;
        return it->second->type == Type::Float ? Value(v.asDouble()) : Value(v.asInt());
    }

    Value eval(const string& token, Frame& fr) {
        if (token.empty()) return Value(0LL);
        char* endp = nullptr;
        if (token.find('.') != string::npos) {
            double d = strtod(token.c_str(), &endp);
            if (endp && *endp == '\0') return Value(d);
        } else {
            long long val = strtoll(token.c_str(), &endp, 10);
            if (endp && *endp == '\0') return Value(val);
        }
        auto it = fr.vars.find(token);
        if (it != fr.vars.end()) return it->second;
        auto g = glob.vars.find(token);
        if (g != glob.vars.end()) return g->second;
        return Value(0LL);
    }

    vector<Value>* findArr(const string& name, Frame& fr) {
        auto it = fr.arrays.find(name);
        if (it != fr.arrays.end()) return &it->second;
        auto g = glob.arrays.find(name);
        if (g != glob.arrays.end()) return &g->second;
        return nullptr;
    }

    bool elementRef(const string& tok, Frame& fr, Value*& out) {
        string name, idxTok;
        splitIndex(tok, name, idxTok);
        long long i = eval(idxTok, fr).asInt();
        vector<Value>* arr = findArr(name, fr);
        if (!arr) { cerr << "Runtime error: unknown array '" << name << "'\n"; return false; }
        if (i < 0 || i >= (long long)arr->size()) {
            cerr << "Runtime error: array index " << i << " out of bounds for '" << name
                 << "' (size " << arr->size() << ")\n";
            return false;
        }
        out = &(*arr)[(size_t)i];
        return true;
    }

    bool store(const string& dest, const Value& val, Frame& fr) {
        if (dest.find('[') != string::npos) {
            string name, idxTok; splitIndex(dest, name, idxTok);
            Value* slot = nullptr;
            if (!elementRef(dest, fr, slot)) return false;
            *slot = coerce(name, val);
            return true;
        }
        Value cv = coerce(dest, val);
        if (fr.vars.count(dest)) fr.vars[dest] = cv;
        else if (glob.vars.count(dest)) glob.vars[dest] = cv;
        else fr.vars[dest] = cv;                    // compiler temporary
        return true;
    }

    bool doCall(const string& name, size_t n, Value& result, int depth) {
        auto it = funcs.find(name);
        if (it == funcs.end()) { cerr << "Runtime error: unknown function '" << name << "'\n"; return false; }
        if (depth >= maxDepth) {
            cerr << "Runtime error: call stack overflow (more than " << maxDepth << " nested calls) in '" << name << "'\n";
            return false;
        }
        if (argStack.size() < n) { cerr << "Runtime error: missing call arguments for '" << name << "'\n"; return false; }
        const FuncInfo& f = it->second;
        vector<Value> args(argStack.end() - (long)n, argStack.end());
        argStack.erase(argStack.end() - (long)n, argStack.end());

        Frame nf;
        for (int li : f.locals) initVar(symbols[(size_t)li], nf);
        for (size_t i = 0; i < f.puniq.size() && i < args.size(); i++)
            nf.vars[f.puniq[i]] = coerce(f.puniq[i], args[i]);

        Value rv;
        if (!exec(f.code, nf, rv, depth + 1)) return false;
        result = f.ret == Type::Float ? Value(rv.asDouble()) : Value(rv.asInt());
        return true;
    }

    // Runs one TAC sequence in the given frame. 'ret' receives the value of a 'return'.
    bool exec(const vector<string>& code, Frame& fr, Value& ret, int depth) {
        map<string, size_t> labels;
        for (size_t i = 0; i < code.size(); i++) {
            string line = trim(code[i]);
            if (!line.empty() && line.back() == ':') labels[line.substr(0, line.size() - 1)] = i;
        }
        ret = Value(0LL);

        size_t pc = 0;
        while (pc < code.size()) {
            if (++stepCount > maxSteps) {
                cerr << "Runtime error: execution limit exceeded (infinite loop protection) after " << maxSteps
                     << " steps, stopped at TAC line " << pc + 1 << ": " << trim(code[pc]) << "\n";
                return false;
            }

            string raw = trim(code[pc]);
            pc++;
            if (raw.empty() || raw.back() == ':') continue;

            stringstream ss(raw);
            string first; ss >> first;

            if (first == "array") continue;                 // storage is created when the frame is built

            if (first == "goto") {
                string target; ss >> target;
                if (!labels.count(target)) {
                    cerr << "Runtime error: unknown jump label " << target << "\n";
                    return false;
                }
                pc = labels[target];
                continue;
            }

            if (first == "if_false" || first == "if_true") {
                string condName, gotoKw, target;
                ss >> condName >> gotoKw >> target;
                Value cv = eval(condName, fr);
                bool jump = (first == "if_false") ? !cv.isTruthy() : cv.isTruthy();
                if (jump) {
                    if (!labels.count(target)) {
                        cerr << "Runtime error: unknown jump label " << target << "\n";
                        return false;
                    }
                    pc = labels[target];
                }
                continue;
            }

            if (first == "param") {
                string a; ss >> a;
                argStack.push_back(eval(a, fr));
                continue;
            }

            if (first == "return") {
                string a; ss >> a;
                if (!a.empty()) ret = eval(a, fr);
                return true;
            }

            if (first == "call") {                          // call f n   (result discarded)
                string nm; size_t n = 0; ss >> nm >> n;
                Value dummy;
                if (!doCall(nm, n, dummy, depth)) return false;
                continue;
            }

            string dest = first;
            string eq; ss >> eq;
            if (eq != "=") continue;

            string rest;
            getline(ss, rest);
            rest = trim(rest);

            if (rest.compare(0, 5, "call ") == 0) {         // dest = call f n
                stringstream cs(rest);
                string kw, nm; size_t n = 0; cs >> kw >> nm >> n;
                Value rv;
                if (!doCall(nm, n, rv, depth)) return false;
                if (!store(dest, rv, fr)) return false;
                continue;
            }

            if (rest.find('[') != string::npos && rest.find(' ') == string::npos) {   // dest = a[i]
                Value* slot = nullptr;
                if (!elementRef(rest, fr, slot)) return false;
                if (!store(dest, *slot, fr)) return false;
                continue;
            }

            if (rest.size() > 1 && (rest[0] == '-' || rest[0] == '!') && rest.find(' ') == string::npos &&
                (isalnum((unsigned char)rest[1]) || rest[1] == '_')) {                // unary - or !
                Value v = eval(rest.substr(1), fr);
                Value res;
                if (rest[0] == '!') res = Value((long long)(v.isTruthy() ? 0 : 1));
                else res = v.isFloat ? Value(-v.dv) : Value(-v.iv);
                if (!store(dest, res, fr)) return false;
                continue;
            }

            stringstream rss(rest);
            string op1, op, op2;
            if (rss >> op1 >> op >> op2) {
                Value v1 = eval(op1, fr);
                Value v2 = eval(op2, fr);
                bool resIsFloat = v1.isFloat || v2.isFloat;
                Value res;

                if (op == "+") {
                    if (resIsFloat) res = Value(v1.asDouble() + v2.asDouble());
                    else res = Value(v1.asInt() + v2.asInt());
                } else if (op == "-") {
                    if (resIsFloat) res = Value(v1.asDouble() - v2.asDouble());
                    else res = Value(v1.asInt() - v2.asInt());
                } else if (op == "*") {
                    if (resIsFloat) res = Value(v1.asDouble() * v2.asDouble());
                    else res = Value(v1.asInt() * v2.asInt());
                } else if (op == "/") {
                    if (v2.asDouble() == 0.0) {
                        cerr << "Runtime error: division by zero during execution\n";
                        return false;
                    }
                    if (resIsFloat) res = Value(v1.asDouble() / v2.asDouble());
                    else res = Value(v1.asInt() / v2.asInt());
                } else if (op == "%") {
                    if (v2.asInt() == 0) {
                        cerr << "Runtime error: modulo by zero during execution\n";
                        return false;
                    }
                    res = Value(v1.asInt() % v2.asInt());
                } else if (op == "==") {
                    res = Value((long long)(resIsFloat ? (v1.asDouble() == v2.asDouble()) : (v1.asInt() == v2.asInt())));
                } else if (op == "!=") {
                    res = Value((long long)(resIsFloat ? (v1.asDouble() != v2.asDouble()) : (v1.asInt() != v2.asInt())));
                } else if (op == "<") {
                    res = Value((long long)(v1.asDouble() < v2.asDouble()));
                } else if (op == "<=") {
                    res = Value((long long)(v1.asDouble() <= v2.asDouble()));
                } else if (op == ">") {
                    res = Value((long long)(v1.asDouble() > v2.asDouble()));
                } else if (op == ">=") {
                    res = Value((long long)(v1.asDouble() >= v2.asDouble()));
                }
                if (!store(dest, res, fr)) return false;
                continue;
            }

            Value v = eval(rest, fr);
            if (!store(dest, v, fr)) return false;
        }
        return true;
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
    string path; bool showTokens = false, trace = false, fold = true, runInterp = false;
    for (int i = 1; i < argc; i++) {
        string a = argv[i];
        if (a == "--tokens") showTokens = true;
        else if (a == "--trace") trace = true;
        else if (a == "--no-fold") fold = false;
        else if (a == "--run") runInterp = true;
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
    bool lexicalErrors = !diags.empty();
    parser.parseProgram();
    parser.finish(lexicalErrors);
    if (trace) cout << "\n";

    {
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
        cout << left << setw(12) << "Name" << setw(12) << "TAC name" << setw(8) << "Type"
             << setw(11) << "Kind" << setw(16) << "Scope" << "Declared (line)\n";
        for (auto& s : parser.allSymbols()) {
            string kind = s.isParam ? string("param") : s.isArray ? "array[" + to_string(s.size) + "]" : string("var");
            cout << left << setw(12) << s.name << setw(12) << s.uname << setw(8) << typeName(s.type)
                 << setw(11) << kind << setw(16) << s.scope << s.line << "\n";
        }

        if (!parser.functionOrder().empty()) {
            cout << "\n---- FUNCTION TABLE ----\n";
            cout << left << setw(12) << "Name" << setw(9) << "Returns" << setw(24) << "Parameters" << "Declared (line)\n";
            for (auto& n : parser.functionOrder()) {
                const FuncInfo& f = parser.functions().at(n);
                string ps;
                for (size_t i = 0; i < f.ptypes.size(); i++)
                    ps += (i ? ", " : "") + string(typeName(f.ptypes[i])) + " " + f.pnames[i];
                if (ps.empty()) ps = "(none)";
                cout << left << setw(12) << f.name << setw(9) << typeName(f.ret) << setw(24) << ps << f.line << "\n";
            }
        }

        cout << "\n---- THREE-ADDRESS CODE ----\n";
        if (!parser.functionOrder().empty()) cout << "-- main program --\n";
        int k = 1;
        for (auto& l : parser.code()) cout << right << setw(3) << k++ << ": " << l << "\n";
        for (auto& n : parser.functionOrder()) {
            const FuncInfo& f = parser.functions().at(n);
            cout << "\n-- function " << f.name << " --\n";
            k = 1;
            for (auto& l : f.code) cout << right << setw(3) << k++ << ": " << l << "\n";
        }
        cout << "\nStatements: " << parser.statementsOk() << "   Constant expressions folded: "
             << parser.foldedCount() << "\n";

        if (runInterp) {
            Interpreter interp(parser.code(), parser.functions(), parser.allSymbols());
            if (!interp.run()) return 3;
        }
        return 0;
    }
    cout << "\nCompilation failed: " << errors << " error(s), " << warnings << " warning(s).\n";
    cout << "Statements: " << parser.statementsOk() << " parsed, " << parser.statementsFailed()
         << " skipped after a syntax error.\n";
    return 1;
}
