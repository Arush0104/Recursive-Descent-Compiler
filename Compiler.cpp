
//  Recursive-Descent Compiler - PROJECT REVIEW 1  (BCSE307P Compiler Design Lab)
//
//  Implemented so far : lexical analyser + recursive-descent parser
//                       + basic syntax error detection/reporting
//  Planned (later)    : error recovery, symbol table, semantic checks, TAC
//
//  Grammar (LL(1), left recursion removed)
//  ---------------------------------------
//    program    -> { statement } EOF
//    statement  -> declaration | assignment
//    declaration-> type ID [ '=' expr ] { ',' ID [ '=' expr ] } ';'
//    type       -> 'int' | 'float'
//    assignment -> ID '=' expr ';'
//    expr       -> term   { ('+' | '-') term }
//    term       -> factor { ('*' | '/' | '%') factor }
//    factor     -> ('+' | '-') factor | primary
//    primary    -> INT_LIT | FLOAT_LIT | ID | '(' expr ')'

#include <cctype>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
using namespace std;

enum class T { KW_INT, KW_FLOAT, ID, INT_LIT, FLOAT_LIT, ASSIGN, PLUS, MINUS,
               STAR, SLASH, PERCENT, LPAREN, RPAREN, SEMI, COMMA, END };

struct Token { T type; string lexeme; int line, col; };

static const char* tokName(T t) {
    static const char* n[] = {"KW_INT","KW_FLOAT","ID","INT_LIT","FLOAT_LIT","ASSIGN","PLUS",
                              "MINUS","STAR","SLASH","PERCENT","LPAREN","RPAREN","SEMI","COMMA","EOF"};
    return n[(int)t];
}

struct CompileError { string kind, msg; int line, col; }; 
static vector<Token> lex(const string& src) {
    vector<Token> out;
    size_t i = 0; int line = 1, col = 1;
    auto peek = [&](size_t k = 0) -> char { return i + k < src.size() ? src[i + k] : '\0'; };
    auto adv  = [&]() { if (src[i] == '\n') { line++; col = 1; } else col++; i++; };
    auto idStart = [](char c) { return isalpha((unsigned char)c) || c == '_'; };
    auto idChar  = [](char c) { return isalnum((unsigned char)c) || c == '_'; };

    while (i < src.size()) {
        char c = peek();
        if (isspace((unsigned char)c)) { adv(); continue; }
        if (c == '/' && peek(1) == '/') { while (i < src.size() && peek() != '\n') adv(); continue; }

        int sl = line, sc = col;
        if (idStart(c)) {                                   
            string s;
            while (idChar(peek())) { s += peek(); adv(); }
            out.push_back({s == "int" ? T::KW_INT : s == "float" ? T::KW_FLOAT : T::ID, s, sl, sc});
        } else if (isdigit((unsigned char)c)) {            
            string s; bool isF = false, bad = false;
            while (isdigit((unsigned char)peek())) { s += peek(); adv(); }
            if (peek() == '.') {
                isF = true; s += '.'; adv();
                if (!isdigit((unsigned char)peek())) bad = true;
                while (isdigit((unsigned char)peek())) { s += peek(); adv(); }
            }
            if (idStart(peek())) { while (idChar(peek())) { s += peek(); adv(); } bad = true; }
            if (bad) throw CompileError{"Lexical error", "malformed number '" + s + "'", sl, sc};
            out.push_back({isF ? T::FLOAT_LIT : T::INT_LIT, s, sl, sc});
        } else {                                            // operators / punctuation
            T t;
            switch (c) {
                case '=': t = T::ASSIGN;  break;  case '+': t = T::PLUS;   break;
                case '-': t = T::MINUS;   break;  case '*': t = T::STAR;   break;
                case '/': t = T::SLASH;   break;  case '%': t = T::PERCENT;break;
                case '(': t = T::LPAREN;  break;  case ')': t = T::RPAREN; break;
                case ';': t = T::SEMI;    break;  case ',': t = T::COMMA;  break;
                default: throw CompileError{"Lexical error", string("unexpected character '") + c + "'", sl, sc};
            }
            out.push_back({t, string(1, c), sl, sc});
            adv();
        }
    }
    out.push_back({T::END, "<EOF>", line, col});
    return out;
}

//parser
class Parser {
public:
    explicit Parser(const vector<Token>& t) : toks(t) {}
    void parseProgram() { while (cur().type != T::END) statement(); }
    int statementsParsed() const { return count; }

private:
    const vector<Token>& toks;
    size_t p = 0;
    int count = 0;

    const Token& cur() const { return toks[p]; }
    static string desc(const Token& t) { return t.type == T::END ? "end of file" : "'" + t.lexeme + "'"; }
    bool accept(T t) { if (cur().type == t) { p++; return true; } return false; }

    void expect(T t, const string& what) {
        if (accept(t)) return;
        if (t == T::SEMI && p > 0) {                        
            const Token& pv = toks[p - 1];
            throw CompileError{"Syntax error", "expected ';' after '" + pv.lexeme + "', found " + desc(cur()),
                               pv.line, pv.col + (int)pv.lexeme.size()};
        }
        throw CompileError{"Syntax error", "expected " + what + ", found " + desc(cur()), cur().line, cur().col};
    }

    void statement() {
        if (cur().type == T::KW_INT || cur().type == T::KW_FLOAT) declaration();
        else if (cur().type == T::ID) assignment();
        else throw CompileError{"Syntax error", "expected a declaration or assignment, found " + desc(cur()),
                                cur().line, cur().col};
        count++;
    }
    void declaration() {
        p++;                                           
        do {
            expect(T::ID, "identifier");
            if (accept(T::ASSIGN)) expr();
        } while (accept(T::COMMA));
        expect(T::SEMI, "';'");
    }
    void assignment() { p++; expect(T::ASSIGN, "'='"); expr(); expect(T::SEMI, "';'"); }

    void expr() { term(); while (cur().type == T::PLUS || cur().type == T::MINUS) { p++; term(); } }
    void term() {
        factor();
        while (cur().type == T::STAR || cur().type == T::SLASH || cur().type == T::PERCENT) { p++; factor(); }
    }
    void factor() {
        if (cur().type == T::PLUS || cur().type == T::MINUS) { p++; factor(); }
        else primary();
    }
    void primary() {
        switch (cur().type) {
            case T::INT_LIT: case T::FLOAT_LIT: case T::ID: p++; break;
            case T::LPAREN: p++; expr(); expect(T::RPAREN, "')'"); break;
            default: throw CompileError{"Syntax error", "expected an expression, found " + desc(cur()),
                                        cur().line, cur().col};
        }
    }
};

int main(int argc, char** argv) {
    string path; bool showTokens = false;
    for (int i = 1; i < argc; i++) { string a = argv[i]; if (a == "--tokens") showTokens = true; else path = a; }

    string src;
    if (!path.empty()) {
        ifstream f(path);
        if (!f) { cerr << "Cannot open file: " << path << "\n"; return 2; }
        stringstream ss; ss << f.rdbuf(); src = ss.str();
    } else {
        cerr << "(type source; finish with Ctrl+D, or Ctrl+Z then Enter on Windows)\n";
        stringstream ss; ss << cin.rdbuf(); src = ss.str();
    }

    try {
        vector<Token> toks = lex(src);
        if (showTokens) {
            cout << "TOKENS\n";
            for (auto& t : toks)
                cout << left << setw(7) << (to_string(t.line) + ":" + to_string(t.col))
                     << setw(11) << tokName(t.type) << t.lexeme << "\n";
            cout << "\n";
        }
        Parser parser(toks);
        parser.parseProgram();
        cout << "Parsing successful: " << parser.statementsParsed() << " statement(s), no syntax errors.\n";
        return 0;
    } catch (CompileError& e) {
        stringstream ss(src); string ln;
        for (int i = 1; getline(ss, ln) && i < e.line; i++) {}
        if (!ln.empty() && ln.back() == '\r') ln.pop_back();
        cout << e.kind << " [" << e.line << ":" << e.col << "]: " << e.msg << "\n";
        cout << "  " << setw(4) << e.line << " | " << ln << "\n";
        cout << "       | " << string(e.col > 0 ? e.col - 1 : 0, ' ') << "^\n";
        return 1;
    }
}
