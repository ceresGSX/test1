#include <fstream>
#include <cassert>
#include <string>
#include <vector>
#include <functional>
#include <unordered_map>
#include <unordered_set>
#include <stack>
#include <iostream>
using namespace std;

enum class Necessary_condition
{
    NECESSARY,
    UNNECESSARY,
    LOOPNECESSARY,
    LOOPUNNECESSARY,
    INSERT
};

enum class State
{
    EQL,
    GRE,
    NOT,
    LSS,
    MOD,
    PLUS,
    IFTK,
    START,
    INTCON,
    ASSIGN,
    LEQ,
    NEQ,
    GEQ,
    DIV,
    AND,
    MULT,
    MINU,
    COMMA,
    STRCON,
    SEMICN,
    LPARENT,
    LBRACK,
    VOIDTK,
    LBRACE,
    IDENFR,
    WHILETK,
    GETINTTK,
    RPARENT,
    RBRACK,
    ELSETK,
    RBRACE,
    MAINTK,
    CONSTTK,
    PRINTFTK,
    OR,
    INTTK,
    RBRAC,
    BREAKTK,
    ANNOTATION,
    CONTINUETK,
    RETURNTK,

    Decl,
    RelExp,
    Block,
    FuncDef,
    FuncType,
    ConstDecl,
    Stmt,
    MulExp,
    EqExp,
    LAndExp,
    CompUnit,
    BlockItem,
    LVal,
    VarDef,
    Number,
    VarDecl,
    ConstExp,
    FuncFParam,
    Cond,
    AddExp,
    LOrExp,
    InitVal,
    UnaryExp,
    PrimaryExp,
    Exp,
    BType,
    ConstDef,
    MainFuncDef,
    FuncFParams,
    FuncRParams,
    ConstInitVal,
    UnaryOp,

    Blank,

    ADDEXP,
    MULEXP,
    LOREXP,
    LANDEXP,
    EQEXP,
    RELEXP
};

unordered_map<State, string> Get_state = {
    {State::ANNOTATION, "ANNOTATION"},
    {State::GETINTTK, "GETINTTK"},
    {State::CONTINUETK, "CONTINUETK"},
    {State::PRINTFTK, "PRINTFTK"},
    {State::GRE, "GRE"},
    {State::MINU, "MINU"},
    {State::INTTK, "INTTK"},
    {State::LSS, "LSS"},
    {State::IFTK, "IFTK"},
    {State::COMMA, "COMMA"},
    {State::MOD, "MOD"},
    {State::PLUS, "PLUS"},
    {State::START, "START"},
    {State::LEQ, "LEQ"},
    {State::INTCON, "INTCON"},
    {State::RBRACK, "RBRACK"},
    {State::NEQ, "NEQ"},
    {State::ASSIGN, "ASSIGN"},
    {State::VOIDTK, "VOIDTK"},
    {State::GEQ, "GEQ"},
    {State::STRCON, "STRCON"},
    {State::IDENFR, "IDENFR"},
    {State::AND, "AND"},
    {State::SEMICN, "SEMICN"},
    {State::RBRACE, "RBRACE"},
    {State::EQL, "EQL"},
    {State::LBRACE, "LBRACE"},
    {State::BREAKTK, "BREAKTK"},
    {State::NOT, "NOT"},
    {State::LBRACK, "LBRACK"},
    {State::RETURNTK, "RETURNTK"},
    {State::WHILETK, "WHILETK"},
    {State::ELSETK, "ELSETK"},
    {State::LPARENT, "LPARENT"},
    {State::RPARENT, "RPARENT"},
    {State::MAINTK, "MAINTK"},
    {State::CONSTTK, "CONSTTK"},
    {State::OR, "OR"},
    {State::DIV, "DIV"},
    {State::MULT, "MULT"},
    {State::RBRAC, "RBRAC"},

    {State::Decl, "<Decl>"},
    {State::EqExp, "<EqExp>"},
    {State::AddExp, "<AddExp>"},
    {State::Stmt, "<Stmt>"},
    {State::Block, "<Block>"},
    {State::MulExp, "<MulExp>"},
    {State::LVal, "<LVal>"},
    {State::RelExp, "<RelExp>"},
    {State::LOrExp, "<LOrExp>"},
    {State::Cond, "<Cond>"},
    {State::VarDef, "<VarDef>"},
    {State::Number, "<Number>"},
    {State::LAndExp, "<LAndExp>"},
    {State::UnaryExp, "<UnaryExp>"},
    {State::ConstDecl, "<ConstDecl>"},
    {State::FuncDef, "<FuncDef>"},
    {State::CompUnit, "<CompUnit>"},
    {State::BlockItem, "<BlockItem>"},
    {State::VarDecl, "<VarDecl>"},
    {State::FuncType, "<FuncType>"},
    {State::FuncFParam, "<FuncFParam>"},
    {State::InitVal, "<InitVal>"},
    {State::ConstExp, "<ConstExp>"},
    {State::PrimaryExp, "<PrimaryExp>"},
    {State::MainFuncDef, "<MainFuncDef>"},
    {State::ConstDef, "<ConstDef>"},
    {State::UnaryOp, "<UnaryOp>"},
    {State::FuncFParams, "<FuncFParams>"},
    {State::ConstInitVal, "<ConstInitVal>"},
    {State::FuncRParams, "<FuncRParams>"},
    {State::Exp, "<Exp>"},
    {State::BType, "<BType>"},
};

unordered_set<State> check = {
    State::BType,
    State::MULEXP,
    State::RELEXP,
    State::UnaryOp,
    State::Decl,
    State::EQEXP,
    State::ADDEXP,
    State::LOREXP,
    State::LANDEXP,
    State::BlockItem};

template <class type>
struct NODE
{
    type data;
    NODE *prev;
    NODE *next;

    NODE()
    {
        this->prev = nullptr;
        this->next = nullptr;
    }
    NODE(type data, NODE *prev = nullptr, NODE *next = nullptr)
    {
        this->data = data;
        this->prev = prev;
        this->next = next;
    }
};

template <class type>
class List
{
private:
    NODE<type> *Head;
    NODE<type> *Tail;

public:
    class List_Iterator
    {
    private:
        NODE<type> *ptr;

    public:
        List_Iterator(NODE<type> *ptr)
        {
            this->ptr = ptr;
        }

        type &operator*()
        {
            return ptr->data;
        }

        type *operator->()
        {
            return &ptr->data;
        }

        List_Iterator &operator++()
        {
            if (this->ptr->next)
            {
                this->ptr = this->ptr->next;
            }
            else
            {
                assert(false);
            }
            return *this;
        }

        List_Iterator &operator--()
        {
            if (this->ptr->prev)
            {
                this->ptr = this->ptr->prev;
            }
            else
            {
                assert(false);
            }
            return *this;
        }

        List_Iterator operator++(int)
        {
            List_Iterator It = *this;
            ++(*this);
            return It;
        }

        List_Iterator operator--(int)
        {
            List_Iterator It = *this;
            --(*this);
            return It;
        }

        List_Iterator &operator=(const List_Iterator &other)
        {
            if (this != &other)
            {
                this->ptr = other.ptr;
            }
            return *this;
        }

        bool operator==(const List_Iterator &other) const
        {
            return ptr == other.ptr;
        }

        bool operator!=(const List_Iterator &other) const
        {
            return ptr != other.ptr;
        }

        void push_back(type T)
        {
            NODE<type> *next_node = new NODE<type>(T, this->ptr, this->ptr->next);
            ptr->next->prev = next_node, ptr->next = next_node;
        }

        void push_front(type T)
        {
            NODE<type> *next_node = new NODE<type>(T, this->ptr->prev, this->ptr);
            ptr->prev->next = next_node, ptr->prev = next_node;
        }
    };

    List()
    {
        Head = new NODE<type>();
        Tail = new NODE<type>();
        Head->next = Tail, Tail->prev = Head;
    }

    void push_back(type T)
    {
        NODE<type> *new_Node = new NODE<type>(T, Tail->prev, Tail);
        Tail->prev->next = new_Node, Tail->prev = new_Node;
    }

    List_Iterator begin()
    {
        return List_Iterator(Head->next);
    }

    List_Iterator end()
    {
        return List_Iterator(Tail);
    }

    List_Iterator rbegin()
    {
        return List_Iterator(Tail->prev);
    }

    List_Iterator rend()
    {
        return List_Iterator(Head);
    }
};

List<pair<State, string>> Lexical_analysis;
unordered_map<State, vector<vector<pair<State, Necessary_condition>>>> Production;

using Iterator = List<pair<State, string>>::List_Iterator;

struct AutoMaton
{
    State state;
    unordered_map<char, AutoMaton *> next_state;
    bool is_alpha = false;

    AutoMaton(bool check = false) : state(State::IDENFR), is_alpha(check) {}
    AutoMaton(State st) : state(st) {}

    void insert(string name, State st)
    {
        AutoMaton *now_automaton = this;
        for (char &ch : name)
        {
            if (!now_automaton->next_state.count(ch))
            {
                now_automaton->next_state[ch] = (isalpha(ch) ? new AutoMaton(true) : new AutoMaton());
            }
            now_automaton = now_automaton->next_state[ch];
        }
        now_automaton->state = st;
    }
};

struct Grammatical_Analysis
{
public:
    void insert(State Left_part, vector<pair<State, Necessary_condition>> Right_part)
    {
        Production[Left_part].emplace_back(Right_part);
    }

    pair<bool, vector<pair<Iterator, State>>> Analysis(State st, Iterator It)
    {
        for (auto &vt : Production[st])
        {
            vector<pair<Iterator, State>> ans;
            auto mid = It;
            bool is_in_loop = false;
            int index = -1;
            function<pair<bool, Iterator>(int, int, Iterator)> check_loop = [&](int Begin, int End, Iterator Iter)
            {
                vector<pair<Iterator, State>> Loop_ans;
                for (int i = Begin; i < End; ++i)
                {
                    if (Production.count(vt[i].first))
                    {
                        auto res = Analysis(vt[i].first, Iter);
                        if (!res.first)
                        {
                            if (vt[i].second == Necessary_condition::LOOPNECESSARY)
                                return make_pair(false, Iter);
                        }
                        else
                        {
                            Loop_ans.insert(Loop_ans.end(), res.second.begin(), res.second.end());
                            Iter = res.second.back().first;
                        }
                    }
                    else if (vt[i].first != Iter->first)
                    {
                        if (vt[i].second == Necessary_condition::LOOPNECESSARY)
                            return make_pair(false, Iter);
                    }
                    else
                    {
                        ++Iter;
                    }
                }
                ans.insert(ans.end(), Loop_ans.begin(), Loop_ans.end());
                return make_pair(true, Iter);
            };
            for (int i = 0; i < vt.size(); ++i)
            {
                function<void()> loop = [&]()
                {
                    while (true)
                    {
                        auto loop_res = check_loop(index, i, mid);
                        if (loop_res.first)
                        {
                            mid = loop_res.second;
                        }
                        else
                            break;
                    }
                };
                if (vt[i].second == Necessary_condition::INSERT)
                {
                    ans.emplace_back(mid, vt[i].first);
                }
                else if (vt[i].second == Necessary_condition::LOOPNECESSARY || vt[i].second == Necessary_condition::LOOPUNNECESSARY)
                {
                    if (!is_in_loop)
                        index = i;
                    is_in_loop = true;
                    continue;
                }
                else
                {
                    if (is_in_loop)
                    {
                        loop();
                        is_in_loop = false;
                    }
                }
                if (Production.count(vt[i].first))
                {
                    auto res = Analysis(vt[i].first, mid);
                    if (!res.first)
                    {
                        if (vt[i].second == Necessary_condition::NECESSARY)
                            break;
                    }
                    else
                    {
                        ans.insert(ans.end(), res.second.begin(), res.second.end());
                        mid = res.second.back().first;
                    }
                }
                else if (vt[i].first != mid->first)
                {
                    if (vt[i].second == Necessary_condition::NECESSARY)
                        break;
                }
                else
                {
                    ++mid;
                }
                if (i == vt.size() - 1)
                {
                    ans.emplace_back(mid, st);
                    return {true, ans};
                }
            }
        }
        return {false, {}};
    }
};

char c;
string words;
bool One_line_comment, Comment, Have_star;

AutoMaton *Start_automaton, *IDENFR, *ANNOTATION, *Automaton, *INTCON, *STRCON;
Grammatical_Analysis *Analysiser;

void insert_words()
{
    if (!words.empty())
    {
        Lexical_analysis.push_back({Automaton->state, words});
        words.clear();
    }
}

void work(char c)
{
    if (isspace(c) && !(Automaton->state == State::ANNOTATION || Automaton->state == State::STRCON))
    {
        insert_words();
        Automaton = Start_automaton;
        return;
    }
    switch (Automaton->state)
    {
    case State::START:
    {
        if (isdigit(c))
        {
            Automaton = INTCON;
        }
        else if (c == '/')
        {
            Automaton = ANNOTATION;
        }
        else if (c == '"')
        {
            Automaton = STRCON;
        }
        else
        {
            auto Next_state = Automaton->next_state.find(c);
            if (Next_state != Automaton->next_state.end())
            {
                Automaton = Next_state->second;
            }
            else
            {
                Automaton = IDENFR;
            }
        }
        if (c != '/')
            words += c;
        break;
    }
    case State::ANNOTATION:
    {
        if (!One_line_comment && !Comment)
        {
            if (c == '/')
            {
                One_line_comment = true;
            }
            else if (c == '*')
            {
                Comment = true;
            }
            else
            {
                Lexical_analysis.push_back({State::DIV, "/"});
                Automaton = Start_automaton;
                work(c);
            }
        }
        else
        {
            if (One_line_comment && c == '\n')
            {
                One_line_comment = false;
                Automaton = Start_automaton;
            }
            else if (Comment)
            {
                if (c == '*')
                    Have_star = true;
                else if (c == '/' && Have_star)
                {
                    Comment = false;
                    Automaton = Start_automaton;
                }
                else
                    Have_star = false;
            }
        }
        break;
    }
    case State::STRCON:
    {
        words += c;
        if (c == '"')
        {
            Lexical_analysis.push_back({State::STRCON, words});
            words.clear();
            Automaton = Start_automaton;
        }
        break;
    }
    default:
    {
        auto Next_state = Automaton->next_state.find(c);
        if (Next_state != Automaton->next_state.end())
        {
            Automaton = Next_state->second;
            words += c;
        }
        else
        {
            if (Automaton->is_alpha && isalnum(c))
            {
                Automaton = IDENFR;
                words += c;
            }
            else
            {
                Lexical_analysis.push_back({Automaton->state, words});
                Automaton = Start_automaton;
                words.clear();
                work(c);
            }
        }
        break;
    }
    }
}

void init()
{
    Automaton = Start_automaton = new AutoMaton(State::START);
    ANNOTATION = new AutoMaton(State::ANNOTATION), IDENFR = new AutoMaton(true);
    INTCON = new AutoMaton(State::INTCON), STRCON = new AutoMaton(State::STRCON);
    for (char i = '0'; i <= '9'; ++i)
    {
        INTCON->next_state[i] = INTCON;
    }
    Automaton->insert("<=", State::LEQ);
    Automaton->insert(">", State::GRE);
    Automaton->insert(">=", State::GEQ);
    Automaton->insert("<", State::LSS);
    Automaton->insert("!=", State::NEQ);
    Automaton->insert("!", State::NOT);
    Automaton->insert("==", State::EQL);
    Automaton->insert("%", State::MOD);
    Automaton->insert("+", State::PLUS);
    Automaton->insert("/", State::DIV);
    Automaton->insert("*", State::MULT);
    Automaton->insert("||", State::OR);
    Automaton->insert("-", State::MINU);
    Automaton->insert("if", State::IFTK);
    Automaton->insert("&&", State::AND);
    Automaton->insert(",", State::COMMA);
    Automaton->insert("=", State::ASSIGN);
    Automaton->insert("(", State::LPARENT);
    Automaton->insert(";", State::SEMICN);
    Automaton->insert(")", State::RPARENT);
    Automaton->insert("[", State::LBRACK);
    Automaton->insert("int", State::INTTK);
    Automaton->insert("]", State::RBRACK);
    Automaton->insert("void", State::VOIDTK);
    Automaton->insert("{", State::LBRACE);
    Automaton->insert("else", State::ELSETK);
    Automaton->insert("}", State::RBRACE);
    Automaton->insert("main", State::MAINTK);
    Automaton->insert("ident", State::IDENFR);
    Automaton->insert("while", State::WHILETK);
    Automaton->insert("const", State::CONSTTK);
    Automaton->insert("break", State::BREAKTK);
    Automaton->insert("getint", State::GETINTTK);
    Automaton->insert("printf", State::PRINTFTK);
    Automaton->insert("return", State::RETURNTK);
    Automaton->insert("intConst", State::INTCON);
    Automaton->insert("FormatString", State::STRCON);
    Automaton->insert("continue", State::CONTINUETK);

    Analysiser = new Grammatical_Analysis();
    Analysiser->insert(State::CompUnit, {{State::Decl, Necessary_condition::LOOPNECESSARY},
                                         {State::Blank, Necessary_condition::UNNECESSARY},
                                         {State::FuncDef, Necessary_condition::LOOPNECESSARY},
                                         {State::MainFuncDef, Necessary_condition::NECESSARY}});

    Analysiser->insert(State::Decl, {
                                        {State::ConstDecl, Necessary_condition::NECESSARY},
                                    });
    Analysiser->insert(State::Decl, {
                                        {State::VarDecl, Necessary_condition::NECESSARY},
                                    });

    Analysiser->insert(State::FuncDef, {{State::FuncType, Necessary_condition::NECESSARY},
                                        {State::IDENFR, Necessary_condition::NECESSARY},
                                        {State::LPARENT, Necessary_condition::NECESSARY},
                                        {State::FuncFParams, Necessary_condition::UNNECESSARY},
                                        {State::RPARENT, Necessary_condition::NECESSARY},
                                        {State::Block, Necessary_condition::NECESSARY}});

    Analysiser->insert(State::MainFuncDef, {{State::INTTK, Necessary_condition::NECESSARY},
                                            {State::MAINTK, Necessary_condition::NECESSARY},
                                            {State::LPARENT, Necessary_condition::NECESSARY},
                                            {State::RPARENT, Necessary_condition::NECESSARY},
                                            {State::Block, Necessary_condition::NECESSARY}});

    Analysiser->insert(State::ConstDecl, {
                                             {State::CONSTTK, Necessary_condition::NECESSARY},
                                             {State::BType, Necessary_condition::NECESSARY},
                                             {State::ConstDef, Necessary_condition::NECESSARY},
                                             {State::COMMA, Necessary_condition::LOOPNECESSARY},
                                             {State::ConstDef, Necessary_condition::LOOPNECESSARY},
                                             {State::SEMICN, Necessary_condition::NECESSARY},
                                         });

    Analysiser->insert(State::VarDecl, {
                                           {State::BType, Necessary_condition::NECESSARY},
                                           {State::VarDef, Necessary_condition::NECESSARY},
                                           {State::COMMA, Necessary_condition::LOOPNECESSARY},
                                           {State::VarDef, Necessary_condition::LOOPNECESSARY},
                                           {State::SEMICN, Necessary_condition::NECESSARY},
                                       });

    Analysiser->insert(State::FuncType, {
                                            {State::VOIDTK, Necessary_condition::NECESSARY},
                                        });
    Analysiser->insert(State::FuncType, {
                                            {State::INTTK, Necessary_condition::NECESSARY},
                                        });

    Analysiser->insert(State::FuncFParams, {
                                               {State::FuncFParam, Necessary_condition::NECESSARY},
                                               {State::COMMA, Necessary_condition::LOOPNECESSARY},
                                               {State::FuncFParam, Necessary_condition::LOOPNECESSARY},
                                               {State::Blank, Necessary_condition::UNNECESSARY},
                                           });

    Analysiser->insert(State::Block, {{State::LBRACE, Necessary_condition::NECESSARY},
                                      {State::BlockItem, Necessary_condition::LOOPNECESSARY},
                                      {State::RBRACE, Necessary_condition::NECESSARY}});

    Analysiser->insert(State::BType, {
                                         {State::INTTK, Necessary_condition::NECESSARY},
                                     });

    Analysiser->insert(State::VarDef, {{State::IDENFR, Necessary_condition::NECESSARY},
                                       {State::LBRACK, Necessary_condition::LOOPNECESSARY},
                                       {State::ConstExp, Necessary_condition::LOOPNECESSARY},
                                       {State::RBRACK, Necessary_condition::LOOPNECESSARY},
                                       {State::ASSIGN, Necessary_condition::UNNECESSARY},
                                       {State::InitVal, Necessary_condition::UNNECESSARY}});

    Analysiser->insert(State::FuncFParam, {{State::BType, Necessary_condition::NECESSARY},
                                           {State::IDENFR, Necessary_condition::NECESSARY},
                                           {State::LBRACK, Necessary_condition::UNNECESSARY},
                                           {State::RBRACK, Necessary_condition::UNNECESSARY},
                                           {State::LBRACK, Necessary_condition::LOOPNECESSARY},
                                           {State::ConstExp, Necessary_condition::LOOPNECESSARY},
                                           {State::RBRACK, Necessary_condition::LOOPNECESSARY},
                                           {State::Blank, Necessary_condition::UNNECESSARY}});

    Analysiser->insert(State::BlockItem, {{State::Decl, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::BlockItem, {{State::Stmt, Necessary_condition::NECESSARY}});

    Analysiser->insert(State::ConstExp, {{State::AddExp, Necessary_condition::NECESSARY}});

    Analysiser->insert(State::InitVal, {{State::UnaryOp, Necessary_condition::UNNECESSARY},
                                        {State::Exp, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::InitVal, {{State::LBRACE, Necessary_condition::NECESSARY},
                                        {State::InitVal, Necessary_condition::UNNECESSARY},
                                        {State::COMMA, Necessary_condition::LOOPNECESSARY},
                                        {State::InitVal, Necessary_condition::LOOPNECESSARY},
                                        {State::RBRACE, Necessary_condition::NECESSARY}});

    Analysiser->insert(State::Stmt, {{State::LVal, Necessary_condition::NECESSARY},
                                     {State::ASSIGN, Necessary_condition::NECESSARY},
                                     {State::UnaryOp, Necessary_condition::UNNECESSARY},
                                     {State::Exp, Necessary_condition::NECESSARY},
                                     {State::SEMICN, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::Stmt, {{State::Exp, Necessary_condition::UNNECESSARY},
                                     {State::SEMICN, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::Stmt, {
                                        {State::Block, Necessary_condition::NECESSARY},
                                    });
    Analysiser->insert(State::Stmt, {{State::IFTK, Necessary_condition::NECESSARY},
                                     {State::LPARENT, Necessary_condition::NECESSARY},
                                     {State::Cond, Necessary_condition::NECESSARY},
                                     {State::RPARENT, Necessary_condition::NECESSARY},
                                     {State::Stmt, Necessary_condition::NECESSARY},
                                     {State::ELSETK, Necessary_condition::NECESSARY},
                                     {State::Stmt, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::Stmt, {
                                        {State::IFTK, Necessary_condition::NECESSARY},
                                        {State::LPARENT, Necessary_condition::NECESSARY},
                                        {State::Cond, Necessary_condition::NECESSARY},
                                        {State::RPARENT, Necessary_condition::NECESSARY},
                                        {State::Stmt, Necessary_condition::NECESSARY},
                                    });
    Analysiser->insert(State::Stmt, {{State::WHILETK, Necessary_condition::NECESSARY},
                                     {State::LPARENT, Necessary_condition::NECESSARY},
                                     {State::Cond, Necessary_condition::NECESSARY},
                                     {State::RPARENT, Necessary_condition::NECESSARY},
                                     {State::Stmt, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::Stmt, {{State::BREAKTK, Necessary_condition::NECESSARY},
                                     {State::SEMICN, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::Stmt, {{State::CONTINUETK, Necessary_condition::NECESSARY},
                                     {State::SEMICN, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::Stmt, {{State::RETURNTK, Necessary_condition::NECESSARY},
                                     {State::Exp, Necessary_condition::UNNECESSARY},
                                     {State::SEMICN, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::Stmt, {{State::LVal, Necessary_condition::NECESSARY},
                                     {State::ASSIGN, Necessary_condition::NECESSARY},
                                     {State::GETINTTK, Necessary_condition::NECESSARY},
                                     {State::LPARENT, Necessary_condition::NECESSARY},
                                     {State::RPARENT, Necessary_condition::NECESSARY},
                                     {State::SEMICN, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::Stmt, {{State::PRINTFTK, Necessary_condition::NECESSARY},
                                     {State::LPARENT, Necessary_condition::NECESSARY},
                                     {State::STRCON, Necessary_condition::NECESSARY},
                                     {State::COMMA, Necessary_condition::LOOPNECESSARY},
                                     {State::Exp, Necessary_condition::LOOPNECESSARY},
                                     {State::RPARENT, Necessary_condition::NECESSARY},
                                     {State::SEMICN, Necessary_condition::NECESSARY}});

    Analysiser->insert(State::AddExp, {{State::MulExp, Necessary_condition::NECESSARY},
                                       {State::ADDEXP, Necessary_condition::UNNECESSARY}});
    Analysiser->insert(State::ADDEXP, {{State::AddExp, Necessary_condition::INSERT},
                                       {State::UnaryOp, Necessary_condition::NECESSARY},
                                       {State::MulExp, Necessary_condition::NECESSARY},
                                       {State::ADDEXP, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::ADDEXP, {{State::Blank, Necessary_condition::UNNECESSARY}});

    Analysiser->insert(State::Exp, {{State::AddExp, Necessary_condition::NECESSARY}});

    Analysiser->insert(State::LVal, {
                                        {State::IDENFR, Necessary_condition::NECESSARY},
                                        {State::LBRACK, Necessary_condition::LOOPNECESSARY},
                                        {State::Exp, Necessary_condition::LOOPNECESSARY},
                                        {State::RBRACK, Necessary_condition::LOOPNECESSARY},
                                        {State::Blank, Necessary_condition::UNNECESSARY},
                                    });

    Analysiser->insert(State::Cond, {{State::LOrExp, Necessary_condition::NECESSARY}});

    Analysiser->insert(State::MulExp, {
                                          {State::UnaryExp, Necessary_condition::NECESSARY},
                                          {State::MULEXP, Necessary_condition::UNNECESSARY},
                                      });
    Analysiser->insert(State::MULEXP, {{State::MulExp, Necessary_condition::INSERT},
                                       {State::MULT, Necessary_condition::NECESSARY},
                                       {State::UnaryExp, Necessary_condition::NECESSARY},
                                       {State::MULEXP, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::MULEXP, {{State::MulExp, Necessary_condition::INSERT},
                                       {State::DIV, Necessary_condition::NECESSARY},
                                       {State::UnaryExp, Necessary_condition::NECESSARY},
                                       {State::MULEXP, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::MULEXP, {{State::MulExp, Necessary_condition::INSERT},
                                       {State::MOD, Necessary_condition::NECESSARY},
                                       {State::UnaryExp, Necessary_condition::NECESSARY},
                                       {State::MULEXP, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::MULEXP, {{State::Blank, Necessary_condition::UNNECESSARY}});

    Analysiser->insert(State::LOrExp, {{State::LAndExp, Necessary_condition::NECESSARY},
                                       {State::LOREXP, Necessary_condition::UNNECESSARY}});
    Analysiser->insert(State::LOREXP, {
                                          {State::LOrExp, Necessary_condition::INSERT},
                                          {State::OR, Necessary_condition::NECESSARY},
                                          {State::LAndExp, Necessary_condition::NECESSARY},
                                          {State::LOREXP, Necessary_condition::NECESSARY},
                                      });
    Analysiser->insert(State::LOREXP, {{State::Blank, Necessary_condition::UNNECESSARY}});

    Analysiser->insert(State::LAndExp, {
                                           {State::EqExp, Necessary_condition::NECESSARY},
                                           {State::LANDEXP, Necessary_condition::UNNECESSARY},
                                       });
    Analysiser->insert(State::LANDEXP, {{State::LAndExp, Necessary_condition::INSERT},
                                        {State::AND, Necessary_condition::NECESSARY},
                                        {State::EqExp, Necessary_condition::NECESSARY},
                                        {State::LANDEXP, Necessary_condition::UNNECESSARY}});
    Analysiser->insert(State::LANDEXP, {
                                           {State::Blank, Necessary_condition::UNNECESSARY},
                                       });

    Analysiser->insert(State::EqExp, {
                                         {State::RelExp, Necessary_condition::NECESSARY},
                                         {State::EQEXP, Necessary_condition::UNNECESSARY},
                                     });
    Analysiser->insert(State::EQEXP, {{State::EqExp, Necessary_condition::INSERT},
                                      {State::EQL, Necessary_condition::NECESSARY},
                                      {State::RelExp, Necessary_condition::NECESSARY},
                                      {State::EQEXP, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::EQEXP, {{State::EqExp, Necessary_condition::INSERT},
                                      {State::NEQ, Necessary_condition::NECESSARY},
                                      {State::RelExp, Necessary_condition::NECESSARY},
                                      {State::EQEXP, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::EQEXP, {{State::Blank, Necessary_condition::UNNECESSARY}});

    Analysiser->insert(State::UnaryExp, {{State::IDENFR, Necessary_condition::NECESSARY},
                                         {State::LPARENT, Necessary_condition::NECESSARY},
                                         {State::FuncRParams, Necessary_condition::UNNECESSARY},
                                         {State::RPARENT, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::UnaryExp, {{State::PrimaryExp, Necessary_condition::NECESSARY}});

    Analysiser->insert(State::RelExp, {{State::UnaryOp, Necessary_condition::UNNECESSARY},
                                       {State::AddExp, Necessary_condition::NECESSARY},
                                       {State::RELEXP, Necessary_condition::UNNECESSARY}});
    Analysiser->insert(State::RELEXP, {{State::RelExp, Necessary_condition::INSERT},
                                       {State::LSS, Necessary_condition::NECESSARY},
                                       {State::UnaryOp, Necessary_condition::UNNECESSARY},
                                       {State::AddExp, Necessary_condition::NECESSARY},
                                       {State::RELEXP, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::RELEXP, {{State::RelExp, Necessary_condition::INSERT},
                                       {State::GRE, Necessary_condition::NECESSARY},
                                       {State::UnaryOp, Necessary_condition::UNNECESSARY},
                                       {State::AddExp, Necessary_condition::NECESSARY},
                                       {State::RELEXP, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::RELEXP, {{State::RelExp, Necessary_condition::INSERT},
                                       {State::LEQ, Necessary_condition::NECESSARY},
                                       {State::AddExp, Necessary_condition::NECESSARY},
                                       {State::RELEXP, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::RELEXP, {{State::RelExp, Necessary_condition::INSERT},
                                       {State::GEQ, Necessary_condition::NECESSARY},
                                       {State::AddExp, Necessary_condition::NECESSARY},
                                       {State::RELEXP, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::RELEXP, {{State::Blank, Necessary_condition::UNNECESSARY}});

    Analysiser->insert(State::PrimaryExp, {{State::LVal, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::PrimaryExp, {{State::LPARENT, Necessary_condition::NECESSARY},
                                           {State::UnaryOp, Necessary_condition::UNNECESSARY},
                                           {State::Exp, Necessary_condition::NECESSARY},
                                           {State::RPARENT, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::PrimaryExp, {{State::Number, Necessary_condition::NECESSARY}});

    Analysiser->insert(State::FuncRParams, {
                                               {State::Exp, Necessary_condition::NECESSARY},
                                               {State::COMMA, Necessary_condition::LOOPNECESSARY},
                                               {State::Exp, Necessary_condition::LOOPNECESSARY},
                                               {State::Blank, Necessary_condition::UNNECESSARY},
                                           });

    Analysiser->insert(State::Number, {{State::INTCON, Necessary_condition::NECESSARY}});

    Analysiser->insert(State::ConstDef, {{State::IDENFR, Necessary_condition::NECESSARY},
                                         {State::LBRACK, Necessary_condition::LOOPNECESSARY},
                                         {State::ConstExp, Necessary_condition::LOOPNECESSARY},
                                         {State::RBRACK, Necessary_condition::LOOPNECESSARY},
                                         {State::ASSIGN, Necessary_condition::NECESSARY},
                                         {State::ConstInitVal, Necessary_condition::NECESSARY}});

    Analysiser->insert(State::ConstInitVal, {{State::ConstExp, Necessary_condition::NECESSARY}});
    Analysiser->insert(State::ConstInitVal, {{State::LBRACE, Necessary_condition::NECESSARY},
                                             {State::ConstInitVal, Necessary_condition::UNNECESSARY},
                                             {State::COMMA, Necessary_condition::LOOPNECESSARY},
                                             {State::ConstInitVal, Necessary_condition::LOOPNECESSARY},
                                             {State::RBRACE, Necessary_condition::NECESSARY}});

    Analysiser->insert(State::UnaryOp, {{State::MINU, Necessary_condition::NECESSARY},
                                        {State::UnaryOp, Necessary_condition::UNNECESSARY}});
    Analysiser->insert(State::UnaryOp, {{State::PLUS, Necessary_condition::NECESSARY},
                                        {State::UnaryOp, Necessary_condition::UNNECESSARY}});
    Analysiser->insert(State::UnaryOp, {{State::NOT, Necessary_condition::NECESSARY},
                                        {State::UnaryOp, Necessary_condition::UNNECESSARY}});
}

void repair()
{
    bool Have_UnaryExp = false;
    Iterator insert_It = Lexical_analysis.rbegin();
    unordered_set<State> CHECK = {
        State::PrimaryExp, State::LVal, State::Number, State::UnaryOp};
    for (auto it = Lexical_analysis.rbegin(); it != Lexical_analysis.rend(); --it)
    {
        if (it->second == "(")
            Have_UnaryExp = false;
        if (!it->second.empty() && !(it->first == State::MINU || it->first == State::PLUS || it->first == State::NOT))
            continue;
        if (it->first == State::UnaryExp)
        {
            Have_UnaryExp = true, insert_It = it;
            auto mid = it;
            bool flag = true;
            ++mid;
            vector<State> mid_check = {State::MulExp, State::AddExp, State::Exp, State::RBRACK, State::LVal, State::PrimaryExp};
            for (int i = 0; i < mid_check.size(); ++i, ++mid)
            {
                if (mid_check[i] != mid->first)
                {
                    flag = false;
                    break;
                }
            }
            if (mid->first == State::UnaryExp && flag)
                insert_It = mid;
        }
        else if (Have_UnaryExp && (it->first == State::MINU || it->first == State::PLUS || it->first == State::NOT))
        {
            auto mid = it;
            --mid;
            if (mid->first == State::AddExp)
                continue;
            it.push_back({State::UnaryOp, ""}), insert_It.push_back({State::UnaryExp, ""});
        }
        else if (!CHECK.count(it->first))
        {
            Have_UnaryExp = false;
        }
    }
    bool need_Insert = false, Is_Empty = true, need_insert = false;
    for (auto it = Lexical_analysis.begin(); it != Lexical_analysis.end(); ++it)
    {
        if (need_insert && it->first == State::UnaryExp)
        {
            it.push_back({State::UnaryExp, ""});
            need_insert = false;
        }
        if (it->first == State::MINU || it->first == State::PLUS || it->first == State::NOT)
        {
            auto mid = it, pre = it;
            ++mid, --pre;
            if (pre->first != State::LPARENT)
                continue;
            if (mid->second == "(")
            {
                ++mid, Is_Empty = true;
                while (mid->second != ")")
                {
                    ++mid, Is_Empty = false;
                }
                --mid;
                if (mid->first == State::Exp)
                {
                    it.push_back({State::UnaryOp, ""});
                    need_insert = true, it = mid;
                }
            }
        }
    }
}

void read()
{
    ifstream ifs("testfile.txt");
    while (ifs.get(c))
    {
        work(c);
    }
    insert_words();
    ifs.close();
}

void print()
{
    ofstream ofs("output.txt");
    for (auto it = Lexical_analysis.begin(); it != Lexical_analysis.end(); ++it)
    {
        ofs << Get_state[it->first];
        if (!(it->second.empty()))
            ofs << " " << it->second;
        ofs << endl;
    }
    ofs.close();
}

int main()
{
    init();
    read();
    auto res = Analysiser->Analysis(State::CompUnit, Lexical_analysis.begin());
    for (auto x = res.second.begin(); x != res.second.end(); ++x)
    {
        if (check.count(x->second))
            continue;
        x->first.push_front({x->second, ""});
    }
    repair();
    print();
    cout << "李梦雨 202112089" << endl;
    return 0;
}