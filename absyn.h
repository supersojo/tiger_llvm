/* Coding: ANSI */
#ifndef ABSYN_H
#define ABSYN_H

#include "tiger_type.h"
#include "tiger_log.h"
#include "tiger_assert.h"
#include "symbol.h"
namespace tiger{

template<typename T,typename U>
bool isa(U* u)
{
    return T::classof(u);
}
template<typename T,typename U>
T* dyn_cast(U* u)
{
    if(isa<T>(u))
        return dynamic_cast<T*>(u);
    TIGER_ASSERT(0,"wrong type cast!!");
}

/*
Var
Dec
Exp
*/
template<typename RetTy,
         typename VarRetTy,
         typename DecRetTy,
         typename ExpRetTy>
class Visitor;

class Node{ //base class of ast tree node
public:
    enum{
        kNode_Var,
        kNode_Dec,
        kNode_Exp,
        kNode_Invalid
    };
    Node(){m_type = kNode_Invalid;}
    Node(s32 type){m_type = type;}
    s32 Type(){return m_type;}
    template<typename RetTy,
         typename VarRetTy,
         typename DecRetTy,
         typename ExpRetTy>
    void Accept(Visitor<RetTy,VarRetTy,DecRetTy,ExpRetTy>& visitor);
    virtual ~Node(){
    }
private:
    s32 m_type;
};
class Var:public Node{
public:
    enum{
        kVar_Simple,
        kVar_Field,
        kVar_Subscript,
        kVar_Invalid
    };
    Var():Node(kNode_Var){m_kind = kVar_Invalid;m_escape=0;/*false*/}
    Var(s32 kind):Node(kNode_Var){m_kind = kind;}
    void SetEscape(s32 escape){m_escape = escape;}
    s32  GetEscape(){return m_escape;}
    virtual s32 Kind(){return m_kind;}
    virtual Var* Clone(){
        Var* n = new Var;
        n->m_kind = m_kind;
        n->m_escape = m_escape;//not used
        return n;
    }
    static bool classof(Var * var){
        return ( (var->Kind()==kVar_Simple)||
                 (var->Kind()==kVar_Field)||
                 (var->Kind()==kVar_Subscript) );
    }
    virtual ~Var(){}
private:
    s32 m_kind;
    s32 m_escape;
};

class SimpleVar:public Var{
public:
    SimpleVar():Var(kVar_Simple){
        m_sym = 0;
    }
    SimpleVar(Symbol* sym):Var(kVar_Simple){
        m_sym = sym;
    }
    Symbol* GetSymbol(){return m_sym;}
    ~SimpleVar(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~SimpleVar");
        delete m_sym;
    }
    SimpleVar* Clone(){
        SimpleVar* n = new SimpleVar;
        n->m_sym = m_sym?m_sym->Clone():0;
        return n;
    }
    static bool classof(Var * var){
        return (var->Kind()==kVar_Simple);
    }
public:
    Symbol* m_sym;
};

class FieldVar:public Var{
public:
    FieldVar():Var(kVar_Field){
        
    }
    FieldVar(Var* var,Symbol* sym):Var(kVar_Field){
        m_var = var;
        m_sym = sym;
    }
    Var* GetVar(){return m_var;}
    Symbol* GetSym(){return m_sym;}
    FieldVar* Clone(){
        FieldVar* n = new FieldVar;
        n->m_var = m_var?m_var->Clone():0;
        n->m_sym = m_sym?m_sym->Clone():0;
        return n;
    }
    ~FieldVar(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~FieldVar");
        delete m_var;
        delete m_sym;
    }
    static bool classof(Var * var){
        return (var->Kind()==kVar_Field);
    }
private:
    Var* m_var;//var 
    Symbol* m_sym;//field
};

/* proto declaration */
class Exp;

class SubscriptVar:public Var{
public:
    SubscriptVar():Var(kVar_Subscript){
    }
    SubscriptVar(Var* var,Exp* exp):Var(kVar_Subscript){
        m_var = var;
        m_exp = exp;
    }
    Var* GetVar(){return m_var;}
    Exp* GetExp(){return m_exp;}
    SubscriptVar* Clone();
    ~SubscriptVar();
    static bool classof(Var * var){
        return (var->Kind()==kVar_Subscript);
    }
private:
    Var* m_var;
    Exp* m_exp;
};

class Exp:public Node{
public:
    enum{
        kExp_Var,
        kExp_Nil,
        kExp_Int,
        kExp_String,
        kExp_Call,
        kExp_Op,
        kExp_Record,
        kExp_Seq,
        kExp_Assign,
        kExp_If,
        kExp_While,
        kExp_Break,
        kExp_For,
        kExp_Let,
        kExp_Array,
        kExp_Invalid
    };
    Exp():Node(kNode_Exp){m_kind = kExp_Invalid;}
    Exp(s32 kind):Node(kNode_Exp){m_kind = kind;}
    virtual s32 Kind(){return m_kind;}
    static char* KindString(s32 kind){
        return ExpKindStrings[kind];
    }
    virtual Exp* Clone(){
        Exp* n = new Exp;
        n->m_kind = m_kind;
        return n;
    }
    static bool classof(Exp* e)
    {
        return ((e->Kind()>=kExp_Var) && (e->Kind()<=kExp_Array));
    }
    virtual ~Exp(){}
private:
    s32 m_kind;
    static char* ExpKindStrings[];
};

struct ExpNode{
    ExpNode(){
        m_exp = 0;
        prev = next = 0;
    }
    ~ExpNode(){
        delete m_exp;
    }
    
    /* members */
    Exp* m_exp;
    ExpNode* prev;
    ExpNode* next;
};

class ExpList{
public:
    ExpList(){
        m_head = 0;
    }
    ExpList(ExpNode* exp_node){
        m_head = exp_node;
    }
    ExpNode* GetHead(){return m_head;}
    ExpList* Clone(){
        ExpList* n = new ExpList;
        ExpNode* p = m_head;
        ExpNode* q = 0;
        ExpNode* newhead=0;
        while(p){
            ExpNode* t = new ExpNode;
            t->m_exp = p->m_exp?p->m_exp->Clone():0;
            if(newhead==0)
                newhead = t;
            if(q==0)
                q = t;
            else
            {
                q->next = t;
                t->prev = q;
                q = t;
            }
            p = p->next;
        }
        n->m_head = newhead;
        return n;
    }
    ~ExpList(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~ExpList");
        ExpNode* p = m_head;
        while(p){
            //logger.D("~ExpList #");
            m_head = m_head->next;
            delete p;
            p = m_head;
        }
    }
private:
    ExpNode* m_head;
};

class VarExp:public Exp{
public:
    VarExp():Exp(kExp_Var){
        m_var = 0;
    }
    VarExp(Var* var):Exp(kExp_Var){
        m_var = var;
    }
    Var* GetVar(){return m_var;}
    virtual ~VarExp(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~VarExp");
        delete m_var;
    }
    VarExp* Clone(){
        VarExp* n = new VarExp;
        n->m_var = m_var?m_var->Clone():0;
        return n;
    }
    static bool classof(Exp* e)
    {
        return (e->Kind()==kExp_Var);
    }
private:
    Var* m_var;
};

class NilExp:public Exp{
public:
    NilExp():Exp(kExp_Nil){
    }
    NilExp* Clone(){
        NilExp* n = new NilExp;
        return n;
    }
    static bool classof(Exp* e)
    {
        return (e->Kind()==kExp_Nil);
    }
};

class IntExp:public Exp{
public:
    IntExp():Exp(kExp_Int){
        m_ival = 0;
    }
    IntExp(s32 v):Exp(kExp_Int){
        m_ival = v;
    }
    IntExp* Clone(){
        IntExp* n = new IntExp;
        n->m_ival = m_ival;
        return n;
    }
    s32 GetInt(){return m_ival;}
    static bool classof(Exp* e)
    {
        return (e->Kind()==kExp_Int);
    }
private:
    s32 m_ival;
};

class StringExp:public Exp{
public:
    StringExp():Exp(kExp_String){
        m_sval = 0;
    }
    StringExp(char* s):Exp(kExp_String){
        m_sval = strdup(s);
    }
    StringExp* Clone(){
        StringExp* n = new StringExp;
        n->m_sval = strdup(m_sval);
        return n;
    }
    char* GetString(){return m_sval;}
    ~StringExp(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~StringExp");
        free(m_sval);
    }
    static bool classof(Exp* e)
    {
        return (e->Kind()==kExp_String);
    }
private:
    char* m_sval;
};

class CallExp:public Exp{
public:
    CallExp():Exp(kExp_Call){
        m_sym = 0;
        m_explist = 0;
    }
    CallExp(Symbol* sym,ExpList* explist):Exp(kExp_Call){
        m_sym = sym;
        m_explist = explist;
    }
    CallExp* Clone(){
        CallExp* n = new CallExp;
        n->m_sym = m_sym?m_sym->Clone():0;
        n->m_explist = m_explist?m_explist->Clone():0;
        return n;
    }
    Symbol* Name(){return m_sym;}
    ExpList* GetList(){return m_explist;}
    ~CallExp(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~CallExp");
        delete m_sym;
        delete m_explist;
    }
    static bool classof(Exp* e)
    {
        return (e->Kind()==kExp_Call);
    }
private:
    Symbol* m_sym;/* func */
    ExpList* m_explist;
    
};

class Oper{
public:
    enum{
        /* calc */
        kOper_Add,
        kOper_Sub,
        kOper_Mul,
        kOper_Div,
        
        /* compare */
        kOper_Lt,
        kOper_Gt,
        kOper_Le,
        kOper_Ge,
        
        kOper_Eq,
        kOper_Neq,
        
        kOper_And,
        kOper_Or,
        
        
        kOper_Invalid
    };
    Oper(){
        m_kind = kOper_Invalid;
    }
    Oper* Clone(){
        Oper* n = new Oper;
        n->m_kind = m_kind;
        return n;
    }
    s32 Kind(){return m_kind;}
    Oper(s32 kind){m_kind = kind;}
private:
    s32 m_kind;
};

class OpExp:public Exp{
public:
    OpExp():Exp(kExp_Op){
        m_oper = 0;
        m_left = 0;
        m_right = 0;
    }
    OpExp* Clone(){
        OpExp* n = new OpExp;
        n->m_oper = m_oper?m_oper->Clone():0;
        n->m_left = m_left?m_left->Clone():0;
        n->m_right = m_right?m_right->Clone():0;
        return n;
    }
    OpExp(Oper* oper,Exp* left,Exp* right):Exp(kExp_Op){
        m_oper = oper;
        m_left = left;
        m_right = right;
    }
    Oper* GetOper(){return m_oper;}
    Exp* GetLeft(){return m_left;}
    Exp* GetRight(){return m_right;}
    ~OpExp(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~OpExp");
        delete m_oper;
        delete m_left;
        delete m_right;
    }
    static bool classof(Exp* e)
    {
        return (e->Kind()==kExp_Op);
    }
private:
    Oper* m_oper;
    Exp* m_left;
    Exp* m_right;
};

class EFieldList;
class RecordExp:public Exp{
public:
    RecordExp():Exp(kExp_Record){
        m_type = 0;
        m_fields = 0;
    }
    RecordExp(Symbol* type,EFieldList* fields):Exp(kExp_Record){
        m_type = type;
        m_fields = fields;
    }
    Symbol* Name(){return m_type;}
    EFieldList* GetList(){return m_fields;}
    RecordExp* Clone();
    ~RecordExp();
private:
    Symbol* m_type;
    EFieldList* m_fields;
};   
 
class SeqExp:public Exp{
public:
    SeqExp():Exp(kExp_Seq){
        m_list = 0;
    }
    SeqExp(ExpList* explist):Exp(kExp_Seq){
        m_list = explist;
    }
    ExpList* GetList(){return m_list;}
    SeqExp* Clone(){
        SeqExp* n = new SeqExp;
        n->m_list = m_list?m_list->Clone():0;
        return n;
    }
    virtual ~SeqExp(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~SeqExp");
        delete m_list;
    }
    static bool classof(Exp* e)
    {
        return (e->Kind()==kExp_Seq);
    }
private:
    ExpList* m_list;
};

class AssignExp:public Exp{
public:
    AssignExp():Exp(kExp_Assign){
        m_var = 0;
        m_exp = 0;
    }
    AssignExp(Var* var,Exp* exp):Exp(kExp_Assign){
        m_var = var;
        m_exp = exp;
    }
    Var* GetVar(){return m_var;}
    Exp* GetExp(){return m_exp;}
    virtual AssignExp* Clone(){
        AssignExp* n = new AssignExp;
        n->m_var = m_var?m_var->Clone():0;
        n->m_exp = m_exp?m_exp->Clone():0;
        return n;
    }
    ~AssignExp(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~AssignExp");
        delete m_var;
        delete m_exp;
    }
    static bool classof(Exp* e)
    {
        return (e->Kind()==kExp_Assign);
    }
private:
    Var* m_var;
    Exp* m_exp;
};

class IfExp:public Exp{
public:
    IfExp():Exp(kExp_If){
        m_test = 0;
        m_then = 0;
        m_elsee = 0;
    }
    IfExp(Exp* test,Exp* then,Exp* elsee):Exp(kExp_If){
        m_test = test;
        m_then = then;
        m_elsee = elsee;
    }
    Exp* GetTest(){return m_test;}
    Exp* GetThen(){return m_then;}
    Exp* GetElsee(){return m_elsee;}
    IfExp* Clone(){
        IfExp* n = new IfExp;
        n->m_test = m_test?m_test->Clone():0;
        n->m_then = m_then?m_then->Clone():0;
        n->m_elsee = m_elsee?m_elsee->Clone():0;
        return n;
    }
    ~IfExp(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~IfExp");
        delete m_test;
        delete m_then;
        delete m_elsee;
    }
    static bool classof(Exp* e)
    {
        return (e->Kind()==kExp_If);
    }
private:
    Exp* m_test;
    Exp* m_then;
    Exp* m_elsee;
};

class WhileExp:public Exp{
public:
    WhileExp():Exp(kExp_While){
        m_test = 0;
        m_body = 0;
    }
    WhileExp(Exp* test,Exp* body):Exp(kExp_While){
        m_test = test;
        m_body = body;
    }
    Exp* GetTest(){return m_test;}
    Exp* GetExp(){return m_body;}
    WhileExp* Clone(){
        WhileExp* n = new WhileExp;
        n->m_test = m_test?m_test->Clone():0;
        n->m_body = m_body?m_body->Clone():0;
        return n;
    }
    ~WhileExp(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~WhileExp");
        delete m_test;
        delete m_body;
    }
    static bool classof(Exp* e)
    {
        return (e->Kind()==kExp_While);
    }
private:
    Exp* m_test;
    Exp* m_body;
};

class BreakExp:public Exp{
public:
    BreakExp():Exp(kExp_Break){}
    BreakExp* Clone(){
        BreakExp* n = new BreakExp;
        return n;
    }
    static bool classof(Exp* e)
    {
        return (e->Kind()==kExp_Break);
    }
};

class ForExp:public Exp{
public:
    ForExp():Exp(kExp_For){
        m_var = 0;
        m_lo = 0;
        m_hi = 0;
        m_body = 0;
    }
    ForExp(Symbol* var,Exp* lo,Exp* hi,Exp* body):Exp(kExp_For){
        m_var = var;
        m_lo = lo;
        m_hi = hi;
        m_body = body;
    }
    Symbol* GetVar(){return m_var;}
    Exp* GetLo(){return m_lo;}
    Exp* GetHi(){return m_hi;}
    Exp* GetExp(){return m_body;}
    ForExp* Clone(){
        ForExp* n = new ForExp;
        n->m_var = m_var?m_var->Clone():0;
        n->m_lo = m_lo?m_lo->Clone():0;
        n->m_hi = m_hi?m_hi->Clone():0;
        n->m_body = m_body?m_body->Clone():0;
        return n;
    }
    ~ForExp(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~ForExp");
        delete m_var;
        delete m_lo;
        delete m_hi;
        delete m_body;
    }
    static bool classof(Exp* e)
    {
        return (e->Kind()==kExp_For);
    }
private:
    Symbol* m_var;
    Exp* m_lo;
    Exp* m_hi;
    Exp* m_body;
};

class DecList;
class LetExp:public Exp{
public:
    LetExp():Exp(kExp_Let){
        m_decs = 0;
        m_body = 0;
    }
    LetExp(DecList* decs,Exp* body):Exp(kExp_Let){
        m_decs = decs;
        m_body = body;
    }
    LetExp* Clone();
    DecList* GetDecList(){return m_decs;}
    Exp*     GetBody(){return m_body;}
    ~LetExp();
    static bool classof(Exp* e)
    {
        return (e->Kind()==kExp_Let);
    }
private:
    DecList* m_decs;
    Exp* m_body;
};

class ArrayExp:public Exp{
public:
    ArrayExp():Exp(kExp_Array){
        m_type = 0;
        m_size = 0;
        m_init = 0;
    }
    ArrayExp(Symbol* type,Exp* size,Exp* init):Exp(kExp_Array){
        m_type = type;
        m_size = size;
        m_init = init;
    }
    Symbol* Name(){return m_type;}
    Exp* GetSize(){return m_size;}
    Exp* GetInit(){return m_init;}
    ArrayExp* Clone(){
        ArrayExp* n = new ArrayExp;
        n->m_type = m_type?m_type->Clone():0;
        n->m_size = m_size?m_size->Clone():0;
        n->m_init = m_init?m_init->Clone():0;
        return n;
    }
    ~ArrayExp(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~ArrayExp");
        delete m_type;
        delete m_size;
        delete m_init;
    }
    static bool classof(Exp* e)
    {
        return (e->Kind()==kExp_Array);
    }
private:
    Symbol* m_type;
    Exp* m_size;
    Exp* m_init;
};

class Dec:public Node{
public:
    enum{
        kDec_Function,
        kDec_Var,
        kDec_Type,
        kDec_Invalid
    };
    Dec():Node(kNode_Dec){m_kind = kDec_Invalid;}
    Dec(s32 kind):Node(kNode_Dec){m_kind = kind;}
    virtual s32 Kind(){return m_kind;}
    virtual Dec* Clone(){
        Dec* n = new Dec;
        n->m_kind = m_kind;
        return n;
    }
    virtual ~Dec(){}
    static bool classof(Dec* d)
    {
        return ((d->Kind()>=kDec_Function)&&(d->Kind()<=kDec_Type));
    }
private:
    s32 m_kind;
};

struct DecNode{
    DecNode(){
        m_dec = 0;
        prev = 0;
        next = 0;
    }
    ~DecNode(){
        delete m_dec;
    }
    
    /*members*/
    Dec* m_dec;
    
    DecNode* prev;
    DecNode* next;
    
};

class DecList{
public:
    DecList(){m_head=0;}
    DecList(DecNode* head){m_head = head;}
    DecNode* GetHead(){return m_head;}
    DecList* Clone(){
        DecList* n = new DecList;
        DecNode* newhead=0;
        DecNode* q=0;
        DecNode* p;
        DecNode* t;
        p = m_head;
        while(p)
        {
            t = new DecNode;
            t->m_dec=p->m_dec?p->m_dec->Clone():0;
            if(newhead==0)
                newhead=t;
            if(q==0)
                q=t;
            else{
                q->next = t;
                t->prev = q;
                q = t;
            }
            p = p->next;
        }
        n->m_head = newhead;
        return n;
    }
    ~DecList(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~DecList");
        DecNode* p;
        p = m_head;
        while(p)
        {
            //logger.D("~DecList #");
            m_head = m_head->next;
            delete p;
            p = m_head;
        }
    }
private:
    DecNode* m_head;
};

class FieldList;

class FunDec{
public:
    FunDec(){
        m_name = 0;
        m_params = 0;
        m_result = 0;
        m_body = 0;
    }
    FunDec(Symbol* name,FieldList* params,Symbol* result,Exp* body){
        m_name = name;
        m_params = params;
        m_result = result;
        m_body = body;
    }
    Symbol* Name(){return m_name;}
    FieldList* GetList(){return m_params;}
    Symbol* Type(){return m_result;}
    Exp* GetExp(){return m_body;}
    FunDec* Clone();
    ~FunDec();
private:
    Symbol* m_name;
    FieldList* m_params;
    Symbol* m_result;
    Exp* m_body;
};

struct FunDecNode{
    FunDecNode(){
        m_fundec = 0;
        prev = 0;
        next = 0;
    }
    ~FunDecNode(){
        delete m_fundec;
    }
    
    /*members*/
    FunDec* m_fundec;
    FunDecNode* prev;
    FunDecNode* next;
};

class FunDecList{
public:
    FunDecList(){m_head=0;}
    FunDecList(FunDecNode* head){m_head=head;}
    FunDecNode* GetHead(){return m_head;}
    FunDecList* Clone(){
        FunDecList* n = new FunDecList;
        FunDecNode* newhead=0;
        FunDecNode* q=0;
        FunDecNode* p;
        FunDecNode* t;
        p = m_head;
        while(p)
        {
            t = new FunDecNode;
            t->m_fundec=p->m_fundec?p->m_fundec->Clone():0;
            if(newhead==0)
                newhead=t;
            if(q==0)
                q=t;
            else{
                q->next = t;
                t->prev = q;
                q = t;
            }
            p = p->next;
        }
        n->m_head = newhead;
        return n;
    }
    ~FunDecList(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~FunDecList");
        FunDecNode* p;
        p = m_head;
        while(p){
            //logger.D("~FunDecList #");
            m_head = m_head->next;
            delete p;
            p = m_head;
        }
    }
private:
    FunDecNode* m_head;
};

class FunctionDec:public Dec{
public:
    FunctionDec():Dec(kDec_Function){
        m_fundeclist = 0;
    }
    FunctionDec(FunDecList* funs):Dec(kDec_Function){
        m_fundeclist = funs;
    }
    FunDecList* GetList(){return m_fundeclist;}
    FunctionDec* Clone(){
        FunctionDec* n = new FunctionDec;
        n->m_fundeclist = m_fundeclist?m_fundeclist->Clone():0;
        return n;
    }
    ~FunctionDec(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~FunctionDec");
        delete m_fundeclist;
    }
    static bool classof(Dec* d)
    {
        return (d->Kind()==kDec_Function);
    }
private:
    FunDecList* m_fundeclist;
};

class VarDec:public Dec{
public:
    VarDec():Dec(kDec_Var){
        m_var = 0;
        m_type = 0;
        m_init = 0;
    }
    VarDec(Symbol* var,Symbol* type,Exp* init):Dec(kDec_Var){
        m_var = var;
        m_type = type;
        m_init = init;
    }
    Symbol* GetSymbol(){return m_var;}
    Symbol* GetType(){return m_type;}
    Exp*    GetExp(){return m_init;}
    VarDec* Clone(){
        VarDec* n = new VarDec;
        n->m_var = m_var?m_var->Clone():0;
        n->m_type = m_type?m_type->Clone():0;
        n->m_init = m_init?m_init->Clone():0;
        return n;
    }
    ~VarDec(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~VarDec");
        delete m_var;
        delete m_type;
        delete m_init;
    }
    static bool classof(Dec* d)
    {
        return (d->Kind()==kDec_Var);
    }
private:
    Symbol* m_var;
    Symbol* m_type;
    Exp*    m_init;
};

class NameTyPairList;

class TypeDec:public Dec{
public:
    TypeDec():Dec(kDec_Type){m_nametylist = 0;}
    TypeDec(NameTyPairList* nametylist):Dec(kDec_Type){m_nametylist = nametylist;}
    NameTyPairList* GetList(){return m_nametylist;}
    TypeDec* Clone();
    ~TypeDec();
    static bool classof(Dec* d)
    {
        return (d->Kind()==kDec_Type);
    }
private:
    NameTyPairList* m_nametylist;
};


class Ty{
public:
    enum{
        kTy_Name,
        kTy_Record,
        kTy_Array,
        kTy_Invalid
    };
    Ty(){m_kind = kTy_Invalid;}
    Ty(s32 kind){m_kind = kind;}
    virtual s32 Kind(){return m_kind;}
    virtual Ty* Clone(){
        Ty* n = new Ty;
        n->m_kind = m_kind;
        return n;
    }
    virtual ~Ty(){}
    static bool classof(Ty* t)
    {
        return (t->Kind()>=kTy_Name && t->Kind()<=kTy_Array);
    }
private:
    s32 m_kind;
};

class NameTy:public Ty{
public:
    NameTy():Ty(kTy_Name){
        m_sym = 0;
    }
    NameTy(Symbol* sym):Ty(kTy_Name){
        m_sym = sym;
    }
    NameTy* Clone(){
        NameTy* n = new NameTy;
        n->m_sym = m_sym?m_sym->Clone():0;
        return n;
    }
    Symbol* Name(){return m_sym;}
    ~NameTy(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~NameTy");
        delete m_sym;
    }
    static bool classof(Ty* t)
    {
        return (t->Kind()==kTy_Name);
    }
private:
        Symbol* m_sym;
};

class FieldList;
class RecordTy:public Ty{
public:
    RecordTy():Ty(kTy_Record){
        m_list = 0;
    }
    RecordTy(FieldList* list):Ty(kTy_Record){
        m_list = list;
    }
    RecordTy* Clone();
    FieldList* GetList(){return m_list;}
    ~RecordTy();
    static bool classof(Ty* t)
    {
        return (t->Kind()==kTy_Record);
    }
private:
    FieldList* m_list;
};

class ArrayTy:public Ty{
public:
    ArrayTy():Ty(kTy_Array){
        m_name = 0;
    }
    ArrayTy(Symbol* name):Ty(kTy_Array){
        m_name = name;
    }
    Symbol* Name(){return m_name;}
    ArrayTy* Clone(){
        ArrayTy* n = new ArrayTy;
        n->m_name = m_name?m_name->Clone():0;
        return n;
    }
    ~ArrayTy(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~ArrayTy");
        delete m_name;
    }
    static bool classof(Ty* t)
    {
        return (t->Kind()==kTy_Array);
    }
private:
    Symbol* m_name;
};

class NameTyPair{
public:
    NameTyPair(){m_name=0;m_ty=0;}
    Symbol* Name(){return m_name;}
    Ty*     Type(){return m_ty;}
    NameTyPair(Symbol* name,Ty* a_ty){m_name = name; m_ty = a_ty;}
    NameTyPair* Clone(){
        NameTyPair* n = new NameTyPair;
        n->m_name = m_name?m_name->Clone():0;
        n->m_ty = m_ty?m_ty->Clone():0;
        return n;
    }
    ~NameTyPair(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~NameTyPair");
        delete m_name;
        delete m_ty;
    }
private:
    Symbol* m_name;
    Ty* m_ty;
};

struct NameTyPairNode{
    NameTyPairNode(){
        m_nametypair = 0;
        prev = 0;
        next = 0;
    }
    ~NameTyPairNode(){
        delete m_nametypair;
    }
    
    /*members*/
    NameTyPair* m_nametypair;
    NameTyPairNode* prev;
    NameTyPairNode* next;
};

class NameTyPairList{
public:
    NameTyPairList(){m_head=0;}
    NameTyPairNode* GetHead(){return m_head;}
    NameTyPairList(NameTyPairNode* head){m_head=head;}
    NameTyPairList* Clone(){
        NameTyPairList* n = new NameTyPairList;
        NameTyPairNode* newhead=0;
        NameTyPairNode* q=0;
        NameTyPairNode* p;
        NameTyPairNode* t;
        p = m_head;
        while(p){
            t = new NameTyPairNode;
            t->m_nametypair = p->m_nametypair?p->m_nametypair->Clone():0;
            if(newhead==0)
                newhead=t;
            if(q==0)
                q=t;
            else{
                q->next = t;
                t->prev = q;
                q = t;
            }
            p = p->next;
        }
        n->m_head = newhead;
        return n;
    }
    ~NameTyPairList(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~NameTyPairList");
        NameTyPairNode* p;
        p = m_head;
        while(p){
            //logger.D("~NameTyPairList #");
            m_head = m_head->next;
            delete p;
            p = m_head;
        }
    }
private:
    NameTyPairNode* m_head;
};

class Field{
public:
    Field(){m_name = 0;m_type = 0;}
    Field(Symbol* name,Symbol* type){
        m_name = name;
        m_type = type;
    }
    Symbol* Name(){return m_name;}
    Symbol* Type(){return m_type;}
    Field* Clone(){
        Field* n = new Field;
        n->m_name = m_name?m_name->Clone():0;
        n->m_type = m_type?m_type->Clone():0;
        return n;
    }
    ~Field(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~Field");
        delete m_name;
        delete m_type;
    }
private:
    Symbol* m_name;
    Symbol* m_type;
};

struct FieldNode{
    FieldNode(){
        m_field = 0;
        next = prev = 0;
    }
    ~FieldNode(){
        delete m_field;
    }
    
    /*members*/
    Field* m_field;
    
    FieldNode* prev;
    FieldNode* next;
};

class FieldList{
public:
    FieldList(){
        m_head = 0;
    }
    FieldList(FieldNode* head){
        m_head = head;
    }
    FieldNode* GetHead(){return m_head;}
    FieldList* Clone(){
        FieldList* n = new FieldList;
        FieldNode* newhead=0;
        FieldNode* q=0;
        FieldNode* p;
        FieldNode* t;
        p = m_head;
        while(p){
            t = new FieldNode;
            t->m_field = p->m_field?p->m_field->Clone():0;
            if(newhead==0)
                newhead=t;
            if(q==0)
                q=t;
            else{
                q->next = t;
                t->prev = q;
                q = t;
            }
            p = p->next;
        }
        n->m_head = newhead;
        return n;
    }
    ~FieldList(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~FieldList");
        FieldNode* p;
        p = m_head;
        while(p){
            //logger.D("~FieldList #");
            m_head = m_head->next;
            delete p;
            p = m_head;
        }
    }
private:
    FieldNode* m_head;
};

class EField{
public:
    EField(){m_name=0;m_exp=0;}
    EField(Symbol* name,Exp* exp){
        m_name = name;
        m_exp = exp;
    }
    Symbol* Name(){return m_name;}
    Exp* GetExp(){return m_exp;}
    EField* Clone(){
        EField* n = new EField;
        n->m_name = m_name?m_name->Clone():0;
        n->m_exp = m_exp?m_exp->Clone():0;
        return n;
    }
    ~EField(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~EField");
        delete m_name;
        delete m_exp;
    }
private:
    Symbol* m_name;
    Exp* m_exp;
};

struct EFieldNode{
    EFieldNode(){
        m_efield = 0;
        next = prev = 0;
    }
    ~EFieldNode(){
        delete m_efield;
    }
    
    /* members*/
    EField* m_efield;
    
    EFieldNode* prev;
    EFieldNode* next;
    
};

class EFieldList{
public:
    EFieldList(){m_head=0;}
    EFieldList(EFieldNode* head){
        m_head = head;
    }
    EFieldNode* GetHead(){return m_head;}
    EFieldList* Clone(){
        EFieldList* n = new EFieldList;
        EFieldNode* newhead=0;
        EFieldNode* p;
        EFieldNode* t;
        EFieldNode* q=0;
        p = m_head;
        while(p){
            t = new EFieldNode;
            t->m_efield = p->m_efield?p->m_efield->Clone():0;
            if(newhead==0)
                newhead=t;
            if(q==0)
                q = t;
            else{
                q->next = t;
                t->prev = q;
                q = t;
            }
            p = p->next;
        }
        n->m_head = newhead;
        return n;
        
    }
    ~EFieldList(){
        LoggerStdio logger;
        logger.SetLevel(LoggerBase::kLogger_Level_Error);
        logger.SetModule("absyn");
        //logger.D("~EFieldList");
        EFieldNode* p;
        p = m_head;
        while(p){
            //logger.D("~EFieldList #");
            m_head = m_head->next;
            delete p;
            p = m_head;
        }
    }
private:
    EFieldNode* m_head;
};


}// namespace tiger 


#endif
