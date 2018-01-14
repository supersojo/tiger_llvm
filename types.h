/* Coding: ANSI */
#ifndef TIGER_INTERNAL_TYPES_H
#define TIGER_INTERNAL_TYPES_H
#include <iostream>
#include "tiger_type.h"
#include "tiger_log.h"
#include "tiger_assert.h"
#include "absyn.h" //Symbol

namespace tiger{

struct SymNameHashTableNode{
    SymNameHashTableNode(){
        m_name = 0;
        m_symbol = 0;
        prev = 0;
        next = 0;
    }
    ~SymNameHashTableNode(){
        if(m_name)
            free(m_name);
        if(m_symbol)
            delete m_symbol;
    }
    char* m_name;
    Symbol* m_symbol;
    SymNameHashTableNode* prev;
    SymNameHashTableNode* next;
};
class SymNameHashTable{
public:
    enum{
        kSymNameHashTable_Size=32,
        kSymNameHashTable_Invalid
    };
    SymNameHashTable();
    Symbol* MakeSymbol(Symbol*);
    ~SymNameHashTable();
private:
    s32 hash(char* s);
    void Clean();
    SymNameHashTableNode** m_tab;
};

class TypeBase{
public:
    enum{
        kType_Int,
        kType_String,
        kType_Nil,
        kType_Void,
        kType_Array,
        kType_Record,
        kType_Name,
        kType_Invalid
    };
    TypeBase(){m_kind = kType_Invalid;}
    TypeBase(s32 kind){m_kind = kind;}
    virtual s32 Kind(){return m_kind;}
    bool Equal(TypeBase* o){
        return (m_kind==o->Kind());
    }
private:
    s32 m_kind;
};

class TypeInt:public TypeBase{
public:
    TypeInt():TypeBase(kType_Int){}
};
class TypeString:public TypeBase{
public:
    TypeString():TypeBase(kType_String){}
};

class TypeNil:public TypeBase{
public:
    TypeNil():TypeBase(kType_Nil){}
};

class TypeVoid:public TypeBase{
public:
    TypeVoid():TypeBase(kType_Void){}
};

class TypeArray:public TypeBase{
public:
    TypeArray():TypeBase(kType_Array){m_array=0;}
    TypeArray(TypeBase* array):TypeBase(kType_Array){m_array = array;}
    ~TypeArray(){
        //delete m_array;
    }
private:
    TypeBase* m_array;
};

class TypeField{
public:
    TypeField(){m_name=0;m_type=0;}
    TypeField(Symbol* name,TypeBase* ty){
        m_name = name;
        m_type = ty;
    }
    ~TypeField(){
        //delete m_name;
        //delete m_type;
    }
private:
    Symbol* m_name;
    TypeBase* m_type;
};

struct TypeFieldNode{

    TypeFieldNode(){
        m_field = 0;
        prev = 0;
        next = 0;
    }
    ~TypeFieldNode(){
        delete m_field;
    }
    /* members */
    TypeField* m_field;
    TypeFieldNode* prev;
    TypeFieldNode* next;
};
class TypeFieldList{
public:
    TypeFieldList(){m_head = 0;}
    TypeFieldList(TypeFieldNode* head){m_head = head;}
    ~TypeFieldList(){
        TypeFieldNode*p;
        p = m_head;
        while(p){
            m_head = m_head->next;
            delete p;
            p = m_head;
        }
    }
private:
    TypeFieldNode* m_head;
};

class TypeRecord:public TypeBase{
public:
    TypeRecord():TypeBase(kType_Record){m_record=0;}
    TypeRecord(TypeFieldList* record):TypeBase(kType_Record){m_record = record;}
    ~TypeRecord(){delete m_record;}
private:
    TypeFieldList* m_record;
};

class TypeName:public TypeBase{
public:
    TypeName():TypeBase(kType_Name){m_name=0;m_type=0;}
    TypeName(Symbol* name,TypeBase* ty):TypeBase(kType_Name){
        m_name = name;
        m_type = ty;
    }
    Symbol* Name(){return m_name;}
    TypeBase* Type(){return m_type;}
    void Update(TypeBase* n){
        if(m_type){
            delete m_type;
        }
        m_type = n;
    }
    ~TypeName(){
        //delete m_name;
        //delete m_type;
    }
private:
    Symbol* m_name;
    TypeBase* m_type;
};
/* Env*/
class EnvEntryBase{
public:
    enum{
      kEnvEntry_Var,/* type environment always uses this kind */
      kEnvEntry_Fun,
      kEnvEntry_Invalid
    };
    EnvEntryBase(){m_kind=kEnvEntry_Invalid;}
    EnvEntryBase(s32 kind){m_kind = kind;}
    virtual s32 Kind(){return m_kind;}
    virtual ~EnvEntryBase(){}
private:
    s32 m_kind;
};

class EnvEntryVar:public EnvEntryBase{
public:
    enum{
        kEnvEntryVar_For_Type,/* used in type environment*/
        kEnvEntryVar_For_Value,/* value environment*/
        kEnvEntryVar_Invalid/* invalid */
    };
    EnvEntryVar():EnvEntryBase(kEnvEntry_Var){m_type=0;m_intent = kEnvEntryVar_Invalid;}
    EnvEntryVar(TypeBase* ty,s32 intent):EnvEntryBase(kEnvEntry_Var){m_type=ty;m_intent = intent;}
    s32 Intent(){return m_intent;}
    TypeBase* Type(){return m_type;}
    void      Update(TypeBase* n){
        TypeName*p = dynamic_cast<TypeName*>(m_type);
        p->Update(n);

    }
    ~EnvEntryVar(){
        if(m_intent==kEnvEntryVar_For_Type){
            delete m_type;
        }
    }
private:
    TypeBase* m_type;
    s32 m_intent;
};

class EnvEntryFun:public EnvEntryBase{
public:
    EnvEntryFun():EnvEntryBase(kEnvEntry_Fun){m_formals=0;m_result=0;}
    EnvEntryFun(TypeFieldList *formals,TypeBase* result):EnvEntryBase(kEnvEntry_Fun){m_formals=formals;m_result=result;}
    ~EnvEntryFun(){
        delete m_formals;
        delete m_result;
    }
private:
    TypeFieldList* m_formals;
    TypeBase* m_result;
    
};

class SymTabEntry{
public:    
    SymTabEntry(){
        m_name = 0;
        m_binding = 0;
    }
    SymTabEntry(Symbol* name,EnvEntryBase* binding){
        m_name = name;
        m_binding = binding;
    }
    Symbol* GetSymbol(){return m_name;}
    EnvEntryBase* GetEnvEntryBase(){return m_binding;}
    ~SymTabEntry(){
        //delete m_name;
        delete m_binding;
    }
private:
    Symbol* m_name;// var or fun name or type name
    EnvEntryBase* m_binding;
};

struct SymTabEntryNode{

    SymTabEntryNode(){
        m_entry = 0;
        prev = next = 0;
    }
    ~SymTabEntryNode(){
        delete m_entry;
    }
    /* members */
    SymTabEntry* m_entry;
    SymTabEntryNode* prev;
    SymTabEntryNode* next;
};
struct SimpleStackNode{
    SimpleStackNode(){
        m_name = 0;
        next = 0;
    }
    ~SimpleStackNode(){
    }
    Symbol* m_name;
    SimpleStackNode* next;
};
class SimpleStack{
public:
    SimpleStack(){m_top = 0;}
    void Push(Symbol* name){
        SimpleStackNode* n;
        n = new SimpleStackNode;
        n->m_name = name;
        n->next = m_top;
        m_top = n;
    }
    Symbol* Pop(){
        SimpleStackNode* p;
        p = m_top;
        if(m_top){
            m_top = m_top->next;
        }
        if(p)
            return p->m_name;
        else
            return 0;
    }
    ~SimpleStack(){
        SimpleStackNode*p;
        p = m_top;
        while(p){
            m_top = m_top->next;
            delete p;
            p = m_top;
        }
    }
private:
    SimpleStackNode* m_top;
};
class SymTab{
public:
    enum{
        kSymTab_Size=32,
        kSymTab_Invalid
    };
    SymTab();
    void Erase(Symbol* name);
    void BeginScope();
    void EndScope();
    void Enter(Symbol* key,EnvEntryBase* value);
    EnvEntryBase* Lookup(Symbol* key);
    void Update(Symbol*s,TypeBase* t);
    Symbol* MakeSymbol(Symbol* s);
    Symbol* MakeSymbolFromString(char* s);
    /* helper for types */
    TypeBase*  Type(Symbol* s);
    ~SymTab();
private:
    SymTabEntryNode** m_tab;
    SimpleStack* m_stack;
    s32 hash(Symbol* key);
    void Clean();
    Symbol* m_marker;
    SymNameHashTable* m_sym_name_mapping;
    LoggerStdio m_logger;
};

}//namespace tiger


#endif
