/* Coding: ANSI */
#ifndef TIGER_INTERNAL_TYPES_H
#define TIGER_INTERNAL_TYPES_H
#include <iostream>
#include "tiger_type.h"
#include "tiger_log.h"
#include "tiger_assert.h"
#include "symbol.h" //Symbol

#include <llvm/IR/Type.h>
#include "irgencontext.h"
namespace llvm{
class Type;
}

namespace tiger{


/* type used in tiger 
TypeBase is the ancestor of all types in tiger.
Be care about the type's deletion.
A type's member may refer to other type,we should only delete type itself,not the refered type member.
In any moment,tenv contains all the types in tiger.

[a type array ]->[other type]
we only delete the type array itself,no the other type.

*/
class TypeBase{
public:
    enum{
        kType_Int,
        kType_String,
        kType_Nil,//internal
        kType_Void,//internal
        kType_Array,
        kType_Record,
        kType_Name,
        kType_Invalid
    };
    TypeBase(){
        m_kind = kType_Invalid;
        m_llvm_type = nullptr;
    }
    TypeBase(s32 kind){
        m_kind = kind;
        m_llvm_type = nullptr;
    }
    virtual s32 Kind(){return m_kind;}
    bool Equal(TypeBase* o){
        return (m_kind==o->Kind());
    }
    virtual char* TypeString(){
        switch(m_kind){
            case kType_Int:
                return "int";
            case kType_String:
                return "string";
            case kType_Nil:
                return "nil";
            case kType_Void:
                return "void";    
            case kType_Array:
                return "[]"; 
            case kType_Record:
                return "{}";
            case kType_Name:
                return "name";
            default:
                return "invalid";
        }
    }
    virtual llvm::Type* GetLLVMType(){return m_llvm_type;}
    void SetLLVMType(llvm::Type* ty){m_llvm_type = ty;}
    virtual s32 Size(){return 0;}
    virtual ~TypeBase(){}
    static bool classof(TypeBase* t)
    {
        return (t->Kind()>=kType_Int && t->Kind()<=kType_Name);
    }
private:
    s32 m_kind;
    llvm::Type* m_llvm_type;
};

class TypeInt:public TypeBase{
public:
    TypeInt():TypeBase(kType_Int){
        SetLLVMType( (llvm::Type*)llvm::Type::getInt32Ty( *(IRGenContext::Get()->C())) );
    }
    virtual s32 Size(){return 4;/*ugly code*/}
    static bool classof(TypeBase* t)
    {
        return (t->Kind()==kType_Int);
    }
};
class TypeString:public TypeBase{
public:
    TypeString():TypeBase(kType_String){
        //SetLLVMType( llvm::PointerType::getUnqual(llvm::Type::getInt8Ty( *(IRGenContext::Get()->C()))) );
    }
    virtual s32 Size(){return 4;/*ugly code*/}
    static bool classof(TypeBase* t)
    {
        return (t->Kind()==kType_String);
    }
};

class TypeNil:public TypeBase{
public:
    TypeNil():TypeBase(kType_Nil){
        //SetLLVMType( (llvm::Type*)llvm::Type::getInt32Ty(*g_llvm_context) );
    }
    virtual s32 Size(){return 0;/*ugly code*/}
    static bool classof(TypeBase* t)
    {
        return (t->Kind()==kType_Nil);
    }
};

class TypeVoid:public TypeBase{
public:
    TypeVoid():TypeBase(kType_Void){
        //SetLLVMType( (llvm::Type*)llvm::Type::getInt32Ty(*g_llvm_context) );
    }
    virtual s32 Size(){return 0;/*ugly code*/}
    static bool classof(TypeBase* t)
    {
        return (t->Kind()==kType_Void);
    }
};

class TypeArray:public TypeBase{
public:
    TypeArray():TypeBase(kType_Array){
        m_array=0;
    }
    TypeArray(TypeBase* array):TypeBase(kType_Array){
        m_array = array;
    }
    TypeBase* Type(){return m_array;}
    virtual s32 Size(){
        /*
        type b={x:int,y:string}
        type a=array of b
        */
        return m_array->Size();/*ugly code*/
    }
    ~TypeArray(){
        //delete m_array;
    }
    static bool classof(TypeBase* t)
    {
        return (t->Kind()==kType_Array);
    }
private:
    TypeBase* m_array;/* memory managed by type member, not type array */
    
};

class TypeField{
public:
    TypeField(){m_name=0;m_type=0;}
    TypeField(Symbol* name,TypeBase* ty){
        m_name = name;
        m_type = ty;
    }
    Symbol* Name(){return m_name;}
    TypeBase* Type(){return m_type;}
    virtual s32 Size(){
        /*
        type x=array of int
        type a={a:int,b:string,c:x [10] of 0}
        
        */
        if(m_type->Kind()==TypeBase::kType_Name)// or else dead loop 
            return 4;// only refer
        return m_type->Size();/*ugly code*/
    }
    virtual ~TypeField(){
        //delete m_name;
        //delete m_type;
    }
private:
    Symbol* m_name;/* memory managed by string hash table */
    TypeBase* m_type;/* memroy managed by type member, not type field */
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
    TypeFieldNode* GetHead(){return m_head;}
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
    TypeRecord():TypeBase(kType_Record){
        m_record=0;
    }
    TypeRecord(TypeFieldList* record):TypeBase(kType_Record){
        m_record = record;
    }
    TypeFieldList* GetList(){return m_record;}
    virtual s32 Size(){
        s32 i=0;
        TypeFieldNode* p;
        p = m_record->GetHead();
        while(p){
            i += p->m_field->Size();// maybe loop defined
            p = p->next;
        }
        return i;
    }
    ~TypeRecord(){delete m_record;}
    static bool classof(TypeBase* t)
    {
        return (t->Kind()==kType_Record);
    }
private:
    TypeFieldList* m_record;
};

class TypeName:public TypeBase{
public:
    TypeName():TypeBase(kType_Name){m_name=0;m_type=0;}
    TypeName(Symbol* name,TypeBase* ty):TypeBase(kType_Name){
        m_name = name;
        m_type = ty;
        //SetLLVMType(ty->GetLLVMType());
    }
    Symbol* Name(){return m_name;}
    TypeBase* Type(){return m_type;}
    
    llvm::Type* GetLLVMType(){return m_type->GetLLVMType();}
    
    void Update(TypeBase* n){
        if(m_type){
            delete m_type;
        }
        m_type = n;
    }
    virtual char* TypeString(){
        switch(Kind()){
            case kType_Name:
                return m_name->Name();
            default:
                return "invalid";
        }
    }
    virtual s32 Size(){
        return m_type->Size();
    }
    ~TypeName(){
        //delete m_name;
        if(m_type &&
           ((m_type->Kind()==kType_Record)||(m_type->Kind()==kType_Array)))
        {
            delete m_type;
        }
    }
    static bool classof(TypeBase* t)
    {
        return (t->Kind()==kType_Name);
    }
private:
    Symbol* m_name;/* memory managed by string hash table */
    TypeBase* m_type;/* memory managed by type member, not type record */
};


}//namespace tiger


#endif
