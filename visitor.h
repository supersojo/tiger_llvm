#ifndef VISITOR_H
#define VISITOR_H
#include <utility>  
#include <iostream>  
#include <memory>  
#include <string>  
#include "absyn.h"
#include "symtab.h"
namespace tiger{

//base of return type    
//RetTy should be the base of VarRetTy,DecRetTy,ExpRetTy
template<typename RetTy=void,
         typename VarRetTy = void,
         typename DecRetTy = void,
         typename ExpRetTy = void>
class Visitor{
public:
#define Define_Visit(Kind) \
    virtual RetTy Visit##Kind(Kind* a){ \
    }
#define Define_Var_Visit(Kind) \
    virtual VarRetTy Visit##Kind(Kind* a){ \
    }
#define Define_Dec_Visit(Kind) \
    virtual DecRetTy Visit##Kind(Kind* a){ \
    }
#define Define_Exp_Visit(Kind) \
    virtual ExpRetTy Visit##Kind(Kind* a){ \
    }
    
#define Make_Visit(Kind) \
    if(n->Type()==Node::kNode_##Kind) \
        return Visit##Kind( dynamic_cast<Kind*>(n));
       
#define Make_Var_Visit(Kind0) \
    if(v->Kind()==Var::kVar_##Kind0) \
        return Visit##Kind0##Var( dynamic_cast<Kind0##Var*>(v));
        
#define Make_Dec_Visit(Kind0) \
    if(d->Kind()==Dec::kDec_##Kind0) \
        return Visit##Kind0##Dec( dynamic_cast<Kind0##Dec*>(d));

#define Make_Exp_Visit(Kind0) \
    if(e->Kind()==Exp::kExp_##Kind0) \
        return Visit##Kind0##Exp( dynamic_cast<Kind0##Exp*>(e));
        
    virtual RetTy Visit(Node* n){
        Make_Visit(Var)
        Make_Visit(Dec)
        Make_Visit(Exp)
    }
    
    virtual VarRetTy VisitVar(Var* v){
        Make_Var_Visit(Simple)
        Make_Var_Visit(Field)
        Make_Var_Visit(Subscript)
    }
    
    Define_Var_Visit(SimpleVar)
    Define_Var_Visit(FieldVar)
    Define_Var_Visit(SubscriptVar)
    
    
    virtual DecRetTy VisitDec(Dec* d){
        Make_Dec_Visit(Function)
        Make_Dec_Visit(Type)
        Make_Dec_Visit(Var)
    }
    Define_Dec_Visit(FunctionDec)
    Define_Dec_Visit(TypeDec)
    Define_Dec_Visit(VarDec)


    virtual ExpRetTy VisitExp(Exp* e){
        Make_Exp_Visit(Var)
        Make_Exp_Visit(Nil)
        Make_Exp_Visit(Int)
        Make_Exp_Visit(String)
        Make_Exp_Visit(Call)
        Make_Exp_Visit(Op)
        Make_Exp_Visit(Record)
        Make_Exp_Visit(Seq)
        Make_Exp_Visit(Assign)
        Make_Exp_Visit(If)
        Make_Exp_Visit(While)
        Make_Exp_Visit(Break)
        Make_Exp_Visit(For)
        Make_Exp_Visit(Let)
        Make_Exp_Visit(Array)
    }
    Define_Exp_Visit(VarExp)
    Define_Exp_Visit(NilExp)
    Define_Exp_Visit(IntExp)
    Define_Exp_Visit(StringExp)
    Define_Exp_Visit(CallExp)
    Define_Exp_Visit(OpExp)
    Define_Exp_Visit(RecordExp)
    Define_Exp_Visit(SeqExp)
    Define_Exp_Visit(AssignExp)
    Define_Exp_Visit(IfExp)
    Define_Exp_Visit(WhileExp)
    Define_Exp_Visit(BreakExp)
    Define_Exp_Visit(ForExp)
    Define_Exp_Visit(LetExp)
    Define_Exp_Visit(ArrayExp)

#undef Define_Visit
#undef Make_Visit
#undef Make_Var_Visit
#undef Make_Dec_Visit
#undef Make_Exp_Visit
    
};
template<typename RetTy=void,
         typename VarRetTy = void,
         typename DecRetTy = void,
         typename ExpRetTy = void>
class IRGenVisitor:public Visitor<RetTy,VarRetTy,DecRetTy,ExpRetTy>{
public:
    IRGenVisitor();
    
};


}//namespace tiger

#endif
