#include "tiger_llvm.h"

namespace tiger{

void IRGen::Init()
{
    m_context = IRGenContext::Get();
    
    
}
IRGen::~IRGen(){
    IRGenContext::Exit();
}
Level* IRGen::OutmostLevel()
{
    if(m_top_level==0){
        //create the out most function and the entry basic block
        m_top_level = new Level(0, new FrameBase(FrameBase::kFrame_X86));
        llvm::FunctionType* ft = llvm::FunctionType::get(llvm::Type::getVoidTy(*(m_context->C())),false/*var args flag*/);
        llvm::Function* f = llvm::Function::Create(ft,llvm::Function::ExternalLinkage,"tiger_main",m_context->M());
        llvm::BasicBlock* bb = llvm::BasicBlock::Create( *(m_context->C()), "entry", f);
        m_context->B()->SetInsertPoint(bb);
        m_top_level->SetFunc(f);
        m_top_level->SetCurBB(bb);
        
    }

    return m_top_level;
}
/*
 1 2 3 -> ConstantValue
 a b c -> Value
 a>b ->Value
 
 level - function - basic blocks 
 a=1
 if a>1 a=0
 a=3
 
*/
IRGenResult*  IRGen::IRGenVar(SymTab* venv,SymTab* tenv,Level* level,Var* var,llvm::BasicBlock* dest_bb)
{
    IRGenResult* result = new IRGenResult;
    switch(var->Kind()){
        case Var::kVar_Simple:
        {
            m_logger.W("simple var using");
            EnvEntryVarLLVM* t;
            /* find var in symbol table */
            t = dynamic_cast<EnvEntryVarLLVM*>(venv->Lookup(venv->MakeSymbol(dynamic_cast<SimpleVar*>(var)->GetSymbol())));
            TIGER_ASSERT(t!=0,"var %s not found",dynamic_cast<SimpleVar*>(var)->GetSymbol()->Name());
            result->m_type = t->Type();//tiger type
            result->m_llvm_value = t->GetLLVMValue();//llvm value -- PointerType's value returned by alloca
            result->m_llvm_type = t->Type()->GetLLVMType();//llvm type -- tiger type to llvm type
            return result;
            
        }
        case Var::kVar_Field:
        {
            m_logger.W("field var using");
            /*
            let
            type a = {x:int,y:int}
            var a0:=a{x:=1,y:=1}
            in
            a0.x:=10
            end
            */
            TypeFieldNode* head;
            IRGenResult* p = IRGenVar(venv,tenv,level,dynamic_cast<FieldVar*>(var)->GetVar(),dest_bb);
            head = dynamic_cast<TypeRecord*>(dynamic_cast<TypeName*>(p->Type())->Type())->GetList()->GetHead();
            s32 i=0;// field index in Record
            while(head){
                if(head->m_field->Name()==tenv->MakeSymbol(dynamic_cast<FieldVar*>(var)->GetSym())){
                    /* ok */
                    llvm::Value* inds[]={
                        IRGenContext::Get()->B()->getInt32(0),
                        IRGenContext::Get()->B()->getInt32(i),
                    };
                    
                    result->m_type = head->m_field->Type();// tiger type 
                    
                    // m_llvm_value must be PointerType
                    // Note: getelementptr must return pointer
                    result->m_llvm_value = IRGenContext::Get()->B()->CreateGEP(p->LLVMType(),p->LLVMValue(),inds);
                    result->m_llvm_type = head->m_field->Type()->GetLLVMType();
                    delete p;
                    return result;
                }
                i++;
                head = head->next;
            }
            
            TIGER_ASSERT(0,"%s not found in record type",dynamic_cast<FieldVar*>(var)->GetSym()->Name());

        }
        case Var::kVar_Subscript:
        {
            m_logger.W("subscript var");
            /*
            let
            type a = array of int
            var a0:=a[10] of [0]
            in
            a0[1]:=10
            end
            */
            IRGenResult* p;
            p = IRGenVar(venv,tenv,level,dynamic_cast<SubscriptVar*>(var)->GetVar(),dest_bb);
            if( (p->Type())->Kind()!=TypeBase::kType_Name){
                m_logger.W("name type needed");
            }
            TIGER_ASSERT(p!=0,"name type needed");
            
            llvm::Value* inds[]={
                IRGenContext::Get()->B()->getInt32(0),
                IRGenContext::Get()->B()->getInt32(1),
            };
            // access array element ptr base
            // after use GEP, always load followed
            llvm::Value* tmp = IRGenContext::Get()->B()->CreateGEP(p->LLVMType(),p->LLVMValue(),inds);
            llvm::Value* tmp1 = IRGenContext::Get()->B()->CreateLoad( tmp );
            
            // access element 
            IRGenResult* t;
            t = IRGenExp(venv,tenv,level,dynamic_cast<SubscriptVar*>(var)->GetExp(),dest_bb);
            result->m_type = dynamic_cast<TypeArray*>(dynamic_cast<TypeName*>(p->Type())->Type())->Type();
            if( llvm::isa<llvm::PointerType>(t->LLVMValue()->getType()) )
            {//pointer type need load first
                llvm::Value* vvv = IRGenContext::Get()->B()->CreateLoad( t->LLVMValue() );
                result->m_llvm_value = IRGenContext::Get()->B()->CreateGEP(result->m_type->GetLLVMType(),tmp1,vvv);
            }
            else
                result->m_llvm_value = IRGenContext::Get()->B()->CreateGEP(result->m_type->GetLLVMType(),tmp1,t->LLVMValue());
            result->m_llvm_type = result->m_type->GetLLVMType();
            return result;
        }
        default:
            break;
    }
    m_logger.W("shoud not reach here %s,%d",__FILE__,__LINE__);
    return 0;
}
/*
gen user defined tiger type
*/
TypeBase* IRGen::IRGenTy(SymTab* tenv,Level* level,Ty* ty)
{
    switch(ty->Kind())
    {
        /*
        type a={x:int,y:{a:int}} not suppport
        */
        case Ty::kTy_Name:
        {
            EnvEntryVarLLVM* t;
            t = dynamic_cast<EnvEntryVarLLVM*>(tenv->Lookup(tenv->MakeSymbol(dynamic_cast<NameTy*>(ty)->Name())));
            TIGER_ASSERT(t!=0,"type %s not found",dynamic_cast<NameTy*>(ty)->Name()->Name());
            return t->Type();
        }
        case Ty::kTy_Record:
        {
            /*
            type a = {a:int,b:string}
            (Field("a","int"),Field("b","string"))
            */
            FieldNode* head;
            TypeFieldNode* n=0,*ret=0,*cur=0;
            EnvEntryVarLLVM* p;
            TIGER_ASSERT(dynamic_cast<RecordTy*>(ty)->GetList(),"empty body");
            head = dynamic_cast<RecordTy*>(ty)->GetList()->GetHead();
            while(head){
                /*
                type a={x:a}
                */
                n = new TypeFieldNode;
                p = dynamic_cast<EnvEntryVarLLVM*>(tenv->Lookup(tenv->MakeSymbol(head->m_field->Type())));
                TIGER_ASSERT(p!=0,"type %s not found",head->m_field->Type()->Name());

                n->m_field = new TypeField(tenv->MakeSymbol(head->m_field->Name()),p->Type());
                if(ret==0)
                    ret = n;
                if(cur==0)
                { 
                    cur = n;
                }
                else
                {
                    cur->next = n;
                    n->prev = cur;
                    cur = n;
                }
                head = head->next;
            }
            m_logger.W("%s,%d",__FILE__,__LINE__);
            return new TypeRecord(new TypeFieldList(ret));
        }
        case Ty::kTy_Array:
        {
            /*
            type a=array of b
            ArrayTy("b")
            */
            EnvEntryVarLLVM* p;
            p = dynamic_cast<EnvEntryVarLLVM*>(tenv->Lookup(tenv->MakeSymbol(dynamic_cast<ArrayTy*>(ty)->Name())));
            return new TypeArray(p->Type());
        }
        default:
            break;
    }
    return 0;
}
/*
int Int32Ty
string i8*
atype a={a:int,b:string}
*/
void IRGen::IRGenTypeDec(SymTab* venv,SymTab* tenv,Level* level,Dec* dec)
{
    NameTyPairNode* head;
    head = dynamic_cast<TypeDec*>(dec)->GetList()->GetHead();
    /* process headers of decs */
    while(head){
        //m_logger.D("New type with %s",head->m_nametypair->Name()->Name());
        tenv->Enter( tenv->MakeSymbol(head->m_nametypair->Name()),
                     new EnvEntryVarLLVM( 
                                      new TypeName(tenv->MakeSymbol(head->m_nametypair->Name()),0/* TypeBase* */),
                                      EnvEntryVarLLVM::kEnvEntryVarLLVM_For_Type, 0/*llvm::Type*/,0/*llvm::Value* */
                                    ) 
                   );
        head = head->next;
    }
    /* process bodys of decs*/
    head = dynamic_cast<TypeDec*>(dec)->GetList()->GetHead();
    while(head){
        /*
        gen type infor from absyn
        type a = {x:int,y:a}
        */
        TypeBase* t = IRGenTy(tenv,level,head->m_nametypair->Type());
        if(t->Kind()!=TypeBase::kType_Name){
            /*
            type a={x:int,y:int}
            When type "a" insert tenv, it's type is dummy TypeName.Now we get real type so refill it here.
            */
            dynamic_cast<EnvEntryVarLLVM*>(tenv->Lookup(tenv->MakeSymbol(head->m_nametypair->Name())))->Update(t);
        }
        else{
            // check cycle dependency 
            EnvEntryVarLLVM* p = dynamic_cast<EnvEntryVarLLVM*>(tenv->Lookup(tenv->MakeSymbol(head->m_nametypair->Name())));
            p->Update(dynamic_cast<TypeName*>(t));
            if(dynamic_cast<TypeName*>(t)->Type()==dynamic_cast<TypeName*>(p->Type())){
                /*
                type b=a
                type a=b
                */
                TIGER_ASSERT(0,"cycle dependency occur");                        
            }

        }
        head = head->next;
    }
    /* tiger type to llvm type */
    head = dynamic_cast<TypeDec*>(dec)->GetList()->GetHead();
    while(head){
        /*
        type b=int
        type a={x:int,y:a}
        */
        EnvEntryVarLLVM* t = dynamic_cast<EnvEntryVarLLVM*>(tenv->Lookup(tenv->MakeSymbol(head->m_nametypair->Name())));
        TIGER_ASSERT(t->Type()->Kind()==TypeBase::kType_Name,"must be type name");
        TypeBase* tt = dynamic_cast<TypeName*>(t->Type())->Type();
        m_logger.W("%s,%d",__FILE__,__LINE__);
        if(tt->Kind()==TypeBase::kType_Record){
            m_logger.W("%s,%d",__FILE__,__LINE__);
            m_logger.D("type record");
            //1) create struct type proto
            llvm::StructType* t_t = llvm::StructType::create( *(m_context->C()) );
            tt->SetLLVMType(t_t);
            //2) create struct type body
            TypeFieldNode* n = dynamic_cast<TypeRecord*>(tt)->GetList()->GetHead();
            std::vector<llvm::Type*> tys;
            while(n){
                //n->m_field->Name() no care
                //n->m_field->Type() **
                TIGER_ASSERT(n->m_field->Type(),"type name null");
                if (llvm::isa<llvm::StructType>(n->m_field->Type()->GetLLVMType())){
                    m_logger.D("struct type need to convert to pointer");
                    tys.push_back( llvm::PointerType::getUnqual(n->m_field->Type()->GetLLVMType()) );
                }else{
                    tys.push_back( n->m_field->Type()->GetLLVMType() );
                }
                n = n->next;
            }
            t_t->setBody(llvm::makeArrayRef<llvm::Type*>(tys));
            t_t->dump();
            
        }else if(tt->Kind()==TypeBase::kType_Array){
            m_logger.W("%s,%d",__FILE__,__LINE__);
            m_logger.D("type array");
            //dynamic_cast<TypeArray*>(tt)->Type()//element type
            llvm::StructType* t_t = llvm::StructType::create( *(m_context->C()) );
            llvm::Type*tys[]={
                llvm::Type::getInt32Ty( *(m_context->C()) ),
                llvm::PointerType::getUnqual( dynamic_cast<TypeArray*>(tt)->Type()->GetLLVMType() )
            };
            t_t->setBody(tys);
            dynamic_cast<TypeArray*>(tt)->SetLLVMType(t_t);
            t_t->dump();
            
        }else{//primary types
            m_logger.W("%s,%d",__FILE__,__LINE__);
            t->Type()->SetLLVMType(tt->GetLLVMType());
            tt->GetLLVMType()->dump();
        }
        head = head->next;
    }
}
TypeFieldList* IRGen::MakeFormalsList(SymTab* venv,SymTab* tenv,Level* level,FieldList* params)
{
    FieldNode* head;
    
    TypeFieldNode* tyhead=0;
    TypeFieldNode* tynext=0;
    TypeFieldNode* tynew=0;
    
    /* function foo() */
    if(params==0){
        m_logger.D("function formals is empty");
        return new TypeFieldList(0);
    }
    
    head = params->GetHead();
    
    while(head)
    {
        tynew = new TypeFieldNode;
        tynew->m_field = (new TypeField(venv->MakeSymbol(head->m_field->Name()),dynamic_cast<EnvEntryVarLLVM*>(tenv->Lookup(tenv->MakeSymbol(head->m_field->Type())))->Type()));
        if(tyhead==0)
            tyhead = tynew;
        if(tynext==0)
            tynext = tynew;
        else{
            tynext->next = tynew;
            tynew->prev = tynext;
            tynext = tynew;

        }
        head = head->next;
    }
    return new TypeFieldList(tyhead);
    
}
FrameBase* IRGen::MakeNewFrame(FunDec* fundec)
{
    FrameBase* f;
    
    f = new FrameBase(FrameBase::kFrame_X86);

    return f;
}
void IRGen::IRGenFunctionDec(SymTab* venv,SymTab* tenv,Level* level,Dec* dec,llvm::BasicBlock* dest_bb)
{
    /*
    stack frame:
    - static link
    - formal args
    - local args
    */
    FunDecNode* fundec_head;
    FieldNode* head;
    
    TypeFieldNode* tyhead=0;
    TypeFieldNode* tynext=0;
    TypeFieldNode* tynew=0;
    
    IRGenResult *a;

    Level* alevel;
    
    m_logger.D("type check with kDec_Function");
    
    fundec_head = dynamic_cast<FunctionDec*>(dec)->GetList()->GetHead();
    /*
    function a()=0 ==> FunctionType * ft = FunctionType::get(params,ret)
    Function::get(ft)
    function b()=a()
    */
    /* process all function header decs */
    while(fundec_head){

        /* level and label */
        alevel = new Level(level,MakeNewFrame(fundec_head->m_fundec));
        //m_level_manager->NewLevel(alevel);
        if(fundec_head->m_fundec->Type()==0){
            m_logger.D("empty function return type ");
            
            std::vector<llvm::Type*> tys;
            if(fundec_head->m_fundec->GetList()!=0)
            {
                head = fundec_head->m_fundec->GetList()->GetHead();
                
                while(head){
                    TypeBase* t = dynamic_cast<EnvEntryVarLLVM*>(tenv->Lookup(tenv->MakeSymbol(head->m_field->Type())))->Type();
                    if(llvm::isa<llvm::StructType>(t->GetLLVMType()))
                        tys.push_back(llvm::PointerType::getUnqual(t->GetLLVMType()));
                    else
                        tys.push_back(t->GetLLVMType());
                    head = head->next;
                }
            }
            
            llvm::FunctionType* ft = llvm::FunctionType::get(llvm::Type::getVoidTy( *(m_context->C())),llvm::makeArrayRef<llvm::Type*>(tys),false/*var args flag*/);
            llvm::Function* f = llvm::Function::Create(ft,llvm::Function::ExternalLinkage,fundec_head->m_fundec->Name()->Name(),m_context->M());
            llvm::BasicBlock* bb = llvm::BasicBlock::Create( *(m_context->C()),"entry",f);
            alevel->SetCurBB(bb);
            
            EnvEntryFunLLVM* ef = new EnvEntryFunLLVM( 
                                          MakeFormalsList(venv,tenv,level,fundec_head->m_fundec->GetList()),
                                          0, 
                                          alevel, 
                                          TempLabel::NewNamedLabel(fundec_head->m_fundec->Name()->Name()),
                                          0/*kind*/
                                        );
            ef->SetFun(f);
            venv->Enter( venv->MakeSymbol(fundec_head->m_fundec->Name()),
                         ef
                       );
            
            
        }else{
            venv->Enter( venv->MakeSymbol(fundec_head->m_fundec->Name()),
                         new EnvEntryFunLLVM( 
                                          MakeFormalsList(venv,tenv,level,fundec_head->m_fundec->GetList()), 
                                          dynamic_cast<EnvEntryVar*>( 
                                                                      tenv->Lookup( tenv->MakeSymbol(fundec_head->m_fundec->Type()) )
                                                                    )->Type(), 
                                          alevel, 
                                          TempLabel::NewNamedLabel(fundec_head->m_fundec->Name()->Name()),
                                          0/*kind*/
                                        )
                       );
        }
        fundec_head = fundec_head->next;
    }
    
    /* process all function body decs */
    fundec_head = dynamic_cast<FunctionDec*>(dec)->GetList()->GetHead();
    while(fundec_head){
        
        /* each function needs its own level information */
        alevel = dynamic_cast<EnvEntryFunLLVM*>( venv->Lookup( venv->MakeSymbol(fundec_head->m_fundec->Name()) ))->GetLevel();
        TIGER_ASSERT(alevel!=0,"function level is empty!");
        
        /* function foo() */
        if(fundec_head->m_fundec->GetList()!=0)
            head = fundec_head->m_fundec->GetList()->GetHead();
        
        venv->BeginScope(ScopeMaker::kScope_Fun);
        if(fundec_head->m_fundec->GetList()!=0){
            s32 i=0;//last formal arg for static link
            llvm::Argument* arg = llvm::cast<llvm::Argument>(alevel->CurBB()->getParent()->arg_begin());
            while(head){
                TypeBase* t;
                t = dynamic_cast<EnvEntryVarLLVM*>(tenv->Lookup(tenv->MakeSymbol(head->m_field->Type())))->Type();
                m_context->B()->SetInsertPoint( alevel->CurBB() );
                llvm::Value* v;
                if(llvm::isa<llvm::StructType>(t->GetLLVMType())){
                    v = m_context->B()->CreateAlloca(llvm::PointerType::getUnqual(t->GetLLVMType()));
                }else
                    v = m_context->B()->CreateAlloca(t->GetLLVMType());
               
                //load param from arguments
                // access function args
                m_context->B()->CreateStore(arg,v);
                llvm::Value* vv;
                if(llvm::isa<llvm::StructType>(t->GetLLVMType())){
                    vv = m_context->B()->CreateLoad(v);
                }else
                    vv = v;
                
                venv->Enter( venv->MakeSymbol(head->m_field->Name()),
                             new EnvEntryVarLLVM( 
                                              t, 
                                              EnvEntryVar::kEnvEntryVar_For_Value, 
                                              t->GetLLVMType(),
                                              vv
                                            ) 
                           );
                
                head = head->next;
                i++;
            }
        }
        // process function body
         m_context->B()->SetInsertPoint( alevel->CurBB() );
        a = IRGenExp(venv,tenv,alevel,fundec_head->m_fundec->GetExp(),alevel->CurBB());
        m_context->B()->CreateRetVoid();
        
        m_context->B()->SetInsertPoint( level->CurBB() );
        //update type info from body if no type in function head
        if(fundec_head->m_fundec->Type()==0){
            m_logger.D("function return type is null");
            // TBD: update type info
            if(a!=0)
                dynamic_cast<EnvEntryFunLLVM*>( venv->Lookup( venv->MakeSymbol(fundec_head->m_fundec->Name()) ))->SetType(a->Type());
        }else
        {
            m_logger.D("type kind %d",a->Type()->Kind());
            if(a->Type()->Kind()!=TypeBase::kType_Nil)
            {
                TIGER_ASSERT(a->Type() == dynamic_cast<EnvEntryVar*>(tenv->Lookup(tenv->MakeSymbol(fundec_head->m_fundec->Type())))->Type(), "return type mismatch");
            }
        }
        

        delete a;
        
        venv->EndScope();
        
        fundec_head = fundec_head->next;
    }
}
void IRGen::IRGenDec(SymTab* venv,SymTab* tenv,Level* level,Dec* dec,llvm::BasicBlock* dest_bb)
{
    switch(dec->Kind())
    {
        case Dec::kDec_Var:{
            m_logger.D("type check with kDec_Var");
            IRGenResult* t;
            if(dynamic_cast<VarDec*>(dec)->GetExp()->Kind()==Exp::kExp_Array){
                m_logger.D("array var");
                //array
                // var a={x:int,y:a}
                //type b=array of a
                //var aa:=b[10] of i
                EnvEntryVarLLVM* p;
                // type a={x:int,y:a}
                //var i:=a{x=0,y=i}
                //p = dynamic_cast<EnvEntryVarLLVM*>(tenv->Lookup(tenv->MakeSymbol(dynamic_cast<ArrayTy*>(ty)->Name())));
                p = dynamic_cast<EnvEntryVarLLVM*>(tenv->Lookup( tenv->MakeSymbol( dynamic_cast<ArrayExp*>(dynamic_cast<VarDec*>(dec)->GetExp())->Name() ) ));
                llvm::Value* v = IRGenContext::Get()->B()->CreateAlloca( p->Type()->GetLLVMType() );

                //element ptr
                llvm::Type* typtr = p->Type()->GetLLVMType()->getContainedType(1);
                
                
                
                t = IRGenExp(venv,tenv,level,dynamic_cast<ArrayExp*>(dynamic_cast<VarDec*>(dec)->GetExp())->GetSize(),dest_bb);
                
                //allocate sized array
                //llvm::Value* vvv = IRGenContext::Get()->B()->CreateAlloca( typtr->getPointerElementType(),t->m_llvm_value );
                llvm::Value* vvv= nullptr;
                if(llvm::isa<llvm::PointerType>(t->m_llvm_value->getType())){
                    llvm::Value* x = IRGenContext::Get()->B()->CreateLoad(t->m_llvm_value);
                    //vvv = new llvm::AllocaInst( typtr->getPointerElementType(),x );
                    vvv = IRGenContext::Get()->B()->CreateAlloca( typtr->getPointerElementType(),x );
                }else
                    vvv = IRGenContext::Get()->B()->CreateAlloca( typtr->getPointerElementType(),t->m_llvm_value );
                //array elements
                llvm::Value* vvvv = IRGenContext::Get()->B()->CreateBitCast(vvv,typtr);
                llvm::Value* ind0[]={
                    m_context->B()->getInt32(0),
                    m_context->B()->getInt32(1)
                };
                llvm::Value* v_a = IRGenContext::Get()->B()->CreateGEP( p->Type()->GetLLVMType(),v, ind0);
                IRGenContext::Get()->B()->CreateStore( vvv,v_a);
                
                llvm::Value* ind[]={
                    m_context->B()->getInt32(0),
                    m_context->B()->getInt32(0)
                };
                //array size
                llvm::Value* v1 = IRGenContext::Get()->B()->CreateGEP( p->Type()->GetLLVMType(),v, ind);
                llvm::Value* v2;
                if(llvm::isa<llvm::PointerType>(t->m_llvm_value->getType())){
                    llvm::Value* v11 = IRGenContext::Get()->B()->CreateLoad(t->m_llvm_value);
                    v2 = IRGenContext::Get()->B()->CreateStore( v11,v1);
                }else
                    v2 = IRGenContext::Get()->B()->CreateStore( t->m_llvm_value,v1);
                // record it in symtab
                venv->Enter( 
                    venv->MakeSymbol( dynamic_cast<VarDec*>(dec)->GetSymbol() ), 
                    new EnvEntryVarLLVM( 
                        p->Type(), 
                        EnvEntryVarLLVM::kEnvEntryVarLLVM_For_Value,
                        p->Type()->GetLLVMType(),
                        v
                    ) 
                );
                ////TBD: element initialize
                delete t;
                return;
                
            }else if(dynamic_cast<VarDec*>(dec)->GetExp()->Kind()==Exp::kExp_Record){
                //record
                EnvEntryVarLLVM* p;
                // type a={x:int,y:a}
                //var i:=a{x=0,y=i}
                //p = dynamic_cast<EnvEntryVarLLVM*>(tenv->Lookup(tenv->MakeSymbol(dynamic_cast<ArrayTy*>(ty)->Name())));
                m_logger.D("record var");
                p = dynamic_cast<EnvEntryVarLLVM*>(tenv->Lookup( tenv->MakeSymbol( dynamic_cast<RecordExp*>(dynamic_cast<VarDec*>(dec)->GetExp())->Name() ) ));
                llvm::Value* v = IRGenContext::Get()->B()->CreateAlloca( p->Type()->GetLLVMType() );
                venv->Enter( 
                    venv->MakeSymbol( dynamic_cast<VarDec*>(dec)->GetSymbol() ), 
                    new EnvEntryVarLLVM( 
                        p->Type(), 
                        EnvEntryVarLLVM::kEnvEntryVarLLVM_For_Value,
                        p->Type()->GetLLVMType(),
                        v
                    ) 
                );
                //TBD: element initialize
                m_logger.D("record var end");
                return;
            
            }else{
                // simple var declaration
                // var a:=1
                m_logger.D("simple var");
                t = IRGenExp(venv,tenv,level,dynamic_cast<VarDec*>(dec)->GetExp(),dest_bb);
            }
            
        
            llvm::Value* v = m_context->B()->CreateAlloca(llvm::Type::getInt32Ty( *(m_context->C()) ));
            //llvm::Value* v = new llvm::AllocaInst(llvm::Type::getInt32Ty( *(m_context->C()) ));
            //llvm::dyn_cast<llvm::AllocaInst>(v)->insertBefore(allocapoint);
            m_context->B()->CreateStore(t->m_llvm_value,v);
            venv->Enter( 
                    venv->MakeSymbol( dynamic_cast<VarDec*>(dec)->GetSymbol() ), 
                    new EnvEntryVarLLVM( 
                        t->Type(), 
                        EnvEntryVarLLVM::kEnvEntryVarLLVM_For_Value,
                        llvm::Type::getInt32Ty( *(m_context->C()) ),
                        v
                    ) 
            );
            delete t;
            return ;
        }
        case Dec::kDec_Function:
        {
            //TBD: 
            IRGenFunctionDec(venv,tenv,level,dec,dest_bb);
            return;
        }
        case Dec::kDec_Type:{
            IRGenTypeDec(venv,tenv,level,dec);
            return;
        }
        default:
            break;
    }
}
IRGenResult* IRGen::IRGenExpLet(SymTab* venv,SymTab* tenv,Level* level,Exp* exp,llvm::BasicBlock* dest_bb)
{

    llvm::Value* ret;
    //check
    TIGER_ASSERT(exp->Kind()==Exp::kExp_Let,"let exp expected");
    
    DecList* declist;
    Exp* body;
    declist = dynamic_cast<LetExp*>(exp)->GetDecList();
    body = dynamic_cast<LetExp*>(exp)->GetBody();
    
    venv->BeginScope(ScopeMaker::kScope_Let);
    tenv->BeginScope(ScopeMaker::kScope_Invalid);// type should not use scope
    
    // dec list
    DecNode* p;
    if(declist){
        p = declist->GetHead();
        while(p){
            m_logger.D("TransDec var");
            IRGenDec(venv,tenv,level,p->m_dec,dest_bb);
            p = p->next;
        }
    }
    
    if(body){
        m_logger.D("TransDec body");
        IRGenExp(venv,tenv,level,body,dest_bb);
    }
    
    
    tenv->EndScope();
    venv->EndScope();
    
    return 0;
     
}
IRGenResult* IRGen::IRGenExp(SymTab* venv,SymTab* tenv,Level* level,Exp* e,llvm::BasicBlock* dest_bb)
{
    IRGenResult* result = new IRGenResult;
    switch( e->Kind() )
    {
        case Exp::kExp_Int:
        {
            Symbol t("int");
            
            result->m_type = tenv->Type(tenv->MakeSymbol(&t));//tiger type
            result->m_llvm_type = result->Type()->GetLLVMType();//i32Ty
            result->m_llvm_value = IRGenContext::Get()->B()->getInt32( dynamic_cast<IntExp*>(e)->GetInt() );//constant
            return result;
        }
        case Exp::kExp_Var:
        {
            delete result;//no use
            // get var's llvm value
            return IRGenVar(venv,tenv,level,dynamic_cast<VarExp*>(e)->GetVar(),dest_bb);
        }
        case Exp::kExp_Assign:
        {
            delete result;//no use
            m_logger.D("kExp_Assign");
            IRGenResult* a = IRGenVar(venv,tenv,level,dynamic_cast<AssignExp*>(e)->GetVar(),dest_bb);
            IRGenResult* b = IRGenExp(venv,tenv,level,dynamic_cast<AssignExp*>(e)->GetExp(),dest_bb);
            if( llvm::isa<llvm::PointerType>(b->m_llvm_value->getType()) )
            {
                /*
                assign
                dst must be pointer
                src must be dst pointer to
                */
                if(a->m_llvm_value->getType()->getPointerElementType()==b->m_llvm_value->getType())
                    IRGenContext::Get()->B()->CreateStore(b->m_llvm_value,a->m_llvm_value);
                else{
                    llvm::Value* b_v = IRGenContext::Get()->B()->CreateLoad(b->m_llvm_value);
                    IRGenContext::Get()->B()->CreateStore(b_v,a->m_llvm_value);
                }
            }else{
                IRGenContext::Get()->B()->CreateStore(b->m_llvm_value,a->m_llvm_value);
            }
            delete a;
            delete b;
            return 0;
        }
        case Exp::kExp_Seq:
        {
            delete result;//no use
            IRGenResult* tt;
            TIGER_ASSERT(e->Kind()==Exp::kExp_Seq,"seq exp expected");
            
            ExpNode* p = dynamic_cast<SeqExp*>(e)->GetList()->GetHead();
            if(p==0){
                m_logger.D("empty seq exp");
                return 0;
            }
            // return value ignore for now
            while(p){
                tt = IRGenExp(venv,tenv,level,p->m_exp,dest_bb);
                delete tt;
                p = p->next;
            }
            return 0;
        }
        case Exp::kExp_Call:
        {
            ExpNode* head;
            IRGenResult* t;
            TIGER_ASSERT(e->Kind()==Exp::kExp_Call,"call exp expected");
            EnvEntryFunLLVM* f = dynamic_cast<EnvEntryFunLLVM*>(venv->Lookup(venv->MakeSymbol(dynamic_cast<CallExp*>(e)->Name())));
            
            head = dynamic_cast<CallExp*>(e)->GetList()->GetHead();
            std::vector<llvm::Value*> parms;
            int i=0;
            while(head){
                t = IRGenExp(venv,tenv,level,head->m_exp,dest_bb);
                f->GetFun()->getFunctionType()->params()[i]->dump();
                t->m_llvm_type->dump();
                if(t->m_llvm_value->getType()!=t->m_llvm_type){
                    llvm::Value* v = m_context->B()->CreateLoad(t->m_llvm_value);
                    parms.push_back(v);
                }
                else
                    parms.push_back(t->m_llvm_value);
                    

                head = head->next;
            }
            m_context->B()->CreateCall(f->GetFun(),llvm::makeArrayRef<llvm::Value*>(parms));
            return 0;
        }
        case Exp::kExp_Op:
        {
            m_logger.D("kExp_Op");
            IRGenResult* l_val,*r_val;
            Exp* l,*r;
            llvm::Value* l_vv=0,*r_vv=0;
            Oper* oper;
            l = dynamic_cast<OpExp*>(e)->GetLeft();
            r = dynamic_cast<OpExp*>(e)->GetRight();
            l_val = IRGenExp(venv,tenv,level,l,0);
            r_val = IRGenExp(venv,tenv,level,r,0);
            if(!llvm::isa<llvm::Constant>(*(l_val->m_llvm_value))){
                if(!llvm::isa<llvm::PointerType>(l_val->m_llvm_value->getType()))
                    l_vv = l_val->m_llvm_value;//SSA
                else
                    l_vv = IRGenContext::Get()->B()->CreateLoad(l_val->m_llvm_value);//memory access
            }
            if(!llvm::isa<llvm::Constant>(*(r_val->m_llvm_value))){
                if(!llvm::isa<llvm::PointerType>(r_val->m_llvm_value->getType()))
                    r_vv = r_val->m_llvm_value;
                else
                    r_vv = IRGenContext::Get()->B()->CreateLoad(r_val->m_llvm_value);
            }
            oper = dynamic_cast<OpExp*>(e)->GetOper();
            switch(oper->Kind())
            {
                case Oper::kOper_Add:
                {
                    m_logger.D("add");
                    result->m_type = l_val->Type();
                    result->m_llvm_value = IRGenContext::Get()->B()->CreateAdd(l_vv?l_vv:l_val->m_llvm_value,r_vv?r_vv:r_val->m_llvm_value);
                    result->m_llvm_type = l_val->Type()->GetLLVMType();
                    delete l_val;
                    delete r_val;
                    return result;
                }
                case Oper::kOper_Sub:
                {
                    m_logger.D("sub");
                    result->m_type = l_val->Type();
                    result->m_llvm_value = IRGenContext::Get()->B()->CreateSub(l_vv?l_vv:l_val->m_llvm_value,r_vv?r_vv:r_val->m_llvm_value);
                    result->m_llvm_type = l_val->Type()->GetLLVMType();
                    delete l_val;
                    delete r_val;
                    return result;
                }
                case Oper::kOper_Mul:
                {
                }
                case Oper::kOper_Div:
                {
                }
                case Oper::kOper_Lt:
                {
                    /*
                    CreateIcmp();
                    CreateBr(cond,true_l,false_l);
                    */
                    llvm::Value* cond = m_context->B()->CreateICmp(llvm::CmpInst::ICMP_SLT,l_vv?l_vv:l_val->m_llvm_value,r_vv?r_vv:r_val->m_llvm_value);
                    result->m_type = l_val->Type();
                    result->m_llvm_value = cond;
                    result->m_llvm_type = l_val->Type()->GetLLVMType();
                    delete l_val;
                    delete r_val;
                    return result;
                }
                case Oper::kOper_Gt:
                {
                    /*
                    CreateIcmp();
                    CreateBr(cond,true_l,false_l);
                    */
                    llvm::Value* cond = m_context->B()->CreateICmp(llvm::CmpInst::ICMP_SGT,l_vv?l_vv:l_val->m_llvm_value,r_vv?r_vv:r_val->m_llvm_value);
                    result->m_type = l_val->Type();
                    result->m_llvm_value = cond;
                    result->m_llvm_type = l_val->Type()->GetLLVMType();
                    delete l_val;
                    delete r_val;
                    return result;
                }
                case Oper::kOper_Le:
                {
                    /*
                    CreateIcmp();
                    CreateBr(cond,true_l,false_l);
                    */
                    llvm::Value* cond = m_context->B()->CreateICmp(llvm::CmpInst::ICMP_SLE,l_vv?l_vv:l_val->m_llvm_value,r_vv?r_vv:r_val->m_llvm_value);
                    result->m_type = l_val->Type();
                    result->m_llvm_value = cond;
                    result->m_llvm_type = l_val->Type()->GetLLVMType();
                    delete l_val;
                    delete r_val;
                    return result;
                }
                case Oper::kOper_Ge:
                {
                    /*
                    CreateIcmp();
                    CreateBr(cond,true_l,false_l);
                    */
                    llvm::Value* cond = m_context->B()->CreateICmp(llvm::CmpInst::ICMP_SGE,l_vv?l_vv:l_val->m_llvm_value,r_vv?r_vv:r_val->m_llvm_value);
                    result->m_type = l_val->Type();
                    result->m_llvm_value = cond;
                    result->m_llvm_type = l_val->Type()->GetLLVMType();
                    delete l_val;
                    delete r_val;
                    return result;
                }
                case Oper::kOper_Eq:
                {
                    /*
                    CreateIcmp();
                    CreateBr(cond,true_l,false_l);
                    */
                    llvm::Value* cond = m_context->B()->CreateICmp(llvm::CmpInst::ICMP_EQ,l_vv?l_vv:l_val->m_llvm_value,r_vv?r_vv:r_val->m_llvm_value);
                    result->m_type = l_val->Type();
                    result->m_llvm_value = cond;
                    result->m_llvm_type = l_val->Type()->GetLLVMType();
                    delete l_val;
                    delete r_val;
                    return result;
                }
                case Oper::kOper_Neq:
                {
                    /*
                    CreateIcmp();
                    CreateBr(cond,true_l,false_l);
                    */
                    llvm::Value* cond = m_context->B()->CreateICmp(llvm::CmpInst::ICMP_NE,l_vv?l_vv:l_val->m_llvm_value,r_vv?r_vv:r_val->m_llvm_value);
                    result->m_type = l_val->Type();
                    result->m_llvm_value = cond;
                    result->m_llvm_type = l_val->Type()->GetLLVMType();
                    delete l_val;
                    delete r_val;
                    return result;
                }
                default:
                {
                    TIGER_ASSERT(0,"Should not reach here");
                }
            }
        }
        case Exp::kExp_If:
        {
            delete result;//no use
            /*
            XXXX1
            if_statement
            XXXX2
            
            if need create new bb, new bb should jump to XXXX2
            */
            Exp* test;
            Exp* then;
            Exp* elsee;
            
            IRGenResult* test_val;
            IRGenResult* then_val;
            IRGenResult* elsee_val;
            
            llvm::BasicBlock* then_bb;
            llvm::BasicBlock* elsee_bb;
            llvm::BasicBlock* end_bb;
            
            test = dynamic_cast<IfExp*>(e)->GetTest();
            then = dynamic_cast<IfExp*>(e)->GetThen();
            elsee = dynamic_cast<IfExp*>(e)->GetElsee();
            
            then_bb = llvm::BasicBlock::Create( *(m_context->C()),"then",level->GetFunc());
            elsee_bb = llvm::BasicBlock::Create( *(m_context->C()),"else",level->GetFunc());
            end_bb = llvm::BasicBlock::Create( *(m_context->C()),"end",level->GetFunc());
            
            test_val = IRGenExp(venv,tenv,level,test,end_bb);
            m_context->B()->CreateCondBr(test_val->m_llvm_value,then_bb,elsee_bb);
            
            
            m_context->B()->SetInsertPoint(then_bb);
            then_val = IRGenExp(venv,tenv,level,then,end_bb);
            m_context->B()->SetInsertPoint(then_bb);
            m_context->B()->CreateBr(end_bb);
            
            m_context->B()->SetInsertPoint(elsee_bb);
            elsee_val = IRGenExp(venv,tenv,level,elsee,end_bb);
            m_context->B()->SetInsertPoint(elsee_bb);
            m_context->B()->CreateBr(end_bb);
            
            m_context->B()->SetInsertPoint(end_bb);
            //if(dest_bb)
            //    m_context->B()->CreateBr(dest_bb);
            
            
            m_context->B()->SetInsertPoint(end_bb);
            
            delete test_val;
            delete then_val;
            delete elsee_val;
            return 0;
            
        }
        case Exp::kExp_While:
        {
            delete result;//no use
            /*
            XXXX1
            while_statement
            XXXX2
            while need jump to XXXX2 // create new bb  the new bb should jump to the XXXX2
            
            */
            Exp* test;
            Exp* body;
            
            IRGenResult* test_val;
            IRGenResult* body_val;
            
            llvm::BasicBlock* loop_bb;
            llvm::BasicBlock* body_bb;
            llvm::BasicBlock* end_bb;
            
            //dyn_cast<WhileExp>(e)
            test = dyn_cast<WhileExp>(e)->GetTest();
            body = dyn_cast<WhileExp>(e)->GetExp();
            
            loop_bb = llvm::BasicBlock::Create( *(m_context->C()),"loop",level->GetFunc());
            body_bb = llvm::BasicBlock::Create( *(m_context->C()),"body",level->GetFunc());
            end_bb = llvm::BasicBlock::Create( *(m_context->C()),"end",level->GetFunc());
            
            m_context->B()->CreateBr(loop_bb);
            m_context->B()->SetInsertPoint(loop_bb);
            test_val = IRGenExp(venv,tenv,level,test,end_bb);
            m_context->B()->SetInsertPoint(loop_bb);
            m_context->B()->CreateCondBr(test_val->m_llvm_value,body_bb,end_bb);
            
            m_context->B()->SetInsertPoint(body_bb);
            body_val = IRGenExp(venv,tenv,level,body,end_bb);///
            //m_context->B()->SetInsertPoint(body_bb);
          
            m_context->B()->CreateBr(loop_bb);
            
            m_context->B()->SetInsertPoint(end_bb);
            if(dest_bb)
                m_context->B()->CreateBr(dest_bb);
            delete test_val;
            delete body_val;
            return 0;
        }
        case Exp::kExp_Let:
        {
            delete result;//no use
            return IRGenExpLet(venv,tenv,level,e,dest_bb);
        }
        default:
        {
            return 0;
        }
    }
}



}//namespace tiger