#include <iostream>

#include "scanner.h"
#include "absyn.h"
#include "parser.h"
#include "tiger_log.h"
#include "tiger_assert.h"
#include "types.h"
#include "type_check.h"
#include "escape.h"
#include "tree.h"
#include "tiger_llvm.h"
#include <llvm/IR/ValueSymbolTable.h>
#include "irgencontext.h"

void test_StringSourceCodeStream()
{
    char *string=(char*)"just a test";
    s32 len=strlen(string);
    tiger::scanner::StringSourceCodeStream stream((char*)"just a test");
    for(int i=0;i<len;i++)
        assert(*(string+i)==stream.Next());
    assert(tiger::scanner::kSourceCodeStream_EOS==stream.Next());
}
void test_FileSourceCodeStream()
{
    char *string=(char*)"just b test";
    s32 len=strlen(string);
    tiger::scanner::FileSourceCodeStream stream((char*)"a.txt");
    for(int i=0;i<len;i++)
        assert(*(string+i)==stream.Next());
    assert(tiger::scanner::kSourceCodeStream_EOS==stream.Next());
}
void test_Next_With_StringSourceCodeStream()
{
    s32 v,v1;
    tiger::Token t,t1;
    tiger::scanner::StringSourceCodeStream stream((char*)".=");
    tiger::scanner::Scanner scanner(&stream);
    
    v = scanner.Next(&t);
    assert(v==tiger::kToken_DOT);
    std::cout<<t.lineno<<","<<t.pos<<","<<t.abs_pos<<std::endl;
    
    v1 = scanner.Next(&t1);
    assert(v1==tiger::kToken_EQUAL);
    std::cout<<t1.lineno<<","<<t1.pos<<","<<t1.abs_pos<<std::endl;
    
    scanner.Back(&t1);
    scanner.Back(&t);
    
    v = scanner.Next(&t);
    assert(v==tiger::kToken_DOT);
    std::cout<<t.lineno<<","<<t.pos<<","<<t.abs_pos<<std::endl;


}
void test_Next_With_FileSourceCodeStream()
{
    s32 v;
    tiger::Token t;
    tiger::scanner::FileSourceCodeStream stream((char*)"a.txt");
    tiger::scanner::Scanner scanner(&stream);
    
    t.Clear();
    v = scanner.Next(&t);
    assert(v==tiger::kToken_ID);
    assert(strcmp(t.u.name,"just")==0);
    std::cout<<t.lineno<<","<<t.pos<<std::endl;

}
void test_sbsyn()
{
    tiger::Symbol *a,*b;
    a = new tiger::Symbol((char*)"a");
    b = new tiger::Symbol((char*)"b");
    tiger::SimpleVar* var = new tiger::SimpleVar(a);
}
void test_parser()
{
    tiger::scanner::FileSourceCodeStream stream((char*)"b.txt");
    //tiger::scanner::StringSourceCodeStream stream((char*)"`");
    tiger::Exp* exp;
    tiger::parser::Parser parser(&stream);
    parser.Parse(&exp);
    delete exp;
}
void test_Logger(){
    tiger::LoggerFile logger;
    logger.SetLevel(tiger::LoggerBase::kLogger_Level_Error);
    logger.D("debug info");
    logger.I("info info");
    logger.W("warn info");
    logger.E("error info");
}
void test_assert(){
    TIGER_ASSERT(1==0,"Expected %s %d",__FILE__,__LINE__);
}
void test_types(){
    tiger::TypeBase* a;
    a = new tiger::TypeNil;
    
    assert(a->Kind()==tiger::TypeBase::kType_Nil);
    tiger::LoggerStdio logger;
    logger.SetLevel(tiger::LoggerBase::kLogger_Level_Error);
    logger.D("%d",a->Kind());
}
void test_symtab(){
    tiger::SymTab symtab;
    symtab.Enter(symtab.MakeSymbol(new tiger::Symbol("a")),0);
    symtab.Enter(symtab.MakeSymbol(new tiger::Symbol("a")),0);
    symtab.BeginScope(tiger::ScopeMaker::kScope_Invalid);
    symtab.Enter(symtab.MakeSymbol(new tiger::Symbol("a")),0);
    symtab.Enter(symtab.MakeSymbol(new tiger::Symbol("b")),0);
    symtab.EndScope();
    std::cout<<"-----"<<std::endl;

}
void test_typecheck(){
    tiger::Exp* exp;
    tiger::TypeCheckResult* ty;
    
    tiger::LoggerStdio logger;
    logger.SetLevel(tiger::LoggerBase::kLogger_Level_Error);
    //logger.setModule("main");
    
    //tiger::scanner::FileSourceCodeStream stream((char*)"a.txt");
    tiger::scanner::FileSourceCodeStream stream((char*)"b.txt");
    //tiger::scanner::StringSourceCodeStream stream((char*)"let var a:=1 var b:=2 var c:=0 in c:=a+b end");
    
    /* generate sbstract syntax tree*/
    tiger::parser::Parser parser(&stream);
    parser.Parse(&exp);

    tiger::SymTab venv,tenv;
    /* init types */
    tenv.Enter(tenv.MakeSymbolFromString("nil"),new tiger::EnvEntryVar(new tiger::TypeNil(),tiger::EnvEntryVar::kEnvEntryVar_For_Type, (tiger::VarAccess*)0));
    tenv.Enter(tenv.MakeSymbolFromString("void"),new tiger::EnvEntryVar(new tiger::TypeVoid(),tiger::EnvEntryVar::kEnvEntryVar_For_Type, (tiger::VarAccess*)0));
    tenv.Enter(tenv.MakeSymbolFromString("int"),new tiger::EnvEntryVar(new tiger::TypeInt(),tiger::EnvEntryVar::kEnvEntryVar_For_Type, (tiger::VarAccess*)0));
    tenv.Enter(tenv.MakeSymbolFromString("string"),new tiger::EnvEntryVar(new tiger::TypeString(),tiger::EnvEntryVar::kEnvEntryVar_For_Type, (tiger::VarAccess*)0));
    
    /* for each external function, it's impossible to access outer level's variable 
    the outer most level do not need frame and actual list 
    */
    
    /* internal functions */
    /* print(x:int)*/
    tiger::TypeFieldNode* node;
    node = new tiger::TypeFieldNode;
    node->m_field = new tiger::TypeField(tenv.MakeSymbolFromString("x"),tenv.Type(tenv.MakeSymbolFromString("string")));
    venv.Enter(venv.MakeSymbolFromString("print"),new tiger::EnvEntryFun(new tiger::TypeFieldList(node),0,0/*level*/,tiger::TempLabel::NewNamedLabel("print"),1/*kind*/));
    
    /* getchar()*/
    //tiger::TypeFieldNode* node;
    venv.Enter(venv.MakeSymbolFromString("getchar"),new tiger::EnvEntryFun(new tiger::TypeFieldList(0),tenv.Type(tenv.MakeSymbolFromString("string")),0,0/*level*/,1/*kind*/));

    /* ord(s:string):int*/
    //tiger::TypeFieldNode* node;
    node = new tiger::TypeFieldNode;
    node->m_field = new tiger::TypeField(tenv.MakeSymbolFromString("s"),tenv.Type(tenv.MakeSymbolFromString("string")));
    venv.Enter(venv.MakeSymbolFromString("ord"),new tiger::EnvEntryFun(new tiger::TypeFieldList(node),tenv.Type(tenv.MakeSymbolFromString("int")),0,0,1/*kind*/));
    
    /* mymalloc(size:int):int*/
    //tiger::TypeFieldNode* node;
    node = new tiger::TypeFieldNode;
    node->m_field = new tiger::TypeField(tenv.MakeSymbolFromString("size"),tenv.Type(tenv.MakeSymbolFromString("int")));
    venv.Enter(venv.MakeSymbolFromString("my_malloc"),new tiger::EnvEntryFun(new tiger::TypeFieldList(node),tenv.Type(tenv.MakeSymbolFromString("int")),0,0,1/*kind*/));
    
    /* chr(i:int):string*/
    //tiger::TypeFieldNode* node;
    node = new tiger::TypeFieldNode;
    node->m_field = new tiger::TypeField(tenv.MakeSymbolFromString("i"),tenv.Type(tenv.MakeSymbolFromString("int")));
    venv.Enter(venv.MakeSymbolFromString("chr"),new tiger::EnvEntryFun(new tiger::TypeFieldList(node),tenv.Type(tenv.MakeSymbolFromString("string")),0,0,1/*kind*/));
    
    // find escape 
    //tiger::EscapeHelper escaper;
    //escaper.FindEscape(exp);
    
    tiger::TypeChecker tc;
    ty = tc.TypeCheck(&venv, &tenv, exp);
    
    delete ty;
    
    /* free */
    delete exp;
    
    tiger::TempLabel::Exit();
}
#if 0
void test_tree_gen(){
    tiger::Exp* exp;
    tiger::TreeGenResult* tr;
    tiger::StatementBase* s;
    
    tiger::LoggerStdio logger;
    logger.SetLevel(tiger::LoggerBase::kLogger_Level_Error);
    //logger.setModule("main");
    
    //tiger::scanner::FileSourceCodeStream stream((char*)"a.txt");
    //tiger::scanner::FileSourceCodeStream stream((char*)"b.txt");
    tiger::scanner::StringSourceCodeStream stream((char*)"let type a={x:int,y:int} in end");
    
    /* generate sbstract syntax tree*/
    tiger::parser::Parser parser(&stream);
    parser.Parse(&exp);

    tiger::SymTab venv,tenv;
    /* init types */
    tenv.Enter(tenv.MakeSymbolFromString("nil"),new tiger::EnvEntryVar(new tiger::TypeNil(),tiger::EnvEntryVar::kEnvEntryVar_For_Type, (tiger::VarAccess*)0));
    tenv.Enter(tenv.MakeSymbolFromString("void"),new tiger::EnvEntryVar(new tiger::TypeVoid(),tiger::EnvEntryVar::kEnvEntryVar_For_Type, (tiger::VarAccess*)0));
    tenv.Enter(tenv.MakeSymbolFromString("int"),new tiger::EnvEntryVar(new tiger::TypeInt(),tiger::EnvEntryVar::kEnvEntryVar_For_Type, (tiger::VarAccess*)0));
    tenv.Enter(tenv.MakeSymbolFromString("string"),new tiger::EnvEntryVar(new tiger::TypeString(),tiger::EnvEntryVar::kEnvEntryVar_For_Type, (tiger::VarAccess*)0));
    
    

    /* for each external function, it's impossible to access outer level's variable 
    the outer most level do not need frame and actual list 
    */
    
    /* internal functions */
    /* print(x:int)*/
    tiger::TypeFieldNode* node;
    node = new tiger::TypeFieldNode;
    node->m_field = new tiger::TypeField(tenv.MakeSymbolFromString("x"),tenv.Type(tenv.MakeSymbolFromString("string")));
    venv.Enter(venv.MakeSymbolFromString("print"),new tiger::EnvEntryFun(new tiger::TypeFieldList(node),0,0/*level*/,tiger::TempLabel::NewNamedLabel("print"),1));
    
    /*
    printint(x:int)
    */
    node = new tiger::TypeFieldNode;
    node->m_field = new tiger::TypeField(tenv.MakeSymbolFromString("x"),tenv.Type(tenv.MakeSymbolFromString("int")));
    venv.Enter(venv.MakeSymbolFromString("printint"),new tiger::EnvEntryFun(new tiger::TypeFieldList(node),0,0/*level*/,tiger::TempLabel::NewNamedLabel("printint"),1));
    
    /* getchar()*/
    //tiger::TypeFieldNode* node;
    venv.Enter(venv.MakeSymbolFromString("getchar"),new tiger::EnvEntryFun(new tiger::TypeFieldList(0),tenv.Type(tenv.MakeSymbolFromString("string")),0,0,1));

    /* ord(s:string):int*/
    //tiger::TypeFieldNode* node;
    node = new tiger::TypeFieldNode;
    node->m_field = new tiger::TypeField(tenv.MakeSymbolFromString("s"),tenv.Type(tenv.MakeSymbolFromString("string")));
    venv.Enter(venv.MakeSymbolFromString("ord"),new tiger::EnvEntryFun(new tiger::TypeFieldList(node),tenv.Type(tenv.MakeSymbolFromString("int")),0,0,1));
    
    /* chr(i:int):string*/
    //tiger::TypeFieldNode* node;
    node = new tiger::TypeFieldNode;
    node->m_field = new tiger::TypeField(tenv.MakeSymbolFromString("i"),tenv.Type(tenv.MakeSymbolFromString("int")));
    venv.Enter(venv.MakeSymbolFromString("chr"),new tiger::EnvEntryFun(new tiger::TypeFieldList(node),tenv.Type(tenv.MakeSymbolFromString("string")),0,0,1));
    
    /* mymalloc(size:int):int*/
    //tiger::TypeFieldNode* node;
    node = new tiger::TypeFieldNode;
    node->m_field = new tiger::TypeField(tenv.MakeSymbolFromString("size"),tenv.Type(tenv.MakeSymbolFromString("int")));
    venv.Enter(venv.MakeSymbolFromString("my_malloc"),new tiger::EnvEntryFun(new tiger::TypeFieldList(node),tenv.Type(tenv.MakeSymbolFromString("int")),0,tiger::TempLabel::NewNamedLabel("my_malloc"),1/*kind*/));

    // find escape 
    #if 0
    tiger::EscapeHelper escaper;
    escaper.FindEscape(exp);
    #endif
    tiger::TreeGenerator tg;
    tr = tg.TreeGen(&venv,&tenv,tg.OuterMostLevel(),exp,0);
    
    #if 0
    tg.ProceeExternalFunctions(&venv,&tenv);
    
    // dump tree
    char t[1024]={0};
    
    if(tr->Kind()==tiger::TreeGenResult::kTreeGenResult_Ex)
    {
        tr->m_exp->Dump(t);
        printf("\n%s\n",t);
        //delete tr->m_exp;
        s = new tiger::StatementExp(tr->m_exp);
    }
    if(tr->Kind()==tiger::TreeGenResult::kTreeGenResult_Nx)
    {
        tr->m_statement->Dump(t);
        printf("\n%s\n",t);
        //delete tr->m_statement;
        s = tr->m_statement;
    }
    // only call ProcessEntryExit for outmost code
    // for function, just view change
    s = tg.ProcessEntryExit(&venv,&tenv,tg.OuterMostLevel(),s);
    #if 0
    // function
    tiger::FragList* fl;
    
    fl = tg.GetFragList();
    s = fl->FindByLabelName("foo")->GetStatement();
    s->Dump(t);
    printf("\nfoo:\n%s\n",t);
    #endif
    //s = tg.ProcessEntryExit(&venv,&tenv,tg.OuterMostLevel(),s);
    //canonical
    tiger::Canon canon;
    s = canon.Statementize( s );
    s->Dump(t);
    printf("\ncanonical:\n%s\n",t);
    
    // linearlize
    tiger::StatementBaseList* l;
    l = canon.Linearize( s );
    l->Dump(t);
    printf("\nlinearlize:\n%s\n",t);
    
    tiger::CanonBlockList* cl;
    cl = canon.BasicBlocks(l);
    cl->Dump(t);
    printf("\nblock:\n%s\n",t);
    
    //trace schedule
    tiger::StatementBaseList* sl;
    sl = canon.TraceSchedule(cl);
    sl->Dump(t);
    printf("\ntrace:\n%s\n",t);
    
    //delete l;
    //delete cl;
    
    tiger::CodeGenerator* cg = new tiger::CodeGenerator;
    tiger::InstrList* il;
    il = cg->CodeGen(0,sl);
    //delete sl;
    il->Dump(t);
    printf("%s\n",t);
    
    // register allocation
    // graph
    tiger::FlowGraph* fg = new tiger::FlowGraph;
    tiger::Graph* g = fg->AssemFlowGraph(il);
    tiger::Liveness* ln = new tiger::Liveness;
    tiger::LivenessResult* lr;
    tiger::ColorList* col;
    lr = ln->LivenessCalc(g);
    
    
    
    
    FILE* f = fopen("tiger.S","w");
    RegAlloc(tg.TempMap(),lr,0,il);
    cg->Output(tg.TempMap(),il,f); //gen real assemble code
    fclose(f);
        
    //delete fg;
    //delete g;
    //delete ln;
    
    //delete tr;
    //delete lr;
    //delete il;
    //delete cg;
    /* free */
    #endif
    delete exp;
}
#endif
#if 0
void test_code_gen(){
    tiger::Exp* exp;
    tiger::ExpBaseTy* ty;
    
    tiger::LoggerStdio logger;
    logger.SetLevel(tiger::LoggerBase::kLogger_Level_Error);
    //logger.setModule("main");
    
    tiger::scanner::FileSourceCodeStream stream((char*)"a.txt");
    //tiger::scanner::FileSourceCodeStream stream((char*)"b.txt");
    //tiger::scanner::StringSourceCodeStream stream((char*)"let var a:=1 var b:=2 var c:=0 in c:=a+b end");
    
    /* generate sbstract syntax tree*/
    tiger::parser::Parser parser(&stream);
    parser.Parse(&exp);

    tiger::SymTab venv,tenv;
    /* init types */
    tenv.Enter(tenv.MakeSymbolFromString("nil"),new tiger::EnvEntryVar(new tiger::TypeNil(),tiger::EnvEntryVar::kEnvEntryVar_For_Type, 0));
    tenv.Enter(tenv.MakeSymbolFromString("void"),new tiger::EnvEntryVar(new tiger::TypeVoid(),tiger::EnvEntryVar::kEnvEntryVar_For_Type, 0));
    tenv.Enter(tenv.MakeSymbolFromString("int"),new tiger::EnvEntryVar(new tiger::TypeInt(),tiger::EnvEntryVar::kEnvEntryVar_For_Type, 0));
    tenv.Enter(tenv.MakeSymbolFromString("string"),new tiger::EnvEntryVar(new tiger::TypeString(),tiger::EnvEntryVar::kEnvEntryVar_For_Type, 0));
    
    /* for each external function, it's impossible to access outer level's variable 
    the outer most level do not need frame and actual list 
    */
    
    /* internal functions */
    /* print(x:int)*/
    tiger::TypeFieldNode* node;
    node = new tiger::TypeFieldNode;
    node->m_field = new tiger::TypeField(tenv.MakeSymbolFromString("x"),tenv.Type(tenv.MakeSymbolFromString("string")));
    venv.Enter(venv.MakeSymbolFromString("print"),new tiger::EnvEntryFun(new tiger::TypeFieldList(node),0,0/*level*/,tiger::TempLabel::NewNamedLabel("print"),1));
    
    /* getchar()*/
    //tiger::TypeFieldNode* node;
    venv.Enter(venv.MakeSymbolFromString("getchar"),new tiger::EnvEntryFun(new tiger::TypeFieldList(0),tenv.Type(tenv.MakeSymbolFromString("string")),0,0,1));

    /* ord(s:string):int*/
    //tiger::TypeFieldNode* node;
    node = new tiger::TypeFieldNode;
    node->m_field = new tiger::TypeField(tenv.MakeSymbolFromString("s"),tenv.Type(tenv.MakeSymbolFromString("string")));
    venv.Enter(venv.MakeSymbolFromString("ord"),new tiger::EnvEntryFun(new tiger::TypeFieldList(node),tenv.Type(tenv.MakeSymbolFromString("int")),0,0,1));
    
    /* chr(i:int):string*/
    //tiger::TypeFieldNode* node;
    node = new tiger::TypeFieldNode;
    node->m_field = new tiger::TypeField(tenv.MakeSymbolFromString("i"),tenv.Type(tenv.MakeSymbolFromString("int")));
    venv.Enter(venv.MakeSymbolFromString("chr"),new tiger::EnvEntryFun(new tiger::TypeFieldList(node),tenv.Type(tenv.MakeSymbolFromString("string")),0,0,1));
    
    // find escape 
    tiger::EscapeHelper escaper;
    escaper.FindEscape(exp);
    
    tiger::Translator translator;
    ty=translator.TransExp(&venv,&tenv,translator.OuterMostLevel(),exp,0);
    
    translator.Traverse( ty->Tree() );
    
    // dump tree
    char t[1024]={0};
    
    if(ty->Tree()->Kind()==tiger::TreeBase::kTreeBase_Ex)
    {
        dynamic_cast<tiger::TreeBaseEx*>(ty->Tree())->GetExp()->Dump(t);
        
        
        delete dynamic_cast<tiger::TreeBaseEx*>(ty->Tree())->GetExp();
    }
    
    if(ty->Tree()->Kind()==tiger::TreeBase::kTreeBase_Nx)
    {
        dynamic_cast<tiger::TreeBaseNx*>(ty->Tree())->GetStatement()->Dump(t);
       
        //printf("\n%s\n",t);
#if 1
        tiger::Canon canon;
        tiger::StatementBase* s;
        s = dynamic_cast<tiger::TreeBaseNx*>(ty->Tree())->GetStatement();
        s = canon.Statementize( s );
        // linearlize
        tiger::StatementBaseList* l;
        l = canon.Linearize( s );
        l->Dump(t);
        printf("%s\n",t);
#endif
#if 0
        // block
        tiger::CanonBlockList* cl;
        cl = canon.BasicBlocks(l);
        cl->Dump(t);
        //printf("%s\n",t);
        
        //trace schedule
        tiger::StatementBaseList* sl;
        sl = canon.TraceSchedule(cl);
        sl->Dump(t);
        //printf("%s\n",t);
        
        // assem
        tiger::CodeGenerator* cg = new tiger::CodeGenerator;
        tiger::InstrList* il;
        il = cg->CodeGen(0,sl);
        il->Dump(t);
        printf("%s\n",t);
        
        // graph
        tiger::FlowGraph* fg = new tiger::FlowGraph;
        tiger::Graph* g = fg->AssemFlowGraph(il);
        tiger::Liveness* ln = new tiger::Liveness;
        tiger::LivenessResult* lr;
        tiger::ColorList* col;
        lr = ln->LivenessCalc(g);
        col = tiger::RegAlloc(lr,0,il);
        FILE* f = fopen("tiger.S","w");
        cg->Output(col,il,f); //gen real assemble code
        fclose(f);
#endif
        //delete dynamic_cast<tiger::TreeBaseNx*>(ty->Tree())->GetStatement();
    }
    if(ty->Tree()->Kind()==tiger::TreeBase::kTreeBase_Cx)
    {
        dynamic_cast<tiger::TreeBaseCx*>(ty->Tree())->GetStatement()->Dump(t);
        
        
        delete dynamic_cast<tiger::TreeBaseCx*>(ty->Tree())->GetStatement();
    }
    
    //printf("\n%s\n",t);
    
    {
        tiger::FragList* fl;
        tiger::StatementBase* s;
        fl = translator.GetFragList();
        s = fl->FindByLabelName("printboard")->GetStatement();
        tiger::Canon canon;
        
        s = canon.Statementize( s );
        // linearlize
        tiger::StatementBaseList* l;
        l = canon.Linearize( s );
        l->Dump(t);
        printf("%s\n",t);
    }
    //translator.TraverseFragList();
    
    delete ty;
    
    /* free */
    delete exp;
}
#endif
void test_escape()
{
    tiger::Exp* exp;
    
    //tiger::scanner::FileSourceCodeStream stream((char*)"a.txt");
    //tiger::scanner::FileSourceCodeStream stream((char*)"b.txt");
    tiger::scanner::StringSourceCodeStream stream((char*)"let type a1={a:int,b:string} var a_:=a1{a=0,b=\"\"} in let in a_.b:=\"\" end end");
    
    /* generate sbstract syntax tree*/
    tiger::parser::Parser parser(&stream);
    parser.Parse(&exp);

    
    tiger::EscapeHelper escaper;
    escaper.FindEscape(exp);
   
    /* free */
    delete exp;
}
void test_tree(){
    tiger::LoggerStdio logger;
    logger.SetModule("tree");
    logger.SetLevel(tiger::LoggerBase::kLogger_Level_Error);
    
    tiger::ExpBaseName* e;
    e = new tiger::ExpBaseName(tiger::TempLabel::NewNamedLabel("main"));
    
    logger.D(e->GetLabel()->Name());
    
    tiger::TempLabel::Exit();
    
    delete e;
    
}
#if 0
void test_litstringlist(){
    tiger::LoggerStdio logger;
    logger.SetModule("tree");
    logger.SetLevel(tiger::LoggerBase::kLogger_Level_Error);
    
    tiger::LitStringList list;
    tiger::Label* l1,* l2,* l3;
    l1 = tiger::TempLabel::NewNamedLabel("a");
    l2 = tiger::TempLabel::NewNamedLabel("b");
    l3 = tiger::TempLabel::NewNamedLabel("c");
    list.Insert(l1,"a");
    list.Insert(l1,"b");
    logger.D(list.Find(l1));
    tiger::TempLabel::Exit();
}
void test_canon(){
    tiger::LoggerStdio logger;
    logger.SetModule("canon");
    logger.SetLevel(tiger::LoggerBase::kLogger_Level_Error);
    tiger::Canon canon;
    
    tiger::StatementBase* s;
    tiger::ExpBase* e;
    /*
    s = new tiger::StatementMove(new tiger::ExpBaseTemp(tiger::TempLabel::NewTemp()),new tiger::ExpBaseConst(1));
    e = new tiger::ExpBaseConst(2);
    
    e = new tiger::ExpBaseEseq(s,e);
    s = new tiger::StatementMove(new tiger::ExpBaseTemp(tiger::TempLabel::NewTemp()), e);
    e = new tiger::ExpBaseEseq( s, new tiger::ExpBaseTemp(tiger::TempLabel::NewTemp()) );
    s = new tiger::StatementMove(e,new tiger::ExpBaseConst(4));
    */
    tiger::ExpBaseList* el1 = new tiger::ExpBaseList;
    tiger::ExpBaseList* el2 = new tiger::ExpBaseList;
    el1->Insert(new tiger::ExpBaseConst(11),tiger::ExpBaseList::kExpBaseList_Rear);
    el2->Insert(new tiger::ExpBaseConst(12),tiger::ExpBaseList::kExpBaseList_Rear);
    e = new tiger::ExpBaseBinop(  tiger::BinaryOp::kBinaryOp_Add, 
            new tiger::ExpBaseCall(new tiger::ExpBaseName(tiger::TempLabel::NewNamedLabel("foo")),el1), 
            new tiger::ExpBaseCall(new tiger::ExpBaseName(tiger::TempLabel::NewNamedLabel("bar")),el2)
        );
    
    s = new tiger::StatementMove(new tiger::ExpBaseTemp(tiger::TempLabel::NewTemp()),e);
    
    tiger::TreeGenerator translator;
    
    char t[1024]={0};
    s->Dump(t);
    printf("\n%s\n",t);
    
    s = canon.Statementize( s );
    
    s->Dump(t);
    printf("\n%s\n",t);
    
    // linearlize
    tiger::StatementBaseList* l;
    l = canon.Linearize( s );
    l->Dump(t);
    printf("%s\n",t);
    
    // block
    tiger::CanonBlockList* cl;
    cl = canon.BasicBlocks(l);
    cl->Dump(t);
    printf("%s\n",t);
    
    // assem
    tiger::CodeGenerator* cg = new tiger::CodeGenerator;
    tiger::InstrList* il;
    il = cg->CodeGen(0,l);
    il->Dump(t);
    printf("%s\n",t);
    
    delete l;
    delete cl;
    delete il;
    delete cg; 
    tiger::TempLabel::Exit();
}
void test_liveness()
{
    tiger::InstrList* il;
    tiger::InstrBase* instr;
    tiger::TempList* dst;
    tiger::TempList* src;
    il = new tiger::InstrList;
    
    dst = new tiger::TempList;
    src = new tiger::TempList;
    dst->Insert(tiger::TempLabel::NewNamedTemp("a"),tiger::TempList::kTempList_Rear);
    instr = new tiger::InstrMove("move d0',0",dst,src);
    il->Insert(instr,tiger::InstrList::kInstrList_Rear);
    
    
    dst = new tiger::TempList;
    src = new tiger::TempList;
    instr = new tiger::InstrLabel("loop:",tiger::TempLabel::NewNamedLabel("loop"));
    il->Insert(instr,tiger::InstrList::kInstrList_Rear);
    
    dst = new tiger::TempList;
    src = new tiger::TempList;
    dst->Insert(tiger::TempLabel::NewNamedTemp("b"),tiger::TempList::kTempList_Rear);
    src->Insert(tiger::TempLabel::NewNamedTemp("a"),tiger::TempList::kTempList_Rear);
    instr = new tiger::InstrOper("add d0',s0,1",dst,src,0);
    il->Insert(instr,tiger::InstrList::kInstrList_Rear);
    
    dst = new tiger::TempList;
    src = new tiger::TempList;
    dst->Insert(tiger::TempLabel::NewNamedTemp("c"),tiger::TempList::kTempList_Rear);
    src->Insert(tiger::TempLabel::NewNamedTemp("c"),tiger::TempList::kTempList_Rear);
    src->Insert(tiger::TempLabel::NewNamedTemp("b"),tiger::TempList::kTempList_Rear);
    instr = new tiger::InstrOper("add d0',s0',s1'",dst,src,0);
    il->Insert(instr,tiger::InstrList::kInstrList_Rear);
    
    dst = new tiger::TempList;
    src = new tiger::TempList;
    dst->Insert(tiger::TempLabel::NewNamedTemp("a"),tiger::TempList::kTempList_Rear);
    src->Insert(tiger::TempLabel::NewNamedTemp("b"),tiger::TempList::kTempList_Rear);
    instr = new tiger::InstrOper("add d0',s0',2",dst,src,0);
    il->Insert(instr,tiger::InstrList::kInstrList_Rear);
    
    dst = new tiger::TempList;
    src = new tiger::TempList;
    tiger::LabelList* ll = new tiger::LabelList;
    ll->Insert(tiger::TempLabel::NewNamedLabel("loop"),tiger::LabelList::kLabelList_Rear);
    instr = new tiger::InstrOper("jmp loop",dst,src,ll);
    il->Insert(instr,tiger::InstrList::kInstrList_Rear);
    
    dst = new tiger::TempList;
    src = new tiger::TempList;
    src->Insert(tiger::TempLabel::NewNamedTemp("c"),tiger::TempList::kTempList_Rear);
    instr = new tiger::InstrOper("inc s0",dst,src,0);
    il->Insert(instr,tiger::InstrList::kInstrList_Rear);
    
    tiger::FlowGraph* fg = new tiger::FlowGraph;
    tiger::Graph* g = fg->AssemFlowGraph(il);
    tiger::Liveness* ln = new tiger::Liveness;
    ln->LivenessCalc(g);
    
    tiger::TempLabel::Exit();
}
#endif
void test_llvm()
{
    tiger::Exp* exp;
    tiger::SymTab venv,tenv;
    

        
    //tiger::scanner::FileSourceCodeStream stream((char*)"a.txt");
    //tiger::scanner::FileSourceCodeStream stream((char*)"b.txt");
    tiger::scanner::StringSourceCodeStream stream((char*)"let var i:=0 in while i<10 do (printint(i);i:=i+1) end");
    
    /* generate sbstract syntax tree*/
    tiger::parser::Parser parser(&stream);
    parser.Parse(&exp);
    tiger::IRGen* ir_gen;
    ir_gen = new tiger::IRGen;
    tenv.Enter(tenv.MakeSymbolFromString("int"),new tiger::EnvEntryVarLLVM(new tiger::TypeInt(),tiger::EnvEntryVarLLVM::kEnvEntryVarLLVM_For_Type, llvm::Type::getInt32Ty( *(ir_gen->GetContext()->C()) ), 0));

    /*
    printint(x:int)
    */
    tiger::TypeFieldNode* node;
    node = new tiger::TypeFieldNode;
    tiger::EnvEntryFunLLVM* ef;
    node->m_field = new tiger::TypeField(tenv.MakeSymbolFromString("x"),tenv.Type(tenv.MakeSymbolFromString("int")));
    ef = new tiger::EnvEntryFunLLVM(new tiger::TypeFieldList(node),0,ir_gen->OutmostLevel()/*level*/,tiger::TempLabel::NewNamedLabel("printint"),1);
    venv.Enter(venv.MakeSymbolFromString("printint"),ef);
    llvm::Type* parms[]={
        llvm::Type::getInt32Ty(*(tiger::IRGenContext::Get()->C()))
    };
    llvm::FunctionType* ft = llvm::FunctionType::get(llvm::Type::getVoidTy( *(tiger::IRGenContext::Get()->C())),llvm::makeArrayRef<llvm::Type*>(parms),false/*var args flag*/);
    llvm::Function*     f = llvm::Function::Create(ft,llvm::Function::ExternalLinkage,"printint",tiger::IRGenContext::Get()->M());
    ef->SetFun(f);
        
    ir_gen->Gen(&venv,&tenv,exp);
    ir_gen->Dump();
    delete ir_gen;
    delete exp;
}
int main()
{
    //test_Next_With_StringSourceCodeStream();
    //test_sbsyn();
    //test_parser();
    //test_Logger();
    //test_assert();
    //test_types();
    //test_symtab();
    //test_escape();
    //test_tree();
    //test_litstringlist();
    //test_typecheck();
    //test_tree_gen();
    //test_canon();
    //test_liveness();
    test_llvm();
    return 0;
}
