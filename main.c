#include <iostream>

#include "scanner.h"
#include "absyn.h"
#include "parser.h"
#include "tiger_log.h"
#include "tiger_assert.h"
#include "types.h"

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
    symtab.BeginScope();
    symtab.Enter(symtab.MakeSymbol(new tiger::Symbol("a")),0);
    symtab.Enter(symtab.MakeSymbol(new tiger::Symbol("b")),0);
    symtab.EndScope();
    std::cout<<"-----"<<std::endl;

}
int main()
{
    //test_Next_With_StringSourceCodeStream();
    //test_sbsyn();
    //test_parser();
    //test_Logger();
    //test_assert();
    //test_types();
    test_symtab();
    return 0;
}
