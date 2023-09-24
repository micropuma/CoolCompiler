/*
 *  The scanner definition for COOL.
 */

/*
 *  Stuff enclosed in %{ %} in the first section is copied verbatim to the
 *  output, so headers and global definitions are placed here to be visible
 * to the code in the file.  Don't remove anything that was here initially
 */
%{
#include <cool-parse.h>
#include <stringtab.h>
#include <utilities.h>
#include <stdio.h>
#include <vector>

/* The compiler assumes these identifiers. */
#define yylval cool_yylval
#define yylex  cool_yylex

/* Max size of string constants */
#define MAX_STR_CONST 1025
#define YY_NO_UNPUT   /* keep g++ happy */

extern FILE *fin; /* we read from this file */

/* define YY_INPUT so we read from the FILE fin:
 * This change makes it possible to use this scanner in
 * the Cool compiler.
 */
#undef YY_INPUT
#define YY_INPUT(buf,result,max_size) \
	if ( (result = fread( (char*)buf, sizeof(char), max_size, fin)) < 0) \
		YY_FATAL_ERROR( "read() in flex scanner failed");

char string_buf[MAX_STR_CONST]; /* to assemble string constants */
char *string_buf_ptr;

extern int curr_lineno;
extern int verbose_flag;

extern YYSTYPE cool_yylval;

static std::vector<char> stringBuf;
static int nest_depth = 0;

%}
/*
 * Define names for regular expressions here.
 */

%option noyywrap

DARROW          =>
DIGIT           [0-9]
%Start          COMMENT
%Start          INLINE_COMMENT
%Start          STRING  
%Start          STRING_ESCAPE
%Start          STRING_ERROR

ASSIGN          <-
LE              <=

%%

 /* ignore all blank, or tab etc.  
  * trickey here:  
  * don't ignore the left blank, otherwise won't deal with blank situation.
  */
[ \r\t\v\f]+    {  }

 /*
  *  Nested comments
  */

<INITIAL,COMMENT,INLINE_COMMENT>"(*" {
    nest_depth++;
    BEGIN(COMMENT);
}

<COMMENT>"*)" {
    nest_depth--;
    if(nest_depth == 0)
        BEGIN(INITIAL);
}

<COMMENT>[^\n(*]* { }

<COMMENT>[()*] { }

"*)" {
    cool_yylval.error_msg = "Unmatched *)";
    BEGIN(INITIAL);
    return ERROR;
}

<COMMENT><<EOF>> {
    cool_yylval.error_msg = "EOF in comment";
    BEGIN(INITIAL);
    return ERROR;
}

<INITIAL>"--" {
    BEGIN(INLINE_COMMENT);
}

<INLINE_COMMENT>"\n" {
    curr_lineno++;
    BEGIN(INITIAL);
}

<INLINE_COMMENT>[^\n]* { }

 /*
  * String const handling.
  */
 /* encounter the first " when in INITIAL state */

 /* Specifically judge whether is single '\0' sign */
<INITIAL>[\"][\\][0][\"] {
    stringBuf.clear();
    stringBuf.insert(stringBuf.end(), '\0');
    cool_yylval.symbol = stringtable.add_string(&stringBuf[0], stringBuf.size());
    return STR_CONST;
}

<INITIAL>"\"" {
    stringBuf.clear();
    BEGIN(STRING);
}

 /* encounter the " when in STRING state, without meeting \\*/
<STRING>[^\"\\]*\" {
    stringBuf.insert(stringBuf.end(), yytext, yytext + yyleng-1);
    cool_yylval.symbol = stringtable.add_string(&stringBuf[0], stringBuf.size());
    BEGIN(INITIAL);
    return STR_CONST;
}

 /* encounter \\ */
 <STRING>[^\"\\]*\\ {
    stringBuf.insert(stringBuf.end(), yytext, yytext + yyleng - 1);
    BEGIN(STRING_ESCAPE);
 }

 <STRING>. {
    stringBuf.push_back(yytext[0]);
    BEGIN(STRING);
 }

 /* need to explictly handle '\\n' and '\n' */
 <STRING_ESCAPE>n {
    stringBuf.push_back('\n');
    BEGIN(STRING);
 }

 <STRING_ESCAPE>\n {
    curr_lineno++;
    stringBuf.push_back('\n');
    BEGIN(STRING);
 }

 <STRING_ESCAPE>b {
    stringBuf.push_back('\b');
    BEGIN(STRING);
 }

 <STRING_ESCAPE>t {
    stringBuf.push_back('\t');
    BEGIN(STRING);
 }

 <STRING_ESCAPE>f {
    stringBuf.push_back('\f');
    BEGIN(STRING);
 }

 <STRING_ESCAPE>0 {
    //printf("arrvied here!\n");
    cool_yylval.error_msg = "Null pointer in string constant";
    BEGIN(STRING_ERROR);
    stringBuf.clear();
    return ERROR;
 }

 <STRING_ESCAPE>. {
    stringBuf.push_back(yytext[0]);
    // printf("arrived here, and yytext is %c\n", yytext[0]);
    BEGIN(STRING);
 }
 
 /*
  * Error_handling for string const.
  */
 
 /* A string may not contain EOF */
 <STRING_ESCAPE><<EOF>> {
    cool_yylval.error_msg = "EOF in string constant";
    BEGIN(STRING);
    return ERROR;
 }

 <STRING><<EOF>> {
    cool_yylval.error_msg = "EOF in string constant";
    BEGIN(INITIAL);
    return ERROR;
 }

 /* without STRING_ESCAPE and also without STIRNG_TERMINATION 
  * need to report error! 
  */
 
 <STRING>[^\\\"]*$ {
    cool_yylval.error_msg = "Unterminated String constant";
    curr_lineno++;
    BEGIN(STRING_ERROR);
    stringBuf.insert(stringBuf.end(), yytext, yytext + yyleng);
    for(const char i : stringBuf)
        cout << stringBuf[i] << " ";
    cout << endl;
    return ERROR;
 }

 /* a new state specifically for STRING_ERROR handling! */
 <STRING_ERROR>[\"\n] {
    BEGIN(INITIAL);
 }

 <STRING_ERROR>. {

 }

 /*
  *  The multiple-character operators.
  */

<INITIAL>{DARROW}		    { return (DARROW); }
<INITIAL>(?i:CLASS)         { return (CLASS); }           
<INITIAL>(?i:FI)            { return (FI); }
<INITIAL>(?i:IF)            { return (IF); }
<INITIAL>(?i:IN)            { return (IN); }
<INITIAL>(?i:INHERITS)      { return (INHERITS); }  
<INITIAL>(?i:LET)           { return (LET); }
<INITIAL>(?i:LOOP)          { return (LOOP); }  
<INITIAL>(?i:POOL)          { return (POOL); } 
<INITIAL>(?i:THEN)          { return (THEN); }  
<INITIAL>(?i:WHILE)         { return (WHILE); }  
<INITIAL>(?i:CASE)          { return (CASE); }  
<INITIAL>(?i:ESAC)          { return (ESAC); }  
<INITIAL>(?i:OF)            { return (OF); }  
<INITIAL>(?i:NEW)           { return (NEW); }  
<INITIAL>(?i:ISVOID)        { return (ISVOID); }
<INITIAL>{ASSIGN}           { return (ASSIGN); }
<INITIAL>(?i:NOT)           { return (NOT); }
<INITIAL>{LE}               { return (LE); }
<INITIAL>(?i:ELSE)          { return (ELSE); }

[\[\]\'>] {
    cool_yylval.error_msg = yytext;
    return (ERROR);
}

","             {
    return int(',');
}

";" {
    return int(';');
}

":" {
    return int(':');
}

"+" {
    return int('+');
}

"-" {
    return int('-');
}

"*" {
    return int('*');
}

"'" {
    return int('\'');
}

"." {
    return int('.');
}

"/" {
    return int('/');
}

"=" {
    return int('=');
}

"{" {
    return int('{');
}

"}" {
    return int('}');
}

"(" {
    return int('(');
}

")" {
    return int(')');
}

"<" {
    return int('<');
}

 /* new line count */
"\n" {
    curr_lineno ++;          
}

"~" {
    return int('~');
}

"@" {
    return int('@');
}

 /*
  * Keywords are case-insensitive except for the values true and false,
  * which must begin with a lower-case letter.
  */

  /* BOOL_CONST */
t[Rr][Uu][Ee] {  
    cool_yylval.boolean = true;
    return BOOL_CONST;
}

f[Aa][Ll][Ss][Ee] {
    cool_yylval.boolean = false;
    return BOOL_CONST;
}
 

 /* DIGIT recognition */
<INITIAL>{DIGIT}+ {      
    cool_yylval.symbol = inttable.add_string(yytext);
    return INT_CONST;
}

 /* OBJECT recognition */
<INITIAL>[a-z][A-Za-z0-9_]* {          
    cool_yylval.symbol = idtable.add_string(yytext);
    return OBJECTID;
}

 /* TYPEID recognition */
<INITIAL>[A-Z][A-Za-z0-9_]* {
    cool_yylval.symbol = idtable.add_string(yytext);
    // printf("%s\n", yytext);
    return TYPEID;
}

 /*
  * error handling
  */
  <INITIAL>[^\n] {
    cool_yylval.error_msg = yytext;
    //printf("arrived here!\n");
    return ERROR;
  }
%%


