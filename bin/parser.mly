%{
open Ast
open Lexing

let loc (startpos:Lexing.position) (endpos:Lexing.position) (elt:'a) : 'a node =
  { elt ; loc=Range.mk_lex_range startpos endpos }

%}

/* Declare your tokens here. */
%token EOF
%token <int64>  INT
%token NULL
%token <string> STRING
%token <string> IDENT

%token TINT     /* int */
%token TBOOL     /* bool */
%token TVOID    /* void */
%token TSTRING  /* string */
%token NEW     /* new */
%token IF       /* if */
%token ELSE     /* else */
%token WHILE    /* while */
%token FOR    /* for */
%token RETURN   /* return */
%token VAR      /* var */
%token TRUE       /* true */
%token FALSE       /* false */
%token SEMI     /* ; */
%token COMMA    /* , */
%token LBRACE   /* { */
%token RBRACE   /* } */
%token PLUS     /* + */
%token DASH     /* - */
%token STAR     /* * */
%token EQEQ     /* == */
%token EQ       /* = */
%token LPAREN   /* ( */
%token RPAREN   /* ) */
%token LBRACKET /* [ */
%token RBRACKET /* ] */
%token TILDE    /* ~ */
%token BANG     /* ! */
%token GLOBAL   /* global */
%token GT   /* > */
%token GE   /* >= */
%token LT   /* < */
%token LE   /* <= */
%token AND   /* & */
%token OR   /* | */
%token SHL   /* << */
%token SHR   /* >> */
%token SAR   /* >>> */
%token NEQ   /* != */
%token BAND   /* [&] */
%token BOR   /* [|] */

%left BOR
%left BAND
%left OR
%left AND 
%left EQEQ NEQ
%left GT LT GE LE
%left SHL SHR SAR
%left PLUS DASH
%left STAR
%nonassoc BANG
%nonassoc TILDE
%nonassoc LBRACKET

/* ---------------------------------------------------------------------- */

%start prog
%start exp_top
%start stmt_top
%type <Ast.exp Ast.node> exp_top
%type <Ast.stmt Ast.node> stmt_top

%type <Ast.prog> prog
%type <Ast.exp Ast.node> exp
%type <Ast.stmt Ast.node> stmt
%type <Ast.block> block
%type <Ast.ty> ty
%%

exp_top:
  | e=exp EOF { e }

stmt_top:
  | s=stmt EOF { s }

prog:
  | p=list(decl) EOF  { p }

decl:
  | GLOBAL name=IDENT EQ init=gexp SEMI
    { Gvdecl (loc $startpos $endpos { name; init }) }
  | frtyp=ret_ty fname=IDENT LPAREN args=arglist RPAREN body=block
    { Gfdecl (loc $startpos $endpos { frtyp; fname; args; body }) }

arglist:
  | l=separated_list(COMMA, pair(ty,IDENT)) { l }
    
ty:
  | TINT   { TInt }
  | TBOOL  { TBool }
  | r=rtyp { TRef r } 
  | LPAREN t=ty RPAREN { t }


%inline ret_ty:
  | TVOID  { RetVoid }
  | t=ty   { RetVal t }

%inline rtyp:
  | TSTRING { RString }
  | t=ty LBRACKET RBRACKET { RArray t }

%inline bop:
  | STAR   { Mul }
  | PLUS   { Add }
  | DASH   { Sub }
  | SHL    { Shl }
  | SHR    { Shr }
  | SAR    { Sar }
  | LT     { Lt }
  | LE     { Lte }
  | GT     { Gt}
  | GE     { Gte }
  | EQEQ   { Eq } 
  | NEQ    { Neq }
  | AND    { And }
  | OR     { Or }
  | BAND   { IAnd }
  | BOR    { IOr }

%inline uop:
  | DASH  { Neg }
  | BANG  { Lognot }
  | TILDE { Bitnot }

gexp:
  | i=INT      { loc $startpos $endpos @@ CInt i } 
  | s=STRING      { loc $startpos $endpos @@ CStr s } 
  | t=rtyp NULL  { loc $startpos $endpos @@ CNull t }
  | b=TRUE               { loc $startpos $endpos @@ CBool true }
  | b=FALSE               { loc $startpos $endpos @@ CBool false }
  | NEW t=ty LBRACKET RBRACKET LBRACE es=separated_list(COMMA, exp) RBRACE
                        { loc $startpos $endpos @@ CArr (t, es) }


lhs:  
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }

exp:
  | id=IDENT            { loc $startpos $endpos @@ Lhs(loc $startpos $endpos @@ Id id) }
  | i=INT               { loc $startpos $endpos @@ CInt i }
  | s=STRING               { loc $startpos $endpos @@ CStr s }
  | t=rtyp NULL           { loc $startpos $endpos @@ CNull t }
  | b=TRUE               { loc $startpos $endpos @@ CBool true }
  | b=FALSE               { loc $startpos $endpos @@ CBool false }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Lhs (loc $startpos $endpos @@ Index(e, i)) }
  | id=IDENT LPAREN es=separated_list(COMMA, exp) RPAREN
                        { loc $startpos $endpos @@ Call (id,es) }
  | NEW t=ty LBRACKET RBRACKET LBRACE es=separated_list(COMMA, exp) RBRACE
                        { loc $startpos $endpos @@ CArr (t, es) }
  | NEW t=ty LBRACKET e=exp RBRACKET 
                        { loc $startpos $endpos @@ NewArr (t, e) }
  | e1=exp b=bop e2=exp { loc $startpos $endpos @@ Bop (b, e1, e2) }
  | u=uop e=exp         { loc $startpos $endpos @@ Uop (u, e) }
  | LPAREN e=exp RPAREN { e } 

vdecl:
  | VAR id=IDENT EQ init=exp { (id, init) }

stmt: 
  | p=lhs EQ e=exp SEMI { loc $startpos $endpos @@ Assn(p,e) }
  | d=vdecl SEMI        { loc $startpos $endpos @@ Decl(d) }
  | RETURN e=exp SEMI   { loc $startpos $endpos @@ Ret(Some e) }
  | RETURN SEMI         { loc $startpos $endpos @@ Ret(None) }
  | id=IDENT LPAREN es=separated_list(COMMA, exp) RPAREN SEMI
                        { loc $startpos $endpos @@ SCall (id, es) }
  | ifs=if_stmt         { ifs }
  | FOR LPAREN vs=separated_list(COMMA, vdecl) SEMI e=option(exp) SEMI s=option(stmt) RPAREN b=block
                        { loc $startpos $endpos @@ For(vs, e, s, b) } 
  | WHILE LPAREN e=exp RPAREN b=block  
                        { loc $startpos $endpos @@ While(e, b) } 

block:
  | LBRACE stmts=list(stmt) RBRACE { stmts }

if_stmt:
  | IF LPAREN e=exp RPAREN b1=block b2=else_stmt
    { loc $startpos $endpos @@ If(e,b1,b2) }

else_stmt:
  | (* empty *)       { [] }
  | ELSE b=block      { b }
  | ELSE ifs=if_stmt  { [ ifs ] }
