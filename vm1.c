#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <unistd.h>
#include <errno.h>
#include <locale.h>

// 全局常量定义
#define MAX_TOKEN_LEN 100
#define MAX_ERRORS 100
#define MAX_LINE_LEN 1024
#define MAX_FILENAME 256
#define INIT_TOKEN_CAPACITY 100
#define MAX_SYMBOL 500    //符号表最大容量(PPT)
#define MAX_SCOPE 30      //新增：作用域最大层数
#define MAX_CODE 1000     //中间代码最大条数(PPT Code结构体)

// Token类型枚举:定义仓颉语言所有单词类型
typedef enum {
    TOKEN_EOF, TOKEN_ERROR,
    // 关键字
    TOKEN_AS, TOKEN_BREAK, TOKEN_CASE, TOKEN_CONST, TOKEN_CONTINUE,
    TOKEN_DEFAULT, TOKEN_DO, TOKEN_ELSE, TOKEN_FOR, TOKEN_FROM, TOKEN_FUNC,
    TOKEN_IF, TOKEN_IN, TOKEN_LET, TOKEN_MAIN, TOKEN_MATCH, TOKEN_SWITCH,
    TOKEN_VAR, TOKEN_WHERE, TOKEN_WHILE, TOKEN_READ, TOKEN_WRITE,
    TOKEN_RETURN,
    // 标识符和字面量
    TOKEN_ID, TOKEN_NUM, TOKEN_STRING,
    // 运算符
    TOKEN_PLUS, TOKEN_MINUS, TOKEN_MUL, TOKEN_DIV,
    TOKEN_ASSIGN, TOKEN_EQ, TOKEN_NE, TOKEN_GT, TOKEN_LT,
    TOKEN_GE, TOKEN_LE,
    // 界符
    TOKEN_LPAREN, TOKEN_RPAREN, TOKEN_LBRACE, TOKEN_RBRACE,
    TOKEN_LBRACKET, TOKEN_RBRACKET, TOKEN_SEMICOLON, TOKEN_COLON,
    TOKEN_COMMA, TOKEN_DOT, TOKEN_DOTDOT, TOKEN_DOTDOTEQ
} TokenType;

// Token结构体
typedef struct {
    TokenType type;//单词类型
    char value[MAX_TOKEN_LEN];//单词值
    int line;
    int column;
} Token;

// 存储所有Token的动态数组（用于词法分析结果传递给语法分析）
typedef struct {
    Token *data;
    int count;
    int capacity;
} TokenList;

// 错误信息结构体
typedef struct {
    char message[256];
    int line;
    int column;
} Error;

// AST节点类型枚举
typedef enum {
    AST_PROGRAM, AST_FUN_DECL, AST_MAIN_DECL, AST_FUN_BODY,
    AST_VAR_DECL, AST_IF_STMT, AST_WHILE_STMT, AST_DO_WHILE_STMT,
    AST_FOR_STMT, AST_SWITCH_STMT, AST_CASE_STMT, AST_DEFAULT_STMT,
    AST_COMPOUND_STMT, AST_EXPR_STMT, AST_ASSIGN_EXPR,
    AST_BINARY_EXPR, AST_IDENTIFIER, AST_NUM_LITERAL, AST_STRING_LITERAL,
    AST_READ_STMT, AST_WRITE_STMT, AST_BREAK_STMT, AST_CONTINUE_STMT,
    AST_FUNC_CALL, AST_RETURN_STMT, AST_ARRAY_DECL, AST_ARRAY_ACCESS
} ASTNodeType;

// AST节点结构体
typedef struct ASTNode {
    ASTNodeType type;
    char *value;
    int line;
    int column;
    struct ASTNode **children;// 子节点(动态数组
    int child_count;// 数组中已有的子节点数量
    int child_capacity;// 数组总容量
} ASTNode;

/**********************【扩展：完整语义分析符号表】**********************/
// 数据类型枚举
typedef enum {
    TYPE_INT, TYPE_STRING, TYPE_BOOL, TYPE_VOID, TYPE_ERROR
} Type;

//符号种类
typedef enum {
    SYM_VARIABLE, SYM_FUNCTION
} Category_symbol;

// 函数参数结构体
typedef struct {
    char name[20];
    Type type;
} FuncParam;

//符号表项结构体(扩展支持函数)
typedef struct {
    char name[20];
    Category_symbol kind;
    int address;    //变量相对偏移地址，从2开始
    Type type;       // 变量类型或函数返回类型
    int dim;         // 数组维数，0表示非数组
    int len[10];     // 各维长度，最多支持10维
    // 函数相关字段
    int param_count;      // 参数个数
    FuncParam params[10]; // 参数列表
    int local_count;      // 局部变量数量（用于ENTER指令）
    int is_global;        // 是否为全局变量（0=局部，1=全局）
} SymbolItem;

// 作用域栈
typedef struct {
    SymbolItem items[MAX_SYMBOL];
    int cnt;
    int base_off;
} Scope;

Scope scope_stack[MAX_SCOPE];
int scope_top = -1;
int global_off = 500;  // 全局变量从高地址500开始

// 控制流状态（用于检测break/continue位置错误）
int loop_nest_level = 0;  // 循环嵌套层级
int in_switch = 0;        // 是否在switch中

// 当前正在处理的函数（用于统计局部变量数量）
SymbolItem *current_fun = NULL;

// 类型名称映射
const char* type_names[] = {"int", "string", "bool", "void", "error"};

/**********************【新增：PPT中间代码结构体 栈汇编指令】**********************/
//中间代码结构体（PPT Code）
typedef struct {
    char opt[10];       //指令：LOAD/LOADI/STO/ADD/SUB/MULT/DIV/IN/OUT/BR/BRF/GT...
    int operand;        //操作数：变量地址/跳转标号
} Code;

Code codes[MAX_CODE];
int codesIndex = 0;     //下一条代码存储下标(PPT codesIndex)

/**********************【新增：语义全局标记】**********************/
static int semantic_err = 0;    //语义错误计数

// 函数前置声明：解决add_error隐式定义编译报错
static void add_error(const char *message, int line, int column);

// 全局变量
static FILE *source_file;// 源文件指针
static int current_line = 1;// 当前扫描行号
static int current_column = 1;// 当前扫描列号
static char current_char;// 当前读取的字符
static TokenList token_list;// 全部Token
static int current_token_index = 0;// 语法分析当前Token位置
static Error errors[MAX_ERRORS];// 错误列表
static int error_count = 0;// 错误数量

// 关键字表：判断标识符是不是关键字
static const struct {
    const char *name;
    TokenType type;
} keywords[] = {
    {"as", TOKEN_AS}, {"break", TOKEN_BREAK}, {"case", TOKEN_CASE},
    {"const", TOKEN_CONST}, {"continue", TOKEN_CONTINUE}, {"default", TOKEN_DEFAULT},
    {"do", TOKEN_DO}, {"else", TOKEN_ELSE}, {"for", TOKEN_FOR}, 
    {"from", TOKEN_FROM}, {"func", TOKEN_FUNC}, {"if", TOKEN_IF}, 
    {"in", TOKEN_IN}, {"let", TOKEN_LET}, {"main", TOKEN_MAIN}, 
    {"match", TOKEN_MATCH}, {"switch", TOKEN_SWITCH}, {"var", TOKEN_VAR},
    {"where", TOKEN_WHERE}, {"while", TOKEN_WHILE},
    {"read", TOKEN_READ}, {"write", TOKEN_WRITE}, {"return", TOKEN_RETURN},
    {"int", TOKEN_ID}, {"string", TOKEN_ID}, {"bool", TOKEN_ID},
    {"and", TOKEN_ID}, {"or", TOKEN_ID},
    {NULL, TOKEN_EOF}
};

// 工具函数
// 生成文件名
char* generate_unique_filename(const char *base, const char *suffix) {
    char *filename = malloc(MAX_FILENAME);
    if (!filename) {
        perror("内存分配失败");
        exit(EXIT_FAILURE);
    }

    int counter = 0;
    snprintf(filename, MAX_FILENAME, "%s%s", base, suffix);

    // 检查文件是否存在，存在则添加序号
    while (access(filename, F_OK) == 0) {
        counter++;
        snprintf(filename, MAX_FILENAME, "%s_%d%s", base, counter, suffix);
    }

    return filename;
}

// 初始化Token列表
void init_token_list(TokenList *list) {
    list->data = malloc(INIT_TOKEN_CAPACITY * sizeof(Token));
    if (!list->data) {
        perror("Token列表内存分配失败");
        exit(EXIT_FAILURE);
    }
    list->count = 0;
    list->capacity = INIT_TOKEN_CAPACITY;
}

// 添加Token到列表
void add_token(TokenList *list, Token token) {
    if (list->count >= list->capacity) {
        list->capacity *= 2;
        list->data = realloc(list->data, list->capacity * sizeof(Token));
        if (!list->data) {
            perror("Token列表扩容失败");
            exit(EXIT_FAILURE);
        }
    }
    list->data[list->count++] = token;
}

// 释放Token列表
void free_token_list(TokenList *list) {
    free(list->data);
    list->data = NULL;
    list->count = list->capacity = 0;
}

// 创建AST节点
ASTNode* create_ast_node(ASTNodeType type, const char *value, int line, int column) {
    ASTNode *node = malloc(sizeof(ASTNode));
    if (!node) {
        perror("AST节点内存分配失败");
        exit(EXIT_FAILURE);
    }

    node->type = type;
    node->line = line;
    node->column = column;
    node->child_count = 0;
    node->child_capacity = 4;
    node->children = malloc(node->child_capacity * sizeof(ASTNode*));
    if (!node->children) {
        perror("AST子节点数组分配失败");
        free(node);
        exit(EXIT_FAILURE);
    }

    if (value) {
        node->value = strdup(value);
        if (!node->value) {
            perror("AST节点值复制失败");
            free(node->children);
            free(node);
            exit(EXIT_FAILURE);
        }
    } else {
        node->value = NULL;
    }

    return node;
}

// 添加子节点到AST
void add_ast_child(ASTNode *parent, ASTNode *child) {
    if (!parent || !child) return;

    if (parent->child_count >= parent->child_capacity) {
        parent->child_capacity *= 2;
        parent->children = realloc(parent->children, parent->child_capacity * sizeof(ASTNode*));
        if (!parent->children) {
            perror("AST子节点数组扩容失败");
            exit(EXIT_FAILURE);
        }
    }
    parent->children[parent->child_count++] = child;
}

// 释放AST内存
void free_ast(ASTNode *node) {
    if (!node) return;

    for (int i = 0; i < node->child_count; i++) {
        free_ast(node->children[i]);
    }
    free(node->children);
    free(node->value);
    free(node);
}

/**********************【修复：作用域操作函数】**********************/
void scope_enter() {
    scope_top++;
    scope_stack[scope_top].cnt = 0;
    scope_stack[scope_top].base_off = global_off;
}

void scope_leave() {
    global_off = scope_stack[scope_top].base_off;
    scope_top--;
}

/**********************【扩展：完整符号表操作函数】**********************/
// 字符串转类型
Type string_to_type(const char *type_str) {
    if (!strcmp(type_str, "int")) return TYPE_INT;
    if (!strcmp(type_str, "string")) return TYPE_STRING;
    if (!strcmp(type_str, "bool")) return TYPE_BOOL;
    if (!strcmp(type_str, "void")) return TYPE_VOID;
    return TYPE_ERROR;
}

// 查找符号：从内到外查找，返回符号项指针
SymbolItem* lookup_symbol(char *name, int line, int report_error) {
    for (int s = scope_top; s >= 0; s--) {
        Scope *sc = &scope_stack[s];
        for (int i = 0; i < sc->cnt; i++) {
            if (!strcmp(sc->items[i].name, name)) {
                return &sc->items[i];
            }
        }
    }
    //未定义标识符，语义报错
    if (report_error) {
        char msg[256];
        sprintf(msg,"语义错误：标识符%s未定义",name);
        add_error(msg,line,1);
        semantic_err++;
    }
    return NULL;
}

// 查找符号地址（保持兼容旧代码）
int lookup(char *name, int line) {
    SymbolItem *item = lookup_symbol(name, line, 0);
    return item ? item->address : -1;
}

//插入变量符号到符号表
void insert_symbol(Category_symbol kind, char *name, Type type, int line, int check_errors) {
    if (scope_top < 0) {
        add_error("内部错误：未初始化作用域", line, 1);
        return;
    }
    
    // 只有在语义分析阶段才进行错误检测
    if (check_errors) {
        // 如果是函数，在所有作用域中检查重复定义
        if (kind == SYM_FUNCTION) {
            for (int s = 0; s <= scope_top; s++) {
                Scope *scope = &scope_stack[s];
                for (int i = 0; i < scope->cnt; i++) {
                    if (!strcmp(scope->items[i].name, name) && scope->items[i].kind == SYM_FUNCTION) {
                        char msg[256];
                        sprintf(msg,"语义错误：函数%s重复定义",name);
                        add_error(msg,line,1);
                        semantic_err++;
                        return;
                    }
                }
            }
        } else {
            // 如果是变量，只检查当前作用域重复定义
            Scope *sc = &scope_stack[scope_top];
            for (int i = 0; i < sc->cnt; i++) {
                if (!strcmp(sc->items[i].name, name)) {
                    char msg[256];
                    sprintf(msg,"语义错误：标识符%s重复定义",name);
                    add_error(msg,line,1);
                    semantic_err++;
                    return;
                }
            }
        }
    }
    
    //写入符号表
    Scope *sc = &scope_stack[scope_top];
    strcpy(sc->items[sc->cnt].name, name);
    sc->items[sc->cnt].kind = kind;
    sc->items[sc->cnt].type = type;
    sc->items[sc->cnt].dim = 0;        // 初始化数组维数为0（非数组）
    memset(sc->items[sc->cnt].len, 0, sizeof(sc->items[sc->cnt].len));  // 初始化各维长度为0
    sc->items[sc->cnt].param_count = 0;
    sc->items[sc->cnt].local_count = 0;  // 初始化局部变量数量为0
    sc->items[sc->cnt].is_global = (scope_top == 0) ? 1 : 0;  // 判断是否为全局变量
    if (kind == SYM_VARIABLE) {
        if (scope_top == 0) {
            // 全局变量：使用低地址空间（从0开始）
            sc->items[sc->cnt].address = global_off;
            global_off++;
        } else {
            // 局部变量：使用正数地址（从0开始，相对于base）
            sc->items[sc->cnt].address = global_off;
            global_off++;
            // 如果是在函数作用域内，增加当前函数的局部变量计数
            if (current_fun != NULL) {
                current_fun->local_count++;
            }
        }
    } else {
        sc->items[sc->cnt].address = 0;
    }
    sc->cnt++;
}

// 插入函数符号到符号表
void insert_function(char *name, Type return_type, FuncParam *params, int param_count, int line) {
    if (scope_top < 0) {
        add_error("内部错误：未初始化作用域", line, 1);
        return;
    }
    
    Scope *sc = &scope_stack[scope_top];
    //查重：全局作用域函数重复定义报错
    for (int s = 0; s <= scope_top; s++) {
        Scope *scope = &scope_stack[s];
        for (int i = 0; i < scope->cnt; i++) {
            if (!strcmp(scope->items[i].name, name) && scope->items[i].kind == SYM_FUNCTION) {
                char msg[256];
                sprintf(msg,"语义错误：函数%s重复定义",name);
                add_error(msg,line,1);
                semantic_err++;
                return;
            }
        }
    }
    //写入符号表
    strcpy(sc->items[sc->cnt].name, name);
    sc->items[sc->cnt].kind = SYM_FUNCTION;
    sc->items[sc->cnt].type = return_type;
    sc->items[sc->cnt].dim = 0;        // 函数不是数组，维数为0
    memset(sc->items[sc->cnt].len, 0, sizeof(sc->items[sc->cnt].len));  // 初始化各维长度为0
    sc->items[sc->cnt].param_count = param_count;
    sc->items[sc->cnt].address = codesIndex; // 保存函数入口地址
    for (int i = 0; i < param_count && i < 10; i++) {
        strcpy(sc->items[sc->cnt].params[i].name, params[i].name);
        sc->items[sc->cnt].params[i].type = params[i].type;
    }
    sc->cnt++;
}

// 检查函数调用参数匹配
int check_function_call(char *func_name, ASTNode **args, int arg_count, int line) {
    SymbolItem *func = lookup_symbol(func_name, line, 1);
    if (!func || func->kind != SYM_FUNCTION) {
        return 0;
    }
    
    if (func->param_count != arg_count) {
        char msg[256];
        sprintf(msg,"语义错误：函数%s参数数量不匹配，期望%d个参数，实际%d个",
                func_name, func->param_count, arg_count);
        add_error(msg, line, 1);
        semantic_err++;
        return 0;
    }
    
    // 参数类型检查（需要类型推断）
    return 1;
}

// 类型不匹配检查
void check_type_match(Type expected, Type actual, const char *context, int line) {
    if (expected != actual && expected != TYPE_ERROR && actual != TYPE_ERROR) {
        char msg[256];
        sprintf(msg,"语义错误：类型不匹配，%s期望%s类型，实际%s类型",
                context, type_names[expected], type_names[actual]);
        add_error(msg, line, 1);
        semantic_err++;
    }
}

// 类型转换错误检查
void check_type_conversion(Type from, Type to, int line) {
    if (from != to) {
        if ((from == TYPE_INT && to == TYPE_VOID) || (from == TYPE_VOID && to == TYPE_INT)) {
            char msg[256];
            sprintf(msg,"语义错误：无法将%s类型转换为%s类型",
                    type_names[from], type_names[to]);
            add_error(msg, line, 1);
            semantic_err++;
        }
    }
}

/**********************【中间代码生成工具】添加一条汇编指令(PPT)】**********************/
void gen_code(char *op, int opr) {
    strcpy(codes[codesIndex].opt,op);
    codes[codesIndex].operand = opr;
    codesIndex++;
}

/**********************【语义遍历AST生成中间代码 递归翻译】**********************/
Type infer_type(ASTNode *node);
void semantic_translate(ASTNode *node);

//翻译赋值语句：id=expr
void trans_assign(ASTNode *node) {
    //左操作数变量
    ASTNode *idnode = node->children[0];
    ASTNode *exprnode = node->children[1];
    
    // 检查是否是数组元素赋值
    if (idnode->type == AST_ARRAY_ACCESS) {
        // 数组元素赋值：arr[index] = value
        // 先翻译表达式（值）
        semantic_translate(exprnode);
        // 再翻译数组索引
        semantic_translate(idnode->children[0]);
        // 获取数组基地址
        int base_addr = lookup(idnode->value, idnode->line);
        // STOA addr：栈顶值存入数组元素（地址 = base_addr + 索引）
        if (base_addr != -1) gen_code("STOA", base_addr);
    } else {
        // 普通变量赋值
        int pos = lookup(idnode->value, idnode->line);
        //先翻译表达式，表达式结果自动压栈
        semantic_translate(exprnode);
        //STO addr：栈顶存入变量地址(PPT STO指令)
        if(pos!=-1) gen_code("STO",pos);
    }
}

//翻译双目运算 +-*/ > < >= <= == != AND OR
void trans_binary(ASTNode *node) {
    // 类型检查：二元运算操作数类型应该一致
    Type left_type = infer_type(node->children[0]);
    Type right_type = infer_type(node->children[1]);
    
    // 逻辑运算(AND, OR)需要bool类型操作数
    char *op = node->value;
    if (strcmp(op,"&&")==0 || strcmp(op,"AND")==0 || strcmp(op,"and")==0 ||
        strcmp(op,"||")==0 || strcmp(op,"OR")==0 || strcmp(op,"or")==0) {
        if (left_type != TYPE_ERROR && left_type != TYPE_BOOL) {
            char msg[256];
            sprintf(msg,"语义错误：逻辑运算需要bool类型操作数，左操作数是%s类型", type_names[left_type]);
            add_error(msg, node->line, 1);
            semantic_err++;
        }
        if (right_type != TYPE_ERROR && right_type != TYPE_BOOL) {
            char msg[256];
            sprintf(msg,"语义错误：逻辑运算需要bool类型操作数，右操作数是%s类型", type_names[right_type]);
            add_error(msg, node->line, 1);
            semantic_err++;
        }
    } else {
        // 其他运算要求类型一致
        if (left_type != TYPE_ERROR && right_type != TYPE_ERROR && left_type != right_type) {
            char msg[256];
            sprintf(msg,"语义错误：二元运算操作数类型不匹配，左操作数%s类型，右操作数%s类型",
                    type_names[left_type], type_names[right_type]);
            add_error(msg, node->line, 1);
            semantic_err++;
        }
    }
    
    semantic_translate(node->children[0]); //左表达式入栈
    semantic_translate(node->children[1]); //右表达式入栈
    if(strcmp(op,"+")==0) gen_code("ADD",0);
    else if(strcmp(op,"-")==0) gen_code("SUB",0);
    else if(strcmp(op,"*")==0) gen_code("MULT",0);
    else if(strcmp(op,"/")==0) gen_code("DIV",0);
    else if(strcmp(op,">")==0) gen_code("GT",0);
    else if(strcmp(op,"<")==0) gen_code("LES",0);
    else if(strcmp(op,">=")==0) gen_code("GE",0);
    else if(strcmp(op,"<=")==0) gen_code("LE",0);
    else if(strcmp(op,"==")==0) gen_code("EQ",0);
    else if(strcmp(op,"!=")==0) gen_code("NOTEQ",0);
    else if(strcmp(op,"&&")==0 || strcmp(op,"AND")==0 || strcmp(op,"and")==0) gen_code("AND",0);
    else if(strcmp(op,"||")==0 || strcmp(op,"OR")==0 || strcmp(op,"or")==0) gen_code("OR",0);
}

//翻译标识符：LOAD 地址
void trans_id(ASTNode *node) {
    SymbolItem *item = lookup_symbol(node->value, node->line, 1);  // 修改为1，启用错误报告
    if(item != NULL) gen_code("LOAD", item->address);
}

//翻译数字常量：LOADI 立即数
void trans_num(ASTNode *node) {
    int val = atoi(node->value);
    gen_code("LOADI",val);
}

//翻译字符串字面量：对于字符串，我们可以使用LOADS或类似指令
//注意：在我们的栈式虚拟机中，字符串字面量的处理方式可能需要扩展
//这里先做占位，确保语义分析能正确处理
void trans_string(ASTNode *node) {
    // 对于字符串字面量，虽然我们的虚拟机主要处理整数
    // 但至少我们可以压入一个占位值（0）来避免栈不平衡
    // 在实际编译器中，这里会处理字符串常量池等
    gen_code("LOADI", 0);
}

//翻译read语句：IN + STO addr PPT示例read a -> IN STO a_addr
void trans_read(ASTNode *node) {
    ASTNode *id = node->children[0];
    int pos = lookup(id->value,id->line);
    gen_code("IN",0);
    if(pos!=-1) gen_code("STO",pos);
}

//翻译write语句：表达式+OUT PPT OUT弹出栈顶输出
void trans_write(ASTNode *node) {
    semantic_translate(node->children[0]);
    gen_code("OUT",0);
}

//翻译if语句（PPT回填BR/BRF）
void trans_if(ASTNode *node) {
    ASTNode *cond = node->children[0];
    ASTNode *stmt1 = node->children[1];
    int cx1 = codesIndex;
    semantic_translate(cond);
    int brf_pos = codesIndex;
    gen_code("BRF",0); //先占位，后续回填地址
    semantic_translate(stmt1);
    int br_pos = codesIndex;
    gen_code("BR",0);
    //回填BRF跳转地址
    codes[brf_pos].operand = codesIndex;
    //存在else
    if(node->child_count ==3){
        semantic_translate(node->children[2]);
    }
    //回填BR跳转地址
    codes[br_pos].operand = codesIndex;
}

//翻译while语句
void trans_while(ASTNode *node) {
    int lab_cond = codesIndex;
    semantic_translate(node->children[0]);
    int cx = codesIndex;
    gen_code("BRF",0);
    semantic_translate(node->children[1]);
    gen_code("BR",lab_cond);
    codes[cx].operand = codesIndex;
}

//翻译do-while语句：do { body } while(cond)
void trans_do_while(ASTNode *node) {
    int lab_body = codesIndex;
    semantic_translate(node->children[0]);
    semantic_translate(node->children[1]);
    int cx = codesIndex;
    gen_code("BRF",0);
    gen_code("BR", lab_body);
    codes[cx].operand = codesIndex;
}

//翻译switch语句
void trans_switch(ASTNode *node) {
    semantic_translate(node->children[0]);  // 计算switch表达式的值
    
    int temp_addr = scope_stack[scope_top].cnt + 1;
    gen_code("STO", temp_addr);  // 保存switch表达式值到临时位置
    
    // 第一遍：收集case和default的信息
    int case_match_addrs[100];   // 每个case比较代码的起始地址
    int case_body_addrs[100];    // 每个case body的起始地址
    int case_end_addrs[100];     // 每个case body结束后的地址（用于穿透）
    int case_has_break[100];     // 每个case是否有break
    int case_count = 0;
    int default_addr = -1;
    int default_end_addr = -1;
    int break_addrs[100];        // 真正的break指令的地址
    int break_count = 0;
    int fallthrough_addrs[100];  // 穿透BR指令的地址
    int fallthrough_count = 0;
    
    for (int i = 1; i < node->child_count; i++) {
        ASTNode *case_node = node->children[i];
        if (case_node->type == AST_CASE_STMT) {
            // 生成case比较代码
            case_match_addrs[case_count] = codesIndex;
            gen_code("LOAD", temp_addr);          // 加载switch表达式值
            semantic_translate(case_node->children[0]);  // 加载case常量
            gen_code("EQ", 0);                    // 比较
            gen_code("BRF", 0);                   // 不匹配则跳转（目标稍后回填）
            
            // case body起始地址
            case_body_addrs[case_count] = codesIndex;
            case_has_break[case_count] = 0;
            
            // 生成case body代码
            // case的children[1]是statements节点（AST_COMPOUND_STMT）
            ASTNode *stmts = case_node->children[1];
            for (int j = 0; j < stmts->child_count; j++) {
                ASTNode *child = stmts->children[j];
                if (child->type == AST_BREAK_STMT) {
                    case_has_break[case_count] = 1;
                    gen_code("BR", 0);            // break跳转（目标稍后回填）
                    break_addrs[break_count++] = codesIndex - 1;
                } else {
                    semantic_translate(child);
                }
            }
            
            // case body结束地址
            case_end_addrs[case_count] = codesIndex;
            
            // 如果没有break，生成穿透跳转（目标稍后回填）
            if (!case_has_break[case_count]) {
                gen_code("BR", 0);
                fallthrough_addrs[fallthrough_count++] = codesIndex - 1;
            }
            
            case_count++;
        } else if (case_node->type == AST_DEFAULT_STMT) {
            default_addr = codesIndex;
            
            // 生成default body代码
            // default的children[0]是statements节点（AST_COMPOUND_STMT）
            ASTNode *stmts = case_node->children[0];
            for (int j = 0; j < stmts->child_count; j++) {
                ASTNode *child = stmts->children[j];
                if (child->type == AST_BREAK_STMT) {
                    gen_code("BR", 0);
                    break_addrs[break_count++] = codesIndex - 1;
                } else {
                    semantic_translate(child);
                }
            }
            
            default_end_addr = codesIndex;
        }
    }
    
    int switch_end_addr = codesIndex;
    
    // 回填BRF跳转目标：不匹配时跳转到下一个case的match或default或switch结束
    for (int i = 0; i < case_count; i++) {
        int brf_addr = case_match_addrs[i] + 3;  // BRF指令的地址
        if (i < case_count - 1) {
            // 跳转到下一个case的match
            codes[brf_addr].operand = case_match_addrs[i + 1];
        } else if (default_addr >= 0) {
            // 跳转到default
            codes[brf_addr].operand = default_addr;
        } else {
            // 跳转到switch结束
            codes[brf_addr].operand = switch_end_addr;
        }
    }
    
    // 回填穿透BR跳转目标：跳转到下一个case的body或default
    for (int i = 0; i < fallthrough_count; i++) {
        // 找到这个穿透BR属于哪个case
        int case_idx = -1;
        for (int j = 0; j < case_count; j++) {
            if (fallthrough_addrs[i] == case_end_addrs[j]) {
                case_idx = j;
                break;
            }
        }
        
        if (case_idx >= 0) {
            if (case_idx < case_count - 1) {
                // 跳转到下一个case的body
                codes[fallthrough_addrs[i]].operand = case_body_addrs[case_idx + 1];
            } else if (default_addr >= 0) {
                // 跳转到default
                codes[fallthrough_addrs[i]].operand = default_addr;
            } else {
                // 跳转到switch结束
                codes[fallthrough_addrs[i]].operand = switch_end_addr;
            }
        }
    }
    
    // 回填所有break跳转目标：跳转到switch结束
    for (int i = 0; i < break_count; i++) {
        codes[break_addrs[i]].operand = switch_end_addr;
    }
}

//翻译for语句：for(init; cond; update) { body }
void trans_for(ASTNode *node) {
    // for循环通常有3个子节点：初始化、条件、更新，然后是循环体
    // 或者根据具体的AST结构，可能有不同的子节点组织
    
    // 1. 先执行初始化语句
    if (node->child_count > 0 && node->children[0]) {
        semantic_translate(node->children[0]);
    }
    
    // 2. 循环开始标签
    int lab_cond = codesIndex;
    
    // 3. 检查条件
    if (node->child_count > 1 && node->children[1]) {
        semantic_translate(node->children[1]);
    }
    
    // 4. 条件不满足则跳出
    int cx_brf = codesIndex;
    gen_code("BRF", 0);
    
    // 5. 执行循环体
    if (node->child_count > 3 && node->children[3]) {
        semantic_translate(node->children[3]);
    }
    
    // 6. 执行更新语句
    if (node->child_count > 2 && node->children[2]) {
        semantic_translate(node->children[2]);
    }
    
    // 7. 跳转回条件检查
    gen_code("BR", lab_cond);
    
    // 8. 回填BRF的目标地址
    codes[cx_brf].operand = codesIndex;
}

//翻译函数调用：参数入栈 -> CAL函数调用 -> 结果在栈顶
void trans_call(ASTNode *node) {
    // 函数调用节点的子节点是参数
    int arg_count = node->child_count;
    
    // 检查函数调用参数匹配
    check_function_call(node->value, node->children, arg_count, node->line);
    
    // 1. 参数入栈（从右到左，符合虚拟机ENTER指令的期望）
    // 参数会在ENTER指令之后位于base之前，使用负数偏移访问
    for (int i = arg_count - 1; i >= 0; i--) {
        semantic_translate(node->children[i]);
    }
    
    // 2. CAL func_name：函数调用
    // 在栈式抽象机中，CAL指令会自动处理栈帧
    // 查找函数符号的地址！（不重复报告错误，因为check_function_call已经报告过了）
    SymbolItem *func_item = lookup_symbol(node->value, node->line, 0);
    int func_addr = 0;
    if (func_item != NULL) {
        func_addr = func_item->address;
    }
    gen_code("CAL", func_addr);
}

//翻译函数声明：生成函数入口和函数体
void trans_fun_decl(ASTNode *node) {
    // 保存当前函数指针（用于统计局部变量）
    SymbolItem *prev_fun = current_fun;
    current_fun = lookup_symbol(node->value, node->line, 0);
    
    // 收集参数数量
    int param_count_in_ast = 0;
    for (int i = 0; i < node->child_count; i++) {
        ASTNode *child = node->children[i];
        if (child->type == AST_VAR_DECL && strchr(child->value, ':') != NULL) {
            param_count_in_ast++;
        } else {
            break;
        }
    }
    
    // 如果函数符号已存在，更新其param_count
    if (current_fun != NULL) {
        current_fun->param_count = param_count_in_ast;
    }
    
    // 1. ENTER n：为函数开辟数据区（n为局部变量数量）
    int enter_pos = codesIndex;
    gen_code("ENTER", 0);
    
    // 2. 找到函数体节点，并收集参数信息
    int body_index = 0;
    int param_count = 0;
    char param_names[10][20];
    Type param_types[10];
    
    for (int i = 0; i < node->child_count; i++) {
        ASTNode *child = node->children[i];
        if (child->type == AST_VAR_DECL && strchr(child->value, ':') != NULL) {
            // 收集参数信息
            char type_str[20];
            sscanf(child->value, "%[^:]:%s", param_names[param_count], type_str);
            
            if (strcmp(type_str, "int") == 0) {
                param_types[param_count] = TYPE_INT;
            } else if (strcmp(type_str, "string") == 0) {
                param_types[param_count] = TYPE_STRING;
            } else if (strcmp(type_str, "bool") == 0) {
                param_types[param_count] = TYPE_BOOL;
            } else {
                param_types[param_count] = TYPE_VOID;
            }
            param_count++;
        } else {
            body_index = i;
            break;
        }
    }
    
    // 3. 调用semantic_translate处理函数体（包括作用域管理）
    if (body_index < node->child_count) {
        // 保存当前global_off，函数内部使用相对地址从0开始
        int saved_global_off = global_off;
        global_off = 0;
        
        // 先插入参数到符号表（参数使用负数偏移，相对于base）
        scope_enter();
        // 临时保存current_fun，避免参数计入局部变量计数
        SymbolItem *temp_current_fun = current_fun;
        current_fun = NULL;
        for (int i = 0; i < param_count; i++) {
            insert_symbol(SYM_VARIABLE, param_names[i], param_types[i], node->line, 0);
            // 参数从右到左入栈：第一个参数在栈底（偏移量大），最后一个在栈顶（偏移量小）
            // 第一个参数对应偏移量 -param_count，最后一个对应偏移量 -1
            SymbolItem *item = lookup_symbol(param_names[i], node->line, 0);
            if (item) {
                item->address = -(param_count - i);
            }
        }
        // 恢复current_fun
        current_fun = temp_current_fun;
        
        // 4. 翻译函数体的子节点
        ASTNode *body_node = node->children[body_index];
        for (int i = 0; i < body_node->child_count; i++) {
            semantic_translate(body_node->children[i]);
        }
        
        scope_leave();
        
        // 恢复global_off
        global_off = saved_global_off;
    }
    
    // 5. 回填ENTER指令的操作数（参数数量*1000 + 局部变量数量）
    if (current_fun != NULL) {
        codes[enter_pos].operand = param_count * 1000 + current_fun->local_count;
    }
    
    // 6. RETURN：函数返回
    gen_code("RETURN", 0);
    
    // 恢复之前的函数
    current_fun = prev_fun;
}

// 类型推断函数
Type infer_type(ASTNode *node) {
    if (!node) return TYPE_ERROR;
    
    switch(node->type) {
        case AST_NUM_LITERAL:
            return TYPE_INT;
        case AST_STRING_LITERAL:
            return TYPE_STRING;
        case AST_IDENTIFIER: {
            SymbolItem *item = lookup_symbol(node->value, node->line, 1);  // 修改为1，启用错误报告
            return item ? item->type : TYPE_ERROR;
        }
        case AST_BINARY_EXPR: {
            Type left_type = infer_type(node->children[0]);
            Type right_type = infer_type(node->children[1]);
            // 如果操作数类型不一致，报错
            if (left_type != right_type && left_type != TYPE_ERROR && right_type != TYPE_ERROR) {
                char msg[256];
                sprintf(msg,"语义错误：二元运算操作数类型不匹配，左操作数%s类型，右操作数%s类型",
                        type_names[left_type], type_names[right_type]);
                add_error(msg, node->line, 1);
                semantic_err++;
            }
            return left_type != TYPE_ERROR ? left_type : right_type;
        }
        case AST_ASSIGN_EXPR:
            return infer_type(node->children[1]);
        default:
            return TYPE_ERROR;
    }
}

//主语义递归遍历（扩展完整语义检查）
void semantic_translate(ASTNode *node) {
    if(!node) return;
    switch(node->type){
        case AST_VAR_DECL: {
            // 获取变量类型
            Type var_type = TYPE_INT; // 默认int类型
            if(node->child_count >= 1 && node->children[0]) {
                const char *type_str = node->children[0]->value;
                var_type = string_to_type(type_str);
                
                // 检查类型不匹配：变量不能声明为void类型
                if (var_type == TYPE_VOID) {
                    char msg[256];
                    sprintf(msg,"语义错误：变量%s不能声明为void类型",node->value);
                    add_error(msg, node->line, 1);
                    semantic_err++;
                }
            }
            //变量声明：符号表插入（语义分析阶段，进行错误检测）
            insert_symbol(SYM_VARIABLE, node->value, var_type, node->line, 1);
            //带初始化：var a:int=10;
            if(node->child_count>=2){
                Type init_type = infer_type(node->children[1]);
                // 检查初始化表达式的类型是否匹配
                if (var_type != TYPE_ERROR && init_type != TYPE_ERROR && var_type != init_type) {
                    char msg[256];
                    sprintf(msg,"语义错误：变量%s初始化类型不匹配，变量是%s类型，表达式是%s类型",
                            node->value, type_names[var_type], type_names[init_type]);
                    add_error(msg, node->line, 1);
                    semantic_err++;
                }
                semantic_translate(node->children[1]);
                int pos=lookup(node->value,node->line);
                if(pos!=-1) gen_code("STO",pos);
            }
            break;
        }
        case AST_ARRAY_DECL: {
            // 获取数组类型
            Type arr_type = TYPE_INT;
            if(node->child_count >= 1 && node->children[0]) {
                const char *type_str = node->children[0]->value;
                arr_type = string_to_type(type_str);
            }
            
            // 获取数组大小（如果有）
            int arr_size = 1;
            if(node->child_count >= 2 && node->children[1]) {
                arr_size = atoi(node->children[1]->value);
                if (arr_size <= 0) {
                    add_error("语义错误：数组大小必须大于0", node->line, 1);
                    semantic_err++;
                    break;
                }
            }
            
            // 插入数组符号（使用dim字段标记为数组）
            insert_symbol(SYM_VARIABLE, node->value, arr_type, node->line, arr_size);
            
            break;
        }
        case AST_ARRAY_ACCESS: {
            // 数组访问：生成LOADA指令
            int base_addr = lookup(node->value, node->line);
            if (base_addr == -1) {
                add_error("语义错误：未声明的数组", node->line, 1);
                semantic_err++;
                break;
            }
            
            // 翻译索引表达式
            semantic_translate(node->children[0]);
            gen_code("LOADA", base_addr);
            break;
        }
        case AST_ASSIGN_EXPR: {
            // 类型检查：赋值语句两边类型应该一致
            ASTNode *idnode = node->children[0];
            ASTNode *exprnode = node->children[1];
            SymbolItem *var_item = lookup_symbol(idnode->value, idnode->line, 1);  // 修改为1，启用错误报告
            Type var_type = var_item ? var_item->type : TYPE_ERROR;
            Type expr_type = infer_type(exprnode);
            if (var_type != TYPE_ERROR && expr_type != TYPE_ERROR && var_type != expr_type) {
                char msg[256];
                sprintf(msg,"语义错误：赋值语句类型不匹配，变量%s是%s类型，表达式是%s类型",
                        idnode->value, type_names[var_type], type_names[expr_type]);
                add_error(msg, node->line, 1);
                semantic_err++;
            }
            trans_assign(node);
            break;
        }
        case AST_BINARY_EXPR:
            trans_binary(node);
            break;
        case AST_IDENTIFIER:
            trans_id(node);
            break;
        case AST_NUM_LITERAL:
            trans_num(node);
            break;
        case AST_STRING_LITERAL:
            trans_string(node);
            break;
        case AST_READ_STMT:
            trans_read(node);
            break;
        case AST_WRITE_STMT:
            trans_write(node);
            break;
        case AST_IF_STMT:
            trans_if(node);
            break;
        case AST_WHILE_STMT:
            loop_nest_level++;
            trans_while(node);
            loop_nest_level--;
            break;
        case AST_DO_WHILE_STMT:
            loop_nest_level++;
            trans_do_while(node);
            loop_nest_level--;
            break;
        case AST_FOR_STMT:
            loop_nest_level++;
            trans_for(node);
            loop_nest_level--;
            break;
        case AST_SWITCH_STMT:
            in_switch = 1;
            trans_switch(node);
            in_switch = 0;
            break;
        case AST_BREAK_STMT:
            if (loop_nest_level == 0 && !in_switch) {
                add_error("语义错误：break语句不在循环或switch中", node->line, 1);
                semantic_err++;
            }
            break;
        case AST_CONTINUE_STMT:
            if (loop_nest_level == 0) {
                add_error("语义错误：continue语句不在循环中", node->line, 1);
                semantic_err++;
            }
            break;
        case AST_RETURN_STMT:
            // return语句：翻译返回表达式（如果有）
            if (node->child_count > 0) {
                semantic_translate(node->children[0]);
            }
            break;
        case AST_COMPOUND_STMT:
            scope_enter();
            for(int i=0;i<node->child_count;i++)
                semantic_translate(node->children[i]);
            scope_leave();
            break;
        case AST_PROGRAM: {
            // 检查是否是 declarations_marker（函数内部的声明列表）
            if(node->value && strcmp(node->value, "declarations_marker") == 0) {
                // 只是简单遍历声明节点
                for(int i=0; i<node->child_count; i++) {
                    semantic_translate(node->children[i]);
                }
            } else {
                // 真正的程序入口：收集所有全局变量声明、函数声明和main函数
                ASTNode *main_node = NULL;
                int func_count = 0;
                int global_var_count = 0;
                ASTNode *funcs[20];
                ASTNode *global_vars[20];
                
                for(int i=0; i<node->child_count; i++) {
                    ASTNode *child = node->children[i];
                    if (child->type == AST_MAIN_DECL) {
                        main_node = child;
                    } else if (child->type == AST_FUN_DECL) {
                        funcs[func_count++] = child;
                    } else if (child->type == AST_VAR_DECL) {
                        global_vars[global_var_count++] = child;
                    }
                }
                
                // 先翻译全局变量声明（生成初始化代码）
                for(int i=0; i<global_var_count; i++) {
                    semantic_translate(global_vars[i]);
                }
                
                // 中间代码第一句：无条件跳转到main函数入口（放在全局变量初始化之后）
                int br_main_pos = codesIndex;
                gen_code("BR", 0);  // 操作数暂时为0，稍后回填
                
                // 先插入所有函数符号到符号表，不翻译，只是占位
                for(int i=0; i<func_count; i++) {
                    int prev_err = semantic_err;
                    insert_symbol(SYM_FUNCTION, funcs[i]->value, TYPE_VOID, funcs[i]->line, 1);
                    // 如果有错误，不插入
                }
                
                // 翻译所有函数（生成中间代码，包括ENTER）
                for(int i=0; i<func_count; i++) {
                    SymbolItem *check_item = lookup_symbol(funcs[i]->value, funcs[i]->line, 0);
                    int has_error = 0;
                    if (check_item == NULL) {
                        has_error = 1;
                    }
                    if (!has_error) {
                        check_item->address = codesIndex;
                        // 重置local_count为0（因为我们现在开始正式翻译）
                        check_item->local_count = 0;
                        trans_fun_decl(funcs[i]);
                    }
                }
                
                // 记录main函数的入口地址（用于回填BR指令）
                int main_entry = 0;
                
                // 生成main函数代码
                if (main_node) {
                    // main函数也需要ENTER指令
                    SymbolItem *main_fun = lookup_symbol("main", main_node->line, 0);
                    SymbolItem *prev_fun = current_fun;
                    current_fun = main_fun;
                    if (main_fun != NULL) {
                        main_fun->local_count = 0;
                    }
                    
                    // 生成ENTER指令（先占位，后面回填）
                    int main_enter_pos = codesIndex;
                    gen_code("ENTER", 0);
                    
                    // 记录main函数的入口地址（用于回填BR指令）
                    main_entry = codesIndex - 1;  // 指向ENTER指令
                    
                    // 保存当前global_off，main函数内部使用相对地址从0开始
                    int saved_global_off = global_off;
                    global_off = 0;
                    
                    // 翻译main函数体
                    semantic_translate(main_node);
                    
                    // 恢复global_off
                    global_off = saved_global_off;
                    
                    // 回填ENTER的操作数
                    if (main_fun != NULL) {
                        codes[main_enter_pos].operand = main_fun->local_count;
                    }
                    
                    current_fun = prev_fun;
                }
                
                // 在main函数结束后添加STOP指令
                gen_code("STOP", 0);
                
                // 回填BR指令的操作数（main函数入口地址）
                codes[br_main_pos].operand = main_entry;
            }
            break;
        }
        case AST_FUN_BODY:
            // 函数体不单独创建作用域，因为函数声明已经创建了作用域
            for(int i=0;i<node->child_count;i++)
                semantic_translate(node->children[i]);
            break;
        case AST_MAIN_DECL: {
            // main函数处理
            if (node->child_count > 0) {
                semantic_translate(node->children[0]);
            }
            break;
        }
        case AST_FUN_DECL: {
            // 在program处理中已经处理过了，这里什么都不做！
            break;
        }
        case AST_FUNC_CALL:
            trans_call(node);
            break;
        case AST_EXPR_STMT:
            semantic_translate(node->children[0]);
            break;
        default:
            for(int i=0;i<node->child_count;i++)
                semantic_translate(node->children[i]);
            break;
    }
}

// 添加错误：仅终端输出，不写入错误文件
static void add_error(const char *message, int line, int column) {
    if (error_count < MAX_ERRORS) {
        snprintf(errors[error_count].message, sizeof(errors[error_count].message),
                 "%s", message);
        errors[error_count].line = line;
        errors[error_count].column = column;
        // 所有错误（词法+语法+语义）仅控制台打印
        printf("第%d行：%s\n", line, message);
        error_count++;
    }
}

//词法分析核心
// 读取下一个字符
static void next_char() {
    current_char = fgetc(source_file);
    if (current_char == '\n') {
        current_line++;// 行号 +1
        current_column = 1;
    } else if (current_char != EOF) {
        current_column++; // 列号 +1
    }
}

// 回退一个字符
static void unget_char() {
    if (current_char != EOF) {
        ungetc(current_char, source_file);
        if (current_char == '\n') {
            current_line--;
        } else {
            current_column--;
        }
    }
}

// Token类型转字符串（严格按照示例输出）
const char* token_type_to_string(TokenType type) {
    switch (type) {
        case TOKEN_ID: return "ID";
        case TOKEN_NUM: return "NUM";
        case TOKEN_STRING: return "STRING";
        case TOKEN_AS: return "as";
        case TOKEN_BREAK: return "break";
        case TOKEN_CASE: return "case";
        case TOKEN_CONST: return "const";
        case TOKEN_CONTINUE: return "continue";
        case TOKEN_DO: return "do";
        case TOKEN_ELSE: return "else";
        case TOKEN_FOR: return "for";
        case TOKEN_FROM: return "from";
        case TOKEN_FUNC: return "func";
        case TOKEN_IF: return "if";
        case TOKEN_IN: return "in";
        case TOKEN_LET: return "let";
        case TOKEN_MAIN: return "main";
        case TOKEN_MATCH: return "match";
        case TOKEN_VAR: return "var";
        case TOKEN_WHERE: return "where";
        case TOKEN_WHILE: return "while";
        case TOKEN_READ: return "read";
        case TOKEN_WRITE: return "write";
        case TOKEN_RETURN: return "return";
        case TOKEN_PLUS: return "+";
        case TOKEN_MINUS: return "-";
        case TOKEN_MUL: return "*";
        case TOKEN_DIV: return "/";
        case TOKEN_ASSIGN: return "=";
        case TOKEN_EQ: return "==";
        case TOKEN_NE: return "!=";
        case TOKEN_GT: return ">";
        case TOKEN_LT: return "<";
        case TOKEN_GE: return ">=";
        case TOKEN_LE: return "<=";
        case TOKEN_LPAREN: return "(";
        case TOKEN_RPAREN: return ")";
        case TOKEN_LBRACE: return "{";
        case TOKEN_RBRACE: return "}";
        case TOKEN_LBRACKET: return "[";
        case TOKEN_RBRACKET: return "]";
        case TOKEN_SEMICOLON: return ";";
        case TOKEN_COLON: return ":";
        case TOKEN_COMMA: return ",";
        case TOKEN_DOT: return ".";
        case TOKEN_DOTDOT: return "..";
        case TOKEN_DOTDOTEQ: return "..=";
        case TOKEN_EOF: return "EOF";
        default: return "ERROR";
    }
}

//词法分析器核心
// 跳过空白字符和注释
static void skip_whitespace_and_comments() {
    while (current_char == ' ' || current_char == '\t' || current_char == '\n' || current_char == '\r') {
        next_char();
    }

    // 处理单行注释 //
    if (current_char == '/') {
        next_char();
        if (current_char == '/') {
            while (current_char != '\n' && current_char != EOF) {
                next_char();
            }
            skip_whitespace_and_comments();
        }
        // 处理多行注释 /* */
        else if (current_char == '*') {
            int start_line = current_line;
            int start_col = current_column - 1;
            next_char();
            while (1) {
                if (current_char == EOF) {
                    add_error("未闭合的多行注释", start_line, start_col);
                    break;
                }
                if (current_char == '*') {
                    next_char();
                    if (current_char == '/') {
                        next_char();
                        break;
                    }
                } else {
                    next_char();
                }
            }
            skip_whitespace_and_comments();
        } else {
            unget_char();
        }
    }
}

// 识别标识符或关键字
static TokenType scan_identifier(char *buffer) {
    int i = 0;
    buffer[i++] = current_char;
    next_char();

    while (((current_char >= 'a' && current_char <= 'z') || (current_char >= 'A' && current_char <= 'Z') || (current_char >= '0' && current_char <= '9') || current_char == '_')) {
        if (i < MAX_TOKEN_LEN - 1) {
            buffer[i++] = current_char;
        }
        next_char();
    }
    buffer[i] = '\0';

    // 查找关键字
    for (int j = 0; keywords[j].name != NULL; j++) {
        if (strcmp(buffer, keywords[j].name) == 0) {
            return keywords[j].type;
        }
    }
    return TOKEN_ID;
}

// 识别数字
static TokenType scan_number(char *buffer) {
    int i = 0;
    buffer[i++] = current_char;
    next_char();

    while (isdigit(current_char)) {
        if (i < MAX_TOKEN_LEN - 1) {
            buffer[i++] = current_char;
        }
        next_char();
    }
    buffer[i] = '\0';
    return TOKEN_NUM;
}

// 识别字符串字面量
static TokenType scan_string(char *buffer) {
    int i = 0;
    next_char(); // 跳过开头的引号

    while (current_char != EOF && current_char != '\"') {
        if (i < MAX_TOKEN_LEN - 2) {
            buffer[i++] = current_char;
        }
        next_char();
    }

    if (current_char == '\"') {
        next_char(); // 跳过结尾的引号
    } else {
        // 字符串未闭合错误
        char err_msg[100];
        snprintf(err_msg, sizeof(err_msg), "字符串未闭合");
        add_error(err_msg, current_line, current_column);
    }

    buffer[i] = '\0';
    return TOKEN_STRING;
}

// 获取下一个Token
static Token get_next_token() {
    Token token;
    skip_whitespace_and_comments();
    token.line = current_line;
    token.column = current_column;

    if (current_char == EOF) {
        token.type = TOKEN_EOF;
        strcpy(token.value, "EOF");
        return token;
    }

    // 标识符或关键字
    if ((current_char >= 'a' && current_char <= 'z') || (current_char >= 'A' && current_char <= 'Z') || current_char == '_') {
        token.type = scan_identifier(token.value);
        return token;
    }

    // 数字
    if (isdigit(current_char)) {
        token.type = scan_number(token.value);
        return token;
    }
    
    // 字符串字面量
    if (current_char == '\"') {
        token.type = scan_string(token.value);
        return token;
    }

    // 运算符和界符
    switch (current_char) {
        case '+': token.type = TOKEN_PLUS; strcpy(token.value, "+"); next_char(); break;
        case '-': token.type = TOKEN_MINUS; strcpy(token.value, "-"); next_char(); break;
        case '*': token.type = TOKEN_MUL; strcpy(token.value, "*"); next_char(); break;
        case '/': token.type = TOKEN_DIV; strcpy(token.value, "/"); next_char(); break;
        case '=':
            next_char();
            if (current_char == '=') {
                token.type = TOKEN_EQ; strcpy(token.value, "=="); next_char();
            } else {
                token.type = TOKEN_ASSIGN; strcpy(token.value, "=");
            }
            break;
        case '!':
            next_char();
            if (current_char == '=') {
                token.type = TOKEN_NE; strcpy(token.value, "!="); next_char();
            } else {
                char err_msg[100];
                snprintf(err_msg, sizeof(err_msg), "非法字符 '!'");
                add_error(err_msg, token.line, token.column);
                token.type = TOKEN_ERROR; strcpy(token.value, "!");
            }
            break;
        case '>':
            next_char();
            if (current_char == '=') {
                token.type = TOKEN_GE; strcpy(token.value, ">="); next_char();
            } else {
                token.type = TOKEN_GT; strcpy(token.value, ">");
            }
            break;
        case '<':
            next_char();
            if (current_char == '=') {
                token.type = TOKEN_LE; strcpy(token.value, "<="); next_char();
            } else {
                token.type = TOKEN_LT; strcpy(token.value, "<");
            }
            break;
        case '(': token.type = TOKEN_LPAREN; strcpy(token.value, "("); next_char(); break;
        case ')': token.type = TOKEN_RPAREN; strcpy(token.value, ")"); next_char(); break;
        case '{': token.type = TOKEN_LBRACE; strcpy(token.value, "{"); next_char(); break;
        case '}': token.type = TOKEN_RBRACE; strcpy(token.value, "}"); next_char(); break;
        case '[': token.type = TOKEN_LBRACKET; strcpy(token.value, "["); next_char(); break;
        case ']': token.type = TOKEN_RBRACKET; strcpy(token.value, "]"); next_char(); break;
        case ';': token.type = TOKEN_SEMICOLON; strcpy(token.value, ";"); next_char(); break;
        case ':': token.type = TOKEN_COLON; strcpy(token.value, ":"); next_char(); break;
        case ',': token.type = TOKEN_COMMA; strcpy(token.value, ","); next_char(); break;
        case '.':
            next_char();
            if (current_char == '.') {
                next_char();
                if (current_char == '=') {
                    token.type = TOKEN_DOTDOTEQ; strcpy(token.value, "..="); next_char();
                } else {
                    token.type = TOKEN_DOTDOT; strcpy(token.value, "..");
                }
            } else {
                token.type = TOKEN_DOT; strcpy(token.value, ".");
            }
            break;
        default:
            char err_msg[100];
            snprintf(err_msg, sizeof(err_msg), "非法字符 '%c'", current_char);
            add_error(err_msg, token.line, token.column);
            token.type = TOKEN_ERROR;
            token.value[0] = current_char;
            token.value[1] = '\0';
            next_char();
            break;
    }
    return token;
}

// 词法分析主函数（严格按照示例输出格式，文件中不包含错误信息）
int lexical_analysis(const char *input_filename, const char *output_filename) {
    source_file = fopen(input_filename, "r");
    if (!source_file) {
        perror("无法打开源文件");
        return 1;
    }

    FILE *token_file = fopen(output_filename, "w");
    if (!token_file) {
        perror("无法创建tokens文件");
        fclose(source_file);
        return 1;
    }

    init_token_list(&token_list);
    current_line = 1;
    current_column = 1;
    error_count = 0;

    // 写入表头（和示例完全一致）
    fprintf(token_file, "%-15s %s\n", "单词类别", "单词值");

    printf("\n===== 词法分析错误 =====\n");
    next_char();
    while (1) {
        Token token = get_next_token();
        add_token(&token_list, token);

        if (token.type == TOKEN_EOF) break;

        // 只输出单词类别和单词值两列，不输出错误信息
        fprintf(token_file, "%-15s %s\n",
                token_type_to_string(token.type), token.value);
    }

    fclose(token_file);
    fclose(source_file);

    if (error_count == 0) {
        printf("无词法错误\n");
    }

    printf("\n✅ 词法分析完成，结果已保存到: %s\n", output_filename);
    return error_count > 0 ? 1 : 0;
}

//语法分析器核心（递归下降+AST生成）
// 获取当前Token
static Token current_token() {
    return token_list.data[current_token_index];
}

// 跳到下一个Token
static void advance() {
    if (current_token_index < token_list.count - 1) {
        current_token_index++;
    }
}

// 匹配预期Token，不匹配则报错
static int match(TokenType expected) {
    if (current_token().type == expected) {
        advance();
        return 1;
    }
    char err_msg[200];
    snprintf(err_msg, sizeof(err_msg), "缺少 '%s', 实际得到 '%s'",
             token_type_to_string(expected), current_token().value);
    add_error(err_msg, current_token().line, current_token().column);
    advance(); // 错误恢复
    return 0;
}

// 语法分析函数声明（返回AST节点）
static ASTNode* program();// 程序入口（必须有main）
static ASTNode* fun_declaration();// 函数声明
static ASTNode* main_declaration();// main函数
static ASTNode* fun_body();// 函数体
static ASTNode* declaration_list();
static ASTNode* declaration_stat();
static ASTNode* statement_list();
static ASTNode* statement();// 语句（if/while/for/变量/read/write/break/continue/return）
static ASTNode* if_stat();
static ASTNode* while_stat();
static ASTNode* do_while_stat();
static ASTNode* for_stat();
static ASTNode* switch_stat();
static ASTNode* read_stat();// read语句
static ASTNode* write_stat();// write语句
static ASTNode* break_stat();// break语句
static ASTNode* continue_stat();// continue语句
static ASTNode* return_stat();// return语句
static ASTNode* expression_stat();
static ASTNode* expression();// 表达式（加减乘除/赋值）
static ASTNode* bool_expr();
static ASTNode* compare_expr();
static ASTNode* additive_expr();
static ASTNode* term();
static ASTNode* factor();

// 程序入口
static ASTNode* program() {
    ASTNode *node = create_ast_node(AST_PROGRAM, "program", 0, 0);

    // 可选的全局变量声明列表
    while (current_token().type == TOKEN_VAR) {
        add_ast_child(node, declaration_stat());
    }

    // 可选的函数声明列表
    while (current_token().type == TOKEN_FUNC) {
        add_ast_child(node, fun_declaration());
    }

    // 必须有main函数，支持两种形式：
    // 1. main()  （无关键字）
    // 2. main()  （TOKEN_MAIN 关键字）
    if (current_token().type == TOKEN_MAIN || current_token().type == TOKEN_ID) {
        // 检查是否是 main 函数
        Token first_token = current_token();
        if (current_token().type == TOKEN_ID && strcmp(current_token().value, "main") == 0) {
            // 处理无关键字的 main()
            match(TOKEN_ID);
            // 手动创建 main 节点
            ASTNode *main_node = create_ast_node(AST_MAIN_DECL, "main", first_token.line, first_token.column);
            insert_symbol(SYM_FUNCTION, "main", TYPE_VOID, first_token.line, 0);
            match(TOKEN_LPAREN);
            while (current_token().type == TOKEN_ID) {
                match(TOKEN_ID);
                if (current_token().type == TOKEN_COLON) {
                    match(TOKEN_COLON);
                    match(TOKEN_ID);
                }
                if (current_token().type == TOKEN_COMMA) {
                    match(TOKEN_COMMA);
                }
            }
            match(TOKEN_RPAREN);
            if (current_token().type == TOKEN_COLON) {
                match(TOKEN_COLON);
                match(TOKEN_ID);
            }
            add_ast_child(main_node, fun_body());
            add_ast_child(node, main_node);
        } else if (current_token().type == TOKEN_MAIN) {
            add_ast_child(node, main_declaration());
        } else {
            add_error("程序缺少main函数", current_token().line, current_token().column);
        }
    } else {
        add_error("程序缺少main函数", current_token().line, current_token().column);
    }

    return node;
}

// 函数声明
static ASTNode* fun_declaration() {
    Token func_token = current_token();
    match(TOKEN_FUNC);
    Token id_token = current_token();
    match(TOKEN_ID);

    ASTNode *node = create_ast_node(AST_FUN_DECL, id_token.value, id_token.line, id_token.column);
    // 语法分析阶段：不插入符号表，只构建AST

    match(TOKEN_LPAREN);
    // 参数列表
    while (current_token().type == TOKEN_ID) {
        Token param_name_token = current_token();
        match(TOKEN_ID);
        match(TOKEN_COLON);
        Token param_type_token = current_token();
        match(TOKEN_ID);
        
        // 创建参数节点（格式："参数名:类型"）
        char param_info[40];
        sprintf(param_info, "%s:%s", param_name_token.value, param_type_token.value);
        ASTNode *param_node = create_ast_node(AST_VAR_DECL, param_info, param_name_token.line, param_name_token.column);
        add_ast_child(node, param_node);
        
        if (current_token().type == TOKEN_COMMA) {
            match(TOKEN_COMMA);
        }
    }
    match(TOKEN_RPAREN);

    // 可选返回值类型
    if (current_token().type == TOKEN_COLON) {
        match(TOKEN_COLON);
        match(TOKEN_ID);
    }

    add_ast_child(node, fun_body());
    return node;
}

// main函数声明
static ASTNode* main_declaration() {
    Token main_token = current_token();
    match(TOKEN_MAIN);

    ASTNode *node = create_ast_node(AST_MAIN_DECL, "main", main_token.line, main_token.column);
    insert_symbol(SYM_FUNCTION,"main", TYPE_VOID, main_token.line, 0);

    match(TOKEN_LPAREN);
    // 参数列表
    while (current_token().type == TOKEN_ID) {
        match(TOKEN_ID);
        match(TOKEN_COLON);
        match(TOKEN_ID);
        if (current_token().type == TOKEN_COMMA) {
            match(TOKEN_COMMA);
        }
    }
    match(TOKEN_RPAREN);

    // 可选返回值类型
    if (current_token().type == TOKEN_COLON) {
        match(TOKEN_COLON);
        match(TOKEN_ID);
    }

    add_ast_child(node, fun_body());
    return node;
}

// 函数体
static ASTNode* fun_body() {
    Token lbrace_token = current_token();
    match(TOKEN_LBRACE);

    ASTNode *node = create_ast_node(AST_FUN_BODY, "body", lbrace_token.line, lbrace_token.column);

    add_ast_child(node, declaration_list());
    add_ast_child(node, statement_list());

    match(TOKEN_RBRACE);
    return node;
}

// 声明列表
// 注意：这里不返回 COMPOUND_STMT，而是直接在 fun_body 中处理，避免额外的作用域
static ASTNode* declaration_list() {
    // 我们返回一个特殊节点或者直接处理，但为了简单，我们返回一个空节点
    // 真正的声明将在 fun_body 中处理
    ASTNode *node = create_ast_node(AST_PROGRAM, "declarations_marker", 0, 0);

    while (current_token().type == TOKEN_VAR || current_token().type == TOKEN_LET ||
           current_token().type == TOKEN_CONST || current_token().type == TOKEN_ID) {
        // 如果是 ID，可能是类型名（如 int），检查下一个 token 是否是 ID（变量名）
        if (current_token().type == TOKEN_ID) {
            // 临时查看下一个 token
            int save_index = current_token_index;
            advance();
            if (current_token().type == TOKEN_ID) {
                // 看起来像 int x，恢复索引后调用 declaration_stat
                current_token_index = save_index;
                add_ast_child(node, declaration_stat());
            } else {
                // 只是普通的 ID，不是声明，恢复索引
                current_token_index = save_index;
                break;
            }
        } else {
            add_ast_child(node, declaration_stat());
        }
    }

    return node;
}

// 声明语句
static ASTNode* declaration_stat() {
    Token type_token = current_token();
    
    // 处理两种格式：
    // 1. 仓颉风格: var x: int
    // 2. C风格: int x
    // 3. 数组声明: var arr: int[10]
    if (type_token.type == TOKEN_VAR || type_token.type == TOKEN_LET || type_token.type == TOKEN_CONST) {
        // 仓颉风格
        match(type_token.type);
        
        Token id_token = current_token();
        if (current_token().type != TOKEN_ID) {
            add_error("缺少变量名", type_token.line, type_token.column);
            return create_ast_node(AST_VAR_DECL, "", type_token.line, type_token.column);
        }
        match(TOKEN_ID);
        match(TOKEN_COLON);
        Token actual_type_token = current_token();
        match(TOKEN_ID);
        
        // 检查是否是数组声明
        if (current_token().type == TOKEN_LBRACKET) {
            match(TOKEN_LBRACKET);
            ASTNode *arr_node = create_ast_node(AST_ARRAY_DECL, id_token.value, id_token.line, id_token.column);
            add_ast_child(arr_node, create_ast_node(AST_IDENTIFIER, actual_type_token.value, actual_type_token.line, actual_type_token.column));
            add_ast_child(arr_node, expression()); // 数组大小
            match(TOKEN_RBRACKET);
            
            // 可选初始化
            if (current_token().type == TOKEN_ASSIGN) {
                match(TOKEN_ASSIGN);
                add_ast_child(arr_node, expression());
            }
            return arr_node;
        }
        
        ASTNode *node = create_ast_node(AST_VAR_DECL, id_token.value, id_token.line, id_token.column);
        add_ast_child(node, create_ast_node(AST_IDENTIFIER, actual_type_token.value, actual_type_token.line, actual_type_token.column));
        
        // 可选初始化
        if (current_token().type == TOKEN_ASSIGN) {
            match(TOKEN_ASSIGN);
            add_ast_child(node, expression());
        }
        
        return node;
    } else if (type_token.type == TOKEN_ID) {
        // 可能是 C 风格声明，如 int x
        char type_name[20];
        strncpy(type_name, type_token.value, 20);
        match(TOKEN_ID);
        
        Token id_token = current_token();
        if (current_token().type != TOKEN_ID) {
            add_error("缺少变量名", type_token.line, type_token.column);
            return create_ast_node(AST_VAR_DECL, "", type_token.line, type_token.column);
        }
        match(TOKEN_ID);
        
        ASTNode *node = create_ast_node(AST_VAR_DECL, id_token.value, id_token.line, id_token.column);
        add_ast_child(node, create_ast_node(AST_IDENTIFIER, type_name, type_token.line, type_token.column));
        
        // 可选初始化
        if (current_token().type == TOKEN_ASSIGN) {
            match(TOKEN_ASSIGN);
            add_ast_child(node, expression());
        }
        
        return node;
    } else {
        add_error("无效的声明语句", type_token.line, type_token.column);
        return create_ast_node(AST_VAR_DECL, "", type_token.line, type_token.column);
    }
}

// 语句列表
static ASTNode* statement_list() {
    ASTNode *node = create_ast_node(AST_COMPOUND_STMT, "statements", 0, 0);

    while (current_token().type != TOKEN_RBRACE && current_token().type != TOKEN_EOF && 
           current_token().type != TOKEN_CASE && current_token().type != TOKEN_DEFAULT) {
        add_ast_child(node, statement());
    }

    return node;
}

// 核心：statement 函数（新增break和continue支持）
static ASTNode* statement() {
    // 检查是否是 C 风格声明，如 int x
    if (current_token().type == TOKEN_ID) {
        // 查看下一个 token 是否是 ID
        int save_index = current_token_index;
        advance();
        if (current_token().type == TOKEN_ID) {
            // 看起来是声明，恢复索引后返回声明语句
            current_token_index = save_index;
            return declaration_stat();
        }
        // 恢复索引
        current_token_index = save_index;
    }
    
    switch (current_token().type) {
        // 支持在任意代码块中声明变量
        case TOKEN_VAR:
        case TOKEN_LET:
        case TOKEN_CONST:
            return declaration_stat();
        case TOKEN_IF:
            return if_stat();
        case TOKEN_WHILE:
            return while_stat();
        case TOKEN_DO:
            return do_while_stat();
        case TOKEN_FOR:
            return for_stat();
        case TOKEN_SWITCH:
            return switch_stat();
        case TOKEN_READ:
            return read_stat();
        case TOKEN_WRITE:
            return write_stat();
        case TOKEN_BREAK:
            return break_stat();
        case TOKEN_CONTINUE:
            return continue_stat();
        case TOKEN_RETURN:
            return return_stat();
        case TOKEN_LBRACE: {
            Token lbrace_token = current_token();
            match(TOKEN_LBRACE);
            ASTNode *node = create_ast_node(AST_COMPOUND_STMT, "compound", lbrace_token.line, lbrace_token.column);
            add_ast_child(node, statement_list());
            match(TOKEN_RBRACE);
            return node;
        }
        default:
            return expression_stat();
    }
}

// if语句
static ASTNode* if_stat() {
    Token if_token = current_token();
    match(TOKEN_IF);

    ASTNode *node = create_ast_node(AST_IF_STMT, "if", if_token.line, if_token.column);

    match(TOKEN_LPAREN);
    add_ast_child(node, expression());
    match(TOKEN_RPAREN);
    add_ast_child(node, statement());

    if (current_token().type == TOKEN_ELSE) {
        match(TOKEN_ELSE);
        add_ast_child(node, statement());
    }

    return node;
}

// while语句
static ASTNode* while_stat() {
    Token while_token = current_token();
    match(TOKEN_WHILE);

    ASTNode *node = create_ast_node(AST_WHILE_STMT, "while", while_token.line, while_token.column);

    match(TOKEN_LPAREN);
    add_ast_child(node, expression());
    match(TOKEN_RPAREN);
    add_ast_child(node, statement());

    return node;
}

// for语句（修复：自动插入循环变量）
static ASTNode* for_stat() {
    Token for_token = current_token();
    match(TOKEN_FOR);

    ASTNode *node = create_ast_node(AST_FOR_STMT, "for", for_token.line, for_token.column);

    match(TOKEN_LPAREN);
    Token id_token = current_token();
    match(TOKEN_ID);
    // 自动插入for循环变量（语法分析阶段，不做错误检测）
    insert_symbol(SYM_VARIABLE, id_token.value, TYPE_INT, id_token.line, 0);
    add_ast_child(node, create_ast_node(AST_IDENTIFIER, id_token.value, id_token.line, id_token.column));
    match(TOKEN_IN);
    add_ast_child(node, expression());
    match(TOKEN_RPAREN);
    add_ast_child(node, statement());

    return node;
}

// do-while语句
static ASTNode* do_while_stat() {
    Token do_token = current_token();
    match(TOKEN_DO);

    ASTNode *node = create_ast_node(AST_DO_WHILE_STMT, "do_while", do_token.line, do_token.column);

    add_ast_child(node, statement());

    match(TOKEN_WHILE);
    match(TOKEN_LPAREN);
    add_ast_child(node, expression());
    match(TOKEN_RPAREN);

    // 可选分号
    if (current_token().type == TOKEN_SEMICOLON) {
        match(TOKEN_SEMICOLON);
    }

    return node;
}

// switch语句
static ASTNode* switch_stat() {
    Token switch_token = current_token();
    match(TOKEN_SWITCH);

    ASTNode *node = create_ast_node(AST_SWITCH_STMT, "switch", switch_token.line, switch_token.column);

    match(TOKEN_LPAREN);
    add_ast_child(node, expression());
    match(TOKEN_RPAREN);

    match(TOKEN_LBRACE);
    
    while (current_token().type == TOKEN_CASE || current_token().type == TOKEN_DEFAULT) {
        if (current_token().type == TOKEN_CASE) {
            match(TOKEN_CASE);
            ASTNode *case_node = create_ast_node(AST_CASE_STMT, "case", current_token().line, current_token().column);
            add_ast_child(case_node, expression());
            match(TOKEN_COLON);
            add_ast_child(case_node, statement_list());
            add_ast_child(node, case_node);
        } else if (current_token().type == TOKEN_DEFAULT) {
            match(TOKEN_DEFAULT);
            ASTNode *default_node = create_ast_node(AST_DEFAULT_STMT, "default", current_token().line, current_token().column);
            match(TOKEN_COLON);
            add_ast_child(default_node, statement_list());
            add_ast_child(node, default_node);
        }
    }

    match(TOKEN_RBRACE);

    return node;
}

// read语句实现
static ASTNode* read_stat() {
    Token read_token = current_token();
    match(TOKEN_READ);

    ASTNode *node = create_ast_node(AST_READ_STMT, "read", read_token.line, read_token.column);

    Token id_token = current_token();
    if (current_token().type != TOKEN_ID) {
        add_error("read语句缺少变量名", read_token.line, read_token.column);
    } else {
        match(TOKEN_ID);
        add_ast_child(node, create_ast_node(AST_IDENTIFIER, id_token.value, id_token.line, id_token.column));
    }

    // 可选分号（按照语法规则{;}）
    if (current_token().type == TOKEN_SEMICOLON) {
        match(TOKEN_SEMICOLON);
    }

    return node;
}

// write语句实现
static ASTNode* write_stat() {
    Token write_token = current_token();
    match(TOKEN_WRITE);

    ASTNode *node = create_ast_node(AST_WRITE_STMT, "write", write_token.line, write_token.column);

    add_ast_child(node, expression());

    // 可选分号（按照语法规则{;}）
    if (current_token().type == TOKEN_SEMICOLON) {
        match(TOKEN_SEMICOLON);
    }

    return node;
}

// break语句实现
static ASTNode* break_stat() {
    Token break_token = current_token();
    match(TOKEN_BREAK);

    ASTNode *node = create_ast_node(AST_BREAK_STMT, "break", break_token.line, break_token.column);

    // 可选分号（按照语法规则{;}）
    if (current_token().type == TOKEN_SEMICOLON) {
        match(TOKEN_SEMICOLON);
    }

    return node;
}

// continue语句实现
static ASTNode* continue_stat() {
    Token continue_token = current_token();
    match(TOKEN_CONTINUE);

    ASTNode *node = create_ast_node(AST_CONTINUE_STMT, "continue", continue_token.line, continue_token.column);

    // 可选分号（按照语法规则{;}）
    if (current_token().type == TOKEN_SEMICOLON) {
        match(TOKEN_SEMICOLON);
    }

    return node;
}

// return语句
static ASTNode* return_stat() {
    Token return_token = current_token();
    match(TOKEN_RETURN);

    ASTNode *node = create_ast_node(AST_RETURN_STMT, "return", return_token.line, return_token.column);

    // 可选的返回表达式
    if (current_token().type != TOKEN_SEMICOLON && 
        current_token().type != TOKEN_RBRACE && 
        current_token().type != TOKEN_EOF) {
        add_ast_child(node, expression());
    }

    // 可选分号
    if (current_token().type == TOKEN_SEMICOLON) {
        match(TOKEN_SEMICOLON);
    }

    return node;
}

// 表达式语句
static ASTNode* expression_stat() {
    ASTNode *node = create_ast_node(AST_EXPR_STMT, "expr_stmt", current_token().line, current_token().column);
    add_ast_child(node, expression());
    return node;
}

// 表达式
static ASTNode* expression() {
    ASTNode *left = bool_expr();
    
    // 处理赋值操作（包括数组元素赋值）
    if (current_token().type == TOKEN_ASSIGN) {
        Token assign_token = current_token();
        advance();
        ASTNode *node = create_ast_node(AST_ASSIGN_EXPR, "=", assign_token.line, assign_token.column);
        add_ast_child(node, left);
        add_ast_child(node, expression());
        return node;
    }
    
    return left;
}

// 布尔表达式（支持 and/or 逻辑运算）
static ASTNode* bool_expr() {
    ASTNode *left = compare_expr();

    // 处理 and/or 逻辑运算
    while (current_token().type == TOKEN_ID && 
           (strcmp(current_token().value, "and") == 0 || strcmp(current_token().value, "or") == 0)) {
        Token op_token = current_token();
        advance();
        ASTNode *node = create_ast_node(AST_BINARY_EXPR, op_token.value, op_token.line, op_token.column);
        add_ast_child(node, left);
        add_ast_child(node, compare_expr());
        left = node;
    }

    return left;
}

// 比较表达式
static ASTNode* compare_expr() {
    ASTNode *left = additive_expr();

    if (current_token().type == TOKEN_GT || current_token().type == TOKEN_LT ||
        current_token().type == TOKEN_GE || current_token().type == TOKEN_LE ||
        current_token().type == TOKEN_EQ || current_token().type == TOKEN_NE) {
        Token op_token = current_token();
        advance();
        ASTNode *node = create_ast_node(AST_BINARY_EXPR, op_token.value, op_token.line, op_token.column);
        add_ast_child(node, left);
        add_ast_child(node, additive_expr());
        return node;
    }

    return left;
}

// 加减表达式
static ASTNode* additive_expr() {
    ASTNode *left = term();

    while (current_token().type == TOKEN_PLUS || current_token().type == TOKEN_MINUS) {
        Token op_token = current_token();
        advance();
        ASTNode *node = create_ast_node(AST_BINARY_EXPR, op_token.value, op_token.line, op_token.column);
        add_ast_child(node, left);
        add_ast_child(node, term());
        left = node;
    }

    return left;
}

// 乘除表达式
static ASTNode* term() {
    ASTNode *left = factor();

    while (current_token().type == TOKEN_MUL || current_token().type == TOKEN_DIV) {
        Token op_token = current_token();
        advance();
        ASTNode *node = create_ast_node(AST_BINARY_EXPR, op_token.value, op_token.line, op_token.column);
        add_ast_child(node, left);
        add_ast_child(node, factor());
        left = node;
    }

    return left;
}

// 因子（错误信息已优化，错误恢复不跳过关键token）
static ASTNode* factor() {
    Token token = current_token();
    switch (token.type) {
        case TOKEN_LPAREN:
            match(TOKEN_LPAREN);
            ASTNode *node = additive_expr();
            match(TOKEN_RPAREN);
            return node;
        case TOKEN_ID: {
            Token id_token = token;
            advance();
            // 检查是否是函数调用
            if (current_token().type == TOKEN_LPAREN) {
                match(TOKEN_LPAREN);
                ASTNode *call_node = create_ast_node(AST_FUNC_CALL, id_token.value, id_token.line, id_token.column);
                // 处理参数列表（允许为空）
                if (current_token().type != TOKEN_RPAREN) {
                    add_ast_child(call_node, expression());
                    while (current_token().type == TOKEN_COMMA) {
                        match(TOKEN_COMMA);
                        add_ast_child(call_node, expression());
                    }
                }
                match(TOKEN_RPAREN);
                return call_node;
            }
            // 检查是否是数组访问
            else if (current_token().type == TOKEN_LBRACKET) {
                match(TOKEN_LBRACKET);
                ASTNode *arr_node = create_ast_node(AST_ARRAY_ACCESS, id_token.value, id_token.line, id_token.column);
                add_ast_child(arr_node, expression()); // 数组索引
                match(TOKEN_RBRACKET);
                return arr_node;
            }
            return create_ast_node(AST_IDENTIFIER, id_token.value, id_token.line, id_token.column);
        }
        case TOKEN_NUM:
            advance();
            return create_ast_node(AST_NUM_LITERAL, token.value, token.line, token.column);
        case TOKEN_STRING:
            advance();
            return create_ast_node(AST_STRING_LITERAL, token.value, token.line, token.column);
        default:
            if (token.type == TOKEN_ERROR) {
                // 词法错误已经在词法分析阶段报告过了，这里不再重复报告
                advance();
                return create_ast_node(AST_NUM_LITERAL, "0", token.line, token.column);
            } else if (token.type == TOKEN_RPAREN || token.type == TOKEN_RBRACE || 
                token.type == TOKEN_EOF || token.type == TOKEN_COMMA ||
                token.type == TOKEN_SEMICOLON) {
                char err_msg[200];
                snprintf(err_msg, sizeof(err_msg), "缺少表达式、标识符或数字, 实际得到 '%s'", token.value);
                add_error(err_msg, token.line, token.column);
                return create_ast_node(AST_NUM_LITERAL, "0", token.line, token.column);
            } else {
                char err_msg[200];
                snprintf(err_msg, sizeof(err_msg), "缺少表达式、标识符或数字, 实际得到 '%s'", token.value);
                add_error(err_msg, token.line, token.column);
                advance();
                return create_ast_node(AST_NUM_LITERAL, "0", token.line, token.column);
            }
    }
}

// 递归输出AST为JSON格式（纯AST，不包含错误信息）
void print_ast_json(FILE *file, ASTNode *node, int indent) {
    if (!node) return;

    // 打印缩进
    for (int i = 0; i < indent; i++) fprintf(file, "  ");
    fprintf(file, "{\n");

    // 节点基本信息
    for (int i = 0; i < indent + 1; i++) fprintf(file, "  ");
    fprintf(file, "\"type\": \"%d\",\n", node->type);

    if (node->value) {
        for (int i = 0; i < indent + 1; i++) fprintf(file, "  ");
        fprintf(file, "\"value\": \"%s\",\n", node->value);
    }

    for (int i = 0; i < indent + 1; i++) fprintf(file, "  ");
    fprintf(file, "\"line\": %d,\n", node->line);
    for (int i = 0; i < indent + 1; i++) fprintf(file, "  ");
    fprintf(file, "\"column\": %d", node->column);

    // 子节点
    if (node->child_count > 0) {
        fprintf(file, ",\n");
        for (int i = 0; i < indent + 1; i++) fprintf(file, "  ");
        fprintf(file, "\"children\": [\n");

        for (int i = 0; i < node->child_count; i++) {
            print_ast_json(file, node->children[i], indent + 2);
            if (i < node->child_count - 1) fprintf(file, ",");
            fprintf(file, "\n");
        }

        for (int i = 0; i < indent + 1; i++) fprintf(file, "  ");
        fprintf(file, "]");
    }

    fprintf(file, "\n");
    for (int i = 0; i < indent; i++) fprintf(file, "  ");
    fprintf(file, "}");
}

// 语法分析主函数（生成纯AST，文件中不包含错误信息）
int syntax_analysis(const char *output_filename, const char *base_name) {
    current_token_index = 0;
    // 重置错误计数，但保留词法分析的错误
    int lex_error_count = error_count;
    error_count = 0;

    // 修复：提前初始化全局根作用域，解决函数声明插入符号时越界
    scope_top = -1;
    global_off = 500;  // 全局变量从高地址500开始
    codesIndex = 0;
    semantic_err = 0;
    scope_enter(); // 全局作用域入栈，scope_top变为0

    printf("\n===== 语法分析错误 =====\n");
    ASTNode *root = program();

    if (error_count == 0) {
        printf("无语法错误\n");
    }

    printf("✅ 语法分析完成，AST已保存到: %s\n", output_filename);

    FILE *ast_file = fopen(output_filename, "w");
    if (!ast_file) {
        perror("无法创建语法树文件");
        free_ast(root);
        return 1;
    }

    // 只写入纯JSON格式的AST，不包含任何错误信息
    fprintf(ast_file, "{\n");
    fprintf(ast_file, "  \"ast\": ");
    print_ast_json(ast_file, root, 1);
    fprintf(ast_file, "\n}\n");
    fclose(ast_file);

    /*********************【语义分析入口】*********************/
    printf("\n===== 语义分析错误 =====\n");
    semantic_translate(root); //AST遍历生成中间汇编代码

    if(semantic_err==0) printf("无语义错误\n");
    else printf("语义错误总数：%d\n",semantic_err);

    //1.输出中间汇编代码 code文件
    char code_name[MAX_FILENAME];
    snprintf(code_name,MAX_FILENAME,"%s_code.txt",base_name);
    FILE *fpcode = fopen(code_name,"w");
    for(int i=0;i<codesIndex;i++){
        fprintf(fpcode,"%-10s %d\n",codes[i].opt,codes[i].operand);
    }
    fclose(fpcode);

    printf("✅ 语义分析完成，结果已保存\n");
    printf("  汇编中间代码：%s\n",code_name);

    free_ast(root);

    // 总错误数 = 词法错误 + 语法错误+语义错误
    return (lex_error_count + error_count + semantic_err) > 0 ? 1 : 0;
}

// 虚拟机函数前向声明
void init_vm();
int load_code(const char *filename);
void execute_vm();

// 虚拟机常量定义
#define MAX_STACK_SIZE 1000
#define MAX_DATA_SIZE 1000
#define MAX_CODE_SIZE 2000
#define MAX_INSTRUCTION_LEN 10

// 虚拟机指令结构体
typedef struct {
    char opt[MAX_INSTRUCTION_LEN];
    int operand;
} Instruction;

// 虚拟机状态结构体
typedef struct {
    int stack[MAX_STACK_SIZE];
    int stack_top;
    int data[MAX_DATA_SIZE];
    int data_top;
    Instruction code[MAX_CODE_SIZE];
    int pc;
    int code_count;
    int base;
    int call_stack[MAX_STACK_SIZE];
    int call_stack_top;
} VM;

// 全局虚拟机实例
VM vm;

// 主函数（已修复strncpy参数顺序错误）
int main(int argc, char *argv[]) {
    char input_filename[MAX_FILENAME];

    setlocale(LC_ALL, "");

    // 获取输入文件名
    if (argc >= 2) {
        // 修复：strncpy(目标, 源, 长度)
        strncpy(input_filename, argv[1], MAX_FILENAME - 1);
        input_filename[MAX_FILENAME - 1] = '\0';
    } else {
        printf("请输入要分析的仓颉源文件名: ");
        if (fgets(input_filename, MAX_FILENAME, stdin) == NULL) {
            fprintf(stderr, "输入错误\n");
            return 1;
        }
        // 去除换行符
        input_filename[strcspn(input_filename, "\n")] = '\0';
    }

    // 检查源文件是否存在
    if (access(input_filename, F_OK) != 0) {
        fprintf(stderr, "错误: 文件 '%s' 不存在\n", input_filename);
        return 1;
    }

    // 提取基础文件名（去除扩展名）
    char base_name[MAX_FILENAME];
    char *dot = strrchr(input_filename, '.');
    if (dot) {
        strncpy(base_name, input_filename, dot - input_filename);
        base_name[dot - input_filename] = '\0';
    } else {
        strncpy(base_name, input_filename, MAX_FILENAME - 1);
        base_name[MAX_FILENAME - 1] = '\0';
    }

    // 生成不重复的输出文件名
    char *tokens_filename = generate_unique_filename(base_name, "_tokens.txt");
    char *ast_filename = generate_unique_filename(base_name, "_ast.json");

    printf("\n开始分析文件: %s \n", input_filename);

    // 词法分析（即使有错误也继续）
    int lex_result = lexical_analysis(input_filename, tokens_filename);
    if (lex_result != 0) {
        printf("\n⚠️ 词法分析存在错误，但继续进行语法分析...\n");
    }

    // 语法+语义分析，传入基础名用于生成语义文件
    int parse_result = syntax_analysis(ast_filename, base_name);
    if (parse_result != 0) {
        printf("\n⚠️ 分析存在错误，跳过虚拟机执行\n");
        // 释放内存
        free(tokens_filename);
        free(ast_filename);
        free_token_list(&token_list);
        return 1;
    }

    printf("\n🎉 分析完成！\n");
    printf(" 单词列表文件: %s\n", tokens_filename);
    printf(" AST语法树文件: %s\n", ast_filename);
    printf(" 中间汇编代码: %s_code.txt\n",base_name);

    // ========== 自动执行虚拟机 ==========
    printf("\n===== 开始执行虚拟机 =====\n");
    
    // 构建中间代码文件名
    char code_filename[MAX_FILENAME];
    snprintf(code_filename, MAX_FILENAME, "%s_code.txt", base_name);
    
    // 初始化虚拟机
    init_vm();
    
    // 加载中间代码
    if (!load_code(code_filename)) {
        printf("无法加载中间代码文件 %s\n", code_filename);
        free(tokens_filename);
        free(ast_filename);
        free_token_list(&token_list);
        return 1;
    }
    
    printf("成功加载 %d 条指令\n", vm.code_count);
    
    // 执行虚拟机
    execute_vm();
    // ========== 虚拟机执行结束 ==========

    // 释放内存
    free(tokens_filename);
    free(ast_filename);
    free_token_list(&token_list);
    return 0;
}

// ==================== 以下是虚拟机代码 ====================
FILE *input_file = NULL;

void init_vm() {
    vm.stack_top = 0;
    vm.pc = 0;
    vm.code_count = 0;
    vm.base = 0;
    vm.data_top = 0;
    vm.call_stack_top = -1;
    for (int i = 0; i < MAX_DATA_SIZE; i++) vm.data[i] = 0;
    for (int i = 0; i < MAX_STACK_SIZE; i++) vm.stack[i] = 0;
}

void push(int value) {
    if (vm.stack_top < MAX_STACK_SIZE - 1) vm.stack[vm.stack_top++] = value;
    else { printf("错误：栈溢出！\n"); exit(1); }
}

int pop() {
    if (vm.stack_top > 0) return vm.stack[--vm.stack_top];
    else { printf("错误：栈下溢！\n"); exit(1); }
}

int load_code(const char *filename) {
    FILE *file = fopen(filename, "r");
    if (!file) { printf("错误：无法打开文件 %s\n", filename); return 0; }

    char line[256];
    while (fgets(line, sizeof(line), file)) {
        char *trimmed = line;
        while (*trimmed == ' ' || *trimmed == '\t' || *trimmed == '\n') trimmed++;
        if (*trimmed == '\0' || *trimmed == '/') continue;
        
        char opt[MAX_INSTRUCTION_LEN];
        int operand = 0;
        
        if (sscanf(line, "%s %d", opt, &operand) == 2) {
            strcpy(vm.code[vm.code_count].opt, opt);
            vm.code[vm.code_count].operand = operand;
            vm.code_count++;
        } else if (sscanf(line, "%s", opt) == 1) {
            strcpy(vm.code[vm.code_count].opt, opt);
            vm.code[vm.code_count].operand = 0;
            vm.code_count++;
        }
    }
    fclose(file);
    return 1;
}

void execute_vm() {
    printf("\n===== 虚拟机开始执行 =====\n\n");
    
    while (vm.pc < vm.code_count) {
        Instruction instr = vm.code[vm.pc];
        char *opt = instr.opt;
        int operand = instr.operand;
        
        if (strcmp(opt, "LOAD") == 0) {
            if (operand < 0) push(vm.data[vm.base + operand]);
            else if (operand >= 500) push(vm.data[operand]);
            else push(vm.data[vm.base + operand + 1]);
            vm.pc++;
        } else if (strcmp(opt, "LOADI") == 0) { push(operand); vm.pc++; }
        else if (strcmp(opt, "LOADA") == 0) {
            int offset = pop();
            push(vm.data[vm.base + operand + offset]);
            vm.pc++;
        } else if (strcmp(opt, "STO") == 0) {
            if (operand < 0) vm.data[vm.base + operand] = vm.stack[vm.stack_top - 1];
            else if (operand >= 500) vm.data[operand] = vm.stack[vm.stack_top - 1];
            else vm.data[vm.base + operand + 1] = vm.stack[vm.stack_top - 1];
            vm.pc++;
        } else if (strcmp(opt, "STOA") == 0) {
            int offset = pop();
            int value = pop();
            vm.data[vm.base + operand + offset] = value;
            vm.pc++;
        } else if (strcmp(opt, "POP") == 0) { pop(); vm.pc++; }
        else if (strcmp(opt, "ADD") == 0) { int b = pop(); int a = pop(); push(a + b); vm.pc++; }
        else if (strcmp(opt, "SUB") == 0) { int b = pop(); int a = pop(); push(a - b); vm.pc++; }
        else if (strcmp(opt, "MULT") == 0) { int b = pop(); int a = pop(); push(a * b); vm.pc++; }
        else if (strcmp(opt, "DIV") == 0) {
            int b = pop(); int a = pop();
            if (b == 0) { printf("错误：除零错误！\n"); return; }
            push(a / b); vm.pc++;
        } else if (strcmp(opt, "BR") == 0) { vm.pc = operand; }
        else if (strcmp(opt, "BRF") == 0) {
            int condition = pop();
            vm.pc = (condition == 0) ? operand : vm.pc + 1;
        } else if (strcmp(opt, "BRT") == 0) {
            int condition = pop();
            vm.pc = (condition != 0) ? operand : vm.pc + 1;
        } else if (strcmp(opt, "EQ") == 0) { int b = pop(); int a = pop(); push(a == b ? 1 : 0); vm.pc++; }
        else if (strcmp(opt, "NOTEQ") == 0) { int b = pop(); int a = pop(); push(a != b ? 1 : 0); vm.pc++; }
        else if (strcmp(opt, "GT") == 0) { int b = pop(); int a = pop(); push(a > b ? 1 : 0); vm.pc++; }
        else if (strcmp(opt, "LES") == 0) { int b = pop(); int a = pop(); push(a < b ? 1 : 0); vm.pc++; }
        else if (strcmp(opt, "GE") == 0) { int b = pop(); int a = pop(); push(a >= b ? 1 : 0); vm.pc++; }
        else if (strcmp(opt, "LE") == 0) { int b = pop(); int a = pop(); push(a <= b ? 1 : 0); vm.pc++; }
        else if (strcmp(opt, "AND") == 0) { int b = pop(); int a = pop(); push((a != 0) && (b != 0) ? 1 : 0); vm.pc++; }
        else if (strcmp(opt, "OR") == 0) { int b = pop(); int a = pop(); push((a != 0) || (b != 0) ? 1 : 0); vm.pc++; }
        else if (strcmp(opt, "NOT") == 0) { int a = pop(); push(a == 0 ? 1 : 0); vm.pc++; }
        else if (strcmp(opt, "IN") == 0) {
            int value;
            if (input_file != NULL) fscanf(input_file, "%d", &value);
            else { printf("请输入整数: "); scanf("%d", &value); }
            push(value); vm.pc++;
        } else if (strcmp(opt, "OUT") == 0) { printf("输出: %d\n", pop()); vm.pc++; }
        else if (strcmp(opt, "STOP") == 0) { printf("\n===== 虚拟机执行结束 =====\n"); return; }
        else if (strcmp(opt, "ENTER") == 0) {
            int param_count = operand / 1000;
            int local_count = operand % 1000;
            vm.data[vm.data_top] = vm.base;
            vm.base = vm.data_top;
            vm.data_top++;
            for (int i = param_count - 1; i >= 0; i--) {
                int arg = pop();
                vm.data[vm.base - param_count + i] = arg;
            }
            for (int i = 0; i < local_count; i++) vm.data[vm.data_top++] = 0;
            vm.pc++;
        } else if (strcmp(opt, "LEAVE") == 0) {
            vm.base = vm.data[vm.base];
            vm.data_top = vm.base;
            vm.pc++;
        } else if (strcmp(opt, "CAL") == 0) {
            if (vm.call_stack_top < MAX_STACK_SIZE - 1) {
                vm.call_stack[++vm.call_stack_top] = vm.pc + 1;
            } else { printf("错误：调用栈溢出！\n"); return; }
            vm.pc = operand;
        } else if (strcmp(opt, "RETURN") == 0) {
            if (vm.call_stack_top >= 0) {
                int return_value = pop();
                vm.base = vm.data[vm.base];
                vm.pc = vm.call_stack[vm.call_stack_top--];
                push(return_value);
            } else { printf("错误：调用栈下溢！\n"); return; }
        } else if (strcmp(opt, "CASE") == 0) {
            int case_value = pop();
            if (vm.stack[vm.stack_top - 1] != case_value) {
                vm.pc = vm.code[vm.pc].operand;
            } else { vm.pc++; }
        } else if (strcmp(opt, "DEFAULT") == 0) { vm.pc++; }
        else if (strcmp(opt, "BREAK") == 0) { vm.pc = operand; }
        else { printf("错误：未知指令 '%s'\n", opt); return; }
    }
    printf("\n===== 虚拟机执行结束（代码执行完毕） =====\n");
}