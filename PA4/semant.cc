#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <unordered_set>
#include <utility>
#include "cool-tree.h"
#include "cool-tree.handcode.h"
#include "semant.h"
#include "utilities.h"
#include <algorithm>


extern int semant_debug;
extern char *curr_filename;

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////
static Symbol 
    arg,
    arg2,
    Bool,
    concat,
    cool_abort,
    copy,
    Int,
    in_int,
    in_string,
    IO,
    length,
    Main,
    main_meth,
    No_class,
    No_type,
    Object,
    out_int,
    out_string,
    prim_slot,
    self,
    SELF_TYPE,
    Str,
    str_field,
    substr,
    type_name,
    val;
//
// Initializing the predefined symbols.
//
static void initialize_constants(void)
{
    arg         = idtable.add_string("arg");
    arg2        = idtable.add_string("arg2");
    Bool        = idtable.add_string("Bool");
    concat      = idtable.add_string("concat");
    cool_abort  = idtable.add_string("abort");
    copy        = idtable.add_string("copy");
    Int         = idtable.add_string("Int");
    in_int      = idtable.add_string("in_int");
    in_string   = idtable.add_string("in_string");
    IO          = idtable.add_string("IO");
    length      = idtable.add_string("length");
    Main        = idtable.add_string("Main");
    main_meth   = idtable.add_string("main");
    //   _no_class is a symbol that can't be the name of any 
    //   user-defined class.
    No_class    = idtable.add_string("_no_class");
    No_type     = idtable.add_string("_no_type");
    Object      = idtable.add_string("Object");
    out_int     = idtable.add_string("out_int");
    out_string  = idtable.add_string("out_string");
    prim_slot   = idtable.add_string("_prim_slot");
    self        = idtable.add_string("self");
    SELF_TYPE   = idtable.add_string("SELF_TYPE");
    Str         = idtable.add_string("String");
    str_field   = idtable.add_string("_str_field");
    substr      = idtable.add_string("substr");
    type_name   = idtable.add_string("type_name");
    val         = idtable.add_string("_val");
}

static ClassTable* classtable;
typedef SymbolTable<Symbol, method_class> MethodEntry;
static std::map<Symbol, MethodEntry> MethodTable;

static SymbolTable<Symbol, Symbol> AttrTable;
 
/*
 * following are some basic helper functions for semant analysis
 */
// used for debug!
static void print_classes(std::map<Symbol, Class_> classes_list)
{
    cout << "=============================" << endl;
    for(auto it = classes_list.begin(); it != classes_list.end(); ++it)
    {
        cout << "<" << it->first <<  ">" << endl;
    }
    cout << "=============================" << endl;
}

static bool is_basic_symbol(Symbol class_name)
{
    return(class_name == Int || class_name == IO || class_name == Object || class_name == Str || class_name == Bool);
}

static bool is_basic_ancestor(Symbol class_name)
{
    return(class_name == Int || class_name == Str || class_name == Bool);
}

/*
 * following are the main content of the semant analyzer!
*/
ClassTable::ClassTable(Classes classes) : semant_errors(0) , error_stream(cerr) {
    if(semant_debug) 
    {
        cout << "************************" << endl;
        std::cout << "Now constructing ClassTable" << endl;
    }

    install_basic_classes();

    if(semant_debug)
    {
        print_classes(classes_list);
    } 
}

void ClassTable::install_basic_classes() {

    // The tree package uses these globals to annotate the classes built below.
    // curr_lineno  = 0;
    Symbol filename = stringtable.add_string("<basic class>");
    
    // The following demonstrates how to create dummy parse trees to
    // refer to basic Cool classes.  There's no need for method
    // bodies -- these are already built into the runtime system.
    
    // IMPORTANT: The results of the following expressions are
    // stored in local variables.  You will want to do something
    // with those variables at the end of this method to make this
    // code meaningful.

    // 
    // The Object class has no parent class. Its methods are
    //        abort() : Object    aborts the program
    //        type_name() : Str   returns a string representation of class name
    //        copy() : SELF_TYPE  returns a copy of the object
    //
    // There is no need for method bodies in the basic classes---these
    // are already built in to the runtime system.

    Class_ Object_class =
	class_(Object, 
	       No_class,
	       append_Features(
			       append_Features(
					       single_Features(method(cool_abort, nil_Formals(), Object, no_expr())),
					       single_Features(method(type_name, nil_Formals(), Str, no_expr()))),
			       single_Features(method(copy, nil_Formals(), SELF_TYPE, no_expr()))),
	       filename);

    // 
    // The IO class inherits from Object. Its methods are
    //        out_string(Str) : SELF_TYPE       writes a string to the output
    //        out_int(Int) : SELF_TYPE            "    an int    "  "     "
    //        in_string() : Str                 reads a string from the input
    //        in_int() : Int                      "   an int     "  "     "
    //
    Class_ IO_class = 
	class_(IO, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       single_Features(method(out_string, single_Formals(formal(arg, Str)),
										      SELF_TYPE, no_expr())),
							       single_Features(method(out_int, single_Formals(formal(arg, Int)),
										      SELF_TYPE, no_expr()))),
					       single_Features(method(in_string, nil_Formals(), Str, no_expr()))),
			       single_Features(method(in_int, nil_Formals(), Int, no_expr()))),
	       filename);  

    //
    // The Int class has no methods and only a single attribute, the
    // "val" for the integer. 
    //
    Class_ Int_class =
	class_(Int, 
	       Object,
	       single_Features(attr(val, prim_slot, no_expr())),
	       filename);

    //
    // Bool also has only the "val" slot.
    //
    Class_ Bool_class =
	class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())),filename);

    //
    // The class Str has a number of slots and operations:
    //       val                                  the length of the string
    //       str_field                            the string itself
    //       length() : Int                       returns length of the string
    //       concat(arg: Str) : Str               performs string concatenation
    //       substr(arg: Int, arg2: Int): Str     substring selection
    //       
    Class_ Str_class =
	class_(Str, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       append_Features(
									       single_Features(attr(val, Int, no_expr())),
									       single_Features(attr(str_field, prim_slot, no_expr()))),
							       single_Features(method(length, nil_Formals(), Int, no_expr()))),
					       single_Features(method(concat, 
								      single_Formals(formal(arg, Str)),
								      Str, 
								      no_expr()))),
			       single_Features(method(substr, 
						      append_Formals(single_Formals(formal(arg, Int)), 
								     single_Formals(formal(arg2, Int))),
						      Str, 
						      no_expr()))),
	       filename);

    classes_list.insert(std::make_pair(Str, Str_class));
    classes_list.insert(std::make_pair(Int, Int_class));
    classes_list.insert(std::make_pair(Object, Object_class));
    classes_list.insert(std::make_pair(IO, IO_class));
    classes_list.insert(std::make_pair(Bool, Bool_class));
}

void ClassTable::install_classes_lists(Classes classes) 
{
    // check:  
    // 1. duplicate class declaration
    // 2. conflict class: SELF_TYPE
    for(int index = classes->first(); classes->more(index); index = classes->next(index))
    {
        Class_ current_class = classes->nth(index);
        Symbol class_name = current_class->get_name();

        if(class_name == SELF_TYPE)
        {
            semant_error(current_class) << "conflict with basic class" << endl;
        }
        else
        {
            // duplicate case
            if(auto search = classes_list.find(class_name); search != classes_list.end())
            {
                if(is_basic_symbol(class_name))
                    semant_error(current_class) << "conflict with basic class" << endl;
                else
                    semant_error(current_class) << "conflict with already exit class" << endl;
            }
            else
            {
                classes_list.insert(std::make_pair(class_name, current_class));
                if(semant_debug) 
                {
                    std::cout << "Successfully insert a new Class Symbol" << class_name << endl;
                }
            }
        }
    }

    // Every cool program must have a Main class, check for that
    if(classes_list.find(Main) == classes_list.end())
        semant_error() << "Class Main is not defined." << endl;

    if(semant_debug)
    {
        print_classes(classes_list);
    }
}

// check inheritance correctness for every Class_ in classes_lists
void ClassTable::check_inheritance(Classes classes) 
{
    if(semant_debug)
    {
        std::cout << endl << "****************************" << endl;
        std::cout << "Check for Class_inheritance correctness" << endl; 
    }
    for(int index = classes->first(); classes->more(index); index = classes->next(index))
    {
        std::unordered_set<Symbol> inheritance_chain;
        Class_ current_class = classes->nth(index);

        Symbol current_class_name = current_class->get_name();
        Symbol class_parent = current_class->get_parent();

        if(semant_debug)
            std::cout << "-----------------------" << endl;

        // according the the class root
        // all class's ancestor is Object class.
        while(class_parent != Object)
        {
            inheritance_chain.insert(current_class_name);
            if(semant_debug)
            {
                std::cout << current_class_name << endl;
                std::cout << class_parent << endl;

                std::cout << "----" << endl;
            }

            // 1. class_parent shouldn't be basic type
            // 2. class_parent should be in the classes_lists
            // 3. acylic
            if(classes_list.find(class_parent) == classes_list.end())
            {
                semant_error(current_class) << "inherits undeclared class" << class_parent << endl;
                break;
            }

            if(is_basic_ancestor(class_parent))
            {
                semant_error(current_class) << "has basic class ancestor, which is out of the rule" << endl;
                break;
            }

            if(auto it = inheritance_chain.find(class_parent); it != inheritance_chain.end())
            {
                semant_error(current_class) << "Error cycle" << endl;
                break;
            }

            current_class = classes_list.find(class_parent)->second;
            current_class_name = current_class->get_name();
            class_parent = current_class->get_parent();
        }

        if(class_parent == Object)
        {
            if(semant_debug)
            {
                std::cout << "no bugs in " << current_class_name << endl;
            }
        }

        if(semant_debug)
                std::cout << "-----------------------" << endl;

        inheritance_chain.clear();
    }

    if(semant_debug)  
    {
        std::cout << "****************************" << endl;
    }
}

// helper function for inheritance list
static void print_inheritance(std::list<Symbol> inheritance_chain)
{
    std::cout<< "inheritance chain is: ";
    for(auto it = inheritance_chain.begin(); it != inheritance_chain.end(); ++it)
    {
        std::cout << *it << endl;
    }
    std::cout<< "Thats all for the inheritance chain" << endl;
}

// get parent list of the given Class_
// end <- Object <- A <- B <- C
// trickey: need to handle if class_name is SELF_TYPE
std::list<Symbol> ClassTable::get_inheritance(Symbol class_name, Class_ class_content)
{ 
    if(class_name == SELF_TYPE)
    {
        class_name = class_content->get_name();
    }

    // first need to check whether class_name is in the classes_lists
    if(classes_list.find(class_name) == classes_list.end())
    {
        semant_error(class_content) << "try to get invalid class's parent lists!" << endl;
    }

    std::list<Symbol> inheritance_list;
    if(class_name == Object)
        return inheritance_list;

    for(; class_name != Object; class_name = classes_list[class_name]->get_parent())
    {
        inheritance_list.push_front(class_name);
    }

    inheritance_list.push_front(Object);

    return inheritance_list;
}

// check whether child <= parent!
// trickey here: need to discuss SELF_TYPE condition when it appears
// either in child or parent!
bool ClassTable::is_inherit_relations(Symbol child, Symbol parent, Symbol class_name)
{
    // patching: something went wrong with this code, if child == parent, return false;
    // awkward code!
    if(child == parent)
        return true;

    if(parent == SELF_TYPE)
    {
        // T
        // so only if we can ensure that child is also SELF_TYPE
        if(child == SELF_TYPE)
            return true;
    }
    else 
    {
       //if(child == SELF_TYPE)
            // SELF_TYPEchild <= parent if child <= parent 
            child = classes_list[class_name]->get_name();
    }

    std::list<Symbol> inheritance_path = get_inheritance(child, classes_list[child]);
    auto it = std::find(inheritance_path.begin(), inheritance_path.end(), parent);
    //auto it = inheritance_path.find(parent);
    if(it != inheritance_path.end())
        return true;
    else
        return false;
}

// find LCA symbol of two class!
// remember that inheritance list is reversed!
// and that every two class: A and B have LCA Object!
Symbol ClassTable::find_lca(Symbol child, Symbol parent) 
{
    // if(semant_debug)
    // {
    //     std::cout << "============== find_lca ===============" << endl;
    //     std::cout << child << "   " << parent;
    // }

    // if(child == parent)
    //     return child;

    // if(semant_debug)
    // {
    //     std::cout << "------------------------------" << endl;
    //     std::cout << "find lca between " << child << " and " << parent << endl;
    // }
    Symbol ancestor = Object;

    std::list<Symbol> child_path = get_inheritance(child, classes_list[child]);
    std::list<Symbol> parent_path = get_inheritance(parent, classes_list[parent]);
    if(semant_debug)
    {
       print_inheritance(child_path);
       print_inheritance(parent_path); 
    }

    auto child_search = child_path.begin();
    auto parent_search = parent_path.begin();

    while(child_search != child_path.end() && parent_search != parent_path.end())
    { 
        if(*child_search == *parent_search)
        {
            // if(semant_debug)
            //     std::cout << "now enter: " << *child_search << "  " << *parent_search << endl;

            ancestor = *child_search;

            ++child_search;
            ++parent_search;
        }
        else 
        {
            break;
        }
    }

    // if(semant_debug)
    // {
    //     std::cout << "result is " << ancestor << endl;
    //     std::cout << "------------------------------" << endl;
    // }

    return ancestor;
}

////////////////////////////////////////////////////////////////////
//
// semant_error is an overloaded function for reporting errors
// during semantic analysis.  There are three versions:
//
//    ostream& ClassTable::semant_error()                
//
//    ostream& ClassTable::semant_error(Class_ c)
//       print line number and filename for `c'
//
//    ostream& ClassTable::semant_error(Symbol filename, tree_node *t)  
//       print a line number and filename
//
///////////////////////////////////////////////////////////////////

ostream& ClassTable::semant_error(Class_ c)
{                                                             
    return semant_error(c->get_filename(),c);
}    

ostream& ClassTable::semant_error(Symbol filename, tree_node *t)
{
    error_stream << filename << ":" << t->get_line_number() << ": ";
    return semant_error();
}

ostream& ClassTable::semant_error()                  
{                                                 
    semant_errors++;                            
    return error_stream;
} 

/* After finishing inserting classes and checking correctness of classes
 * It is time to check features of classes, that is methods and attributes.
*/
// insert all method classes, according to classes_lists fulfilled before!
// trickey: Feature may be attr_class, which has default add_method functions.
void ClassTable::insert_methods()
{
    if(semant_debug)
    {
        std::cout << "================= start method checking! ===================" << endl;    
    }

    for(auto it = classes_list.begin(); it != classes_list.end(); ++it)
    {
        Symbol class_name = it->first;
        Class_ class_content = it->second;

        if(semant_debug)
        {
            std::cout << "Now checking class: " << class_name << endl;
        }

        // remember to go into the scope of the class
        // symbol table used!
        MethodTable[class_name].enterscope();

        // need to walk through all elements in the Feature list!
        Features feature_list = class_content->get_features();
        for(int index = feature_list->first(); feature_list->more(index); index = feature_list->next(index))
        {
            Feature current_feature = feature_list->nth(index);
            current_feature->add_method(class_name, class_content);
        }
    }

    if(semant_debug)
    {
        std::cout << "================= end method checking! ===================" << endl;    
    }
}

// check if:
// class A inherits class B
// the method C of A must be the same with method C of B
void ClassTable::check_method_inheritance()
{
    if(semant_debug)
    {
        std::cout << "================= start method inheritance checking! ===================" << endl;    
    }

    // traverse the classes_list to get the <Symbol, Class_> pair.
    for(auto it = classes_list.begin(); it != classes_list.end(); ++it)
    {
        Symbol current_name = it->first;
        Class_ current_content = classes_list[current_name];
        
        if(semant_debug)
        {
            std::cout << "current class is " << current_name << endl;
        }

        // get features of the current class
        Features feature_list = current_content->get_features();
        for(int index = feature_list->first(); feature_list->more(index); index = feature_list->next(index))
        {
            Feature current_feature= feature_list->nth(index);
            // specifically check method feature!
            if(current_feature->is_method())
            {
                method_class* current_method = (method_class*) current_feature;
                std::list<Symbol> inherit_chain = get_inheritance(current_name, current_content);

                if(semant_debug)
                {
                    std::cout << "get inheritance chain of " << current_name << endl;
                    print_inheritance(inherit_chain);
                }

                for(auto it = inherit_chain.begin(); it != inherit_chain.end(); ++it)
                {
                    Symbol parent_name = *it;
                    method_class* parent_method = MethodTable[parent_name].lookup(current_method->get_name());
                    if(parent_method != NULL)
                    {
                        if(semant_debug)
                        {
                            std::cout << "***************************" << endl;
                            std::cout << "find method checking between parent and child" << endl;
                            std::cout << "parent: " << parent_method->get_name() << endl;
                            std::cout << "child: " << current_method->get_name() << endl;
                            std::cout << "***************************" << endl;
                        }

                        Formals current_formal = current_method->get_formals();
                        Formals parent_formal = parent_method->get_formals();

                        // check Formal lists sequence and number!
                        int s1 = current_formal->first();
                        int s2 = parent_formal->first();
                        for(; current_formal->more(s1) && parent_formal->more(s2); s1 = current_formal->next(s1) , s2 = parent_formal->next(s2))
                        {
                            // check lists type sequence! naming is not essential
                            if(current_formal->nth(s1)->get_type() != parent_formal->nth(s2)->get_type())
                            {
                                    semant_error(current_content) << "wrong method inheritance(sequence) between " << current_name << " and " << parent_name <<" in " << current_feature->get_name() << endl;
                            }
                        }

                        if(current_formal->more(s1) || parent_formal->more(s2))
                        {
                            semant_error(current_content) << "wrong method inheritance(number) between " << current_name << " and " << parent_name <<" in " << current_feature->get_name() << endl; 
                        }

                        if(semant_debug)
                        {
                            std::cout << "method inheritance succeed!" << endl;
                        }
                    }
                }
            }
        }
    }
    
    if(semant_debug)
    {
        std::cout << "================= end method inheritance checking! ===================" << endl;    
    }
}

// goal of this function:  
// 1. enter all classes
// 2. enter all scope
// 3. check each scope's type expression
// 4. exit scope recursively
// what is important is that:
// A <= B <= C <= D
// So A may use attr from B , C or D
// So need to get an inheritance chain, and reserve a Scope list environment!
void ClassTable::check_ast_type() 
{
    if(semant_debug)
    {
        std::cout << "****************** check_ast_type phase ********************" << endl;
    }

    // step1: enter all classes
    for(auto search = classes_list.begin(); search != classes_list.end(); ++search)
    {
        Symbol class_name = search->first;
        Class_ class_content = search->second;

        // get the inheritance list
        std::list<Symbol> inheritance_path = get_inheritance(class_name, class_content);

        // get all the AttrTable!
        // key: inheritance_path is reverse ordered!
        for(auto search = inheritance_path.begin(); search != inheritance_path.end(); ++search)
        {
            AttrTable.enterscope();
            Class_ current_class = classes_list[*search];
            Features feature_list = current_class->get_features();

            // go over all the feature_list of class
            // and add all attr to the current scope
            // and as we have override check_feature for both method_class and attr_class
            // we can use it to do basic type_checking.
            for(int index = feature_list->first(); feature_list->more(index); index = feature_list->next(index))
            {
                Feature current_feature = feature_list->nth(index);
                current_feature->add_attr(class_name, class_content);
            }
        }

        // as we have a scope structure for attr
        // we should check it for the current class!
        Features feature_list = class_content->get_features();
        for(int index = feature_list->first(); feature_list->more(index); index = feature_list->next(index))
        {
            Feature current_feature = feature_list->nth(index);
            current_feature->check_feature(class_name);
        }

        // don't forget to exitscope
        for(int i = 0; i < inheritance_path.size(); i++)
            AttrTable.exitscope();
    } 

    if(semant_debug)
    {
        std::cout << "***************** check_ast_type phase *********************" << endl;
    }
}

// helper function
// override add_method and add_attr methods for method_class and attr_class
// remember that: symbol, formals and expr are pointers, so need to copy one!
void method_class::add_method(Symbol class_name, Class_ class_ins)
{
    // need to check if there is already the same name methods in a class
    // as a class feature consists a specific attr and method!
    if(MethodTable[class_name].lookup(name) != NULL)
        classtable->semant_error(class_ins) << "error!" << "duplicate method" << name << endl;

    MethodTable[class_name].addid(this->name, new method_class(copy_Symbol(this->name), formals->copy_list(), copy_Symbol(this->return_type), expr->copy_Expression()));
    
    if(semant_debug)
    {
        std::cout << "add method " << this->name << endl;
    }
}

void method_class::add_attr(Symbol class_name, Class_ class_ins) { }

void attr_class::add_method(Symbol class_name, Class_ class_ins) { }

// but it is an error to assign to self or to bind self in a let, a
// case, or as a formal parameter. It is also illegal to have attributes named self.
void attr_class::add_attr(Symbol class_name, Class_ class_ins)
{
    if(semant_debug)
    {
        std::cout << "add attribute to attr_class" << class_name << endl;
    }

    if(this->name == self)
        classtable->semant_error(class_ins) << "self can not be attribute" << endl;
    
    // need to check if there is already the same name attributes in a class
    // as a class feature consists a specific attr and method!
    if(AttrTable.lookup(name) != NULL)
        classtable->semant_error(class_ins) << "error!" << "duplicate attr" << name << endl;
    
    AttrTable.addid(this->name, new Symbol(type_decl));
}

/**
 * type checking functions!
*/

/**
 * SELF_TYPE: 
 * may be used in the following places: new SELF TYPE, as the return type of a
 * method, as the declared type of a let variable, or as the declared type of an attribute. No other uses of
 * SELF TYPE are permitted.    
 *
*/

// check feature for method_class and attr_class
// these two are type checking, need to fulfill helper typedchecking of class inherited from 
// Expression_class.
// Symbol name;
// Formals formals;
// Symbol return_type;
// Expression expr;
//
// quite trickey here:
// 1. need to add all formal into AttrTable to get correct expr->check_expr
// 2. need to check return_type and expr->check_expr inheritance, be sure to solve
// return_type = SELF_TYPE condition.
// 3. all formals should have different names!
void method_class::check_feature(Symbol class_name)
{
    bool is_valid_type = TRUE;

    if(semant_debug)
    {
        std::cout << "=============== checking method_class feature =============" << endl;
    }

    if(semant_debug)
        print_classes(classtable->classes_list);

    Class_ class_content = classtable->classes_list[class_name];

    // need to check whether return_type is an valid type_name;
    Symbol return_type = return_method_type();
    if(semant_debug)
        std::cout << "======== return type: " << return_type << " =============" << endl;
    if(auto search = classtable->classes_list.find(return_type); search == classtable->classes_list.end())
    {
        if(return_type != SELF_TYPE)
        {
            is_valid_type = false;
            classtable->semant_error()<< "Undefined return type  " << return_type << " in method " << get_name() <<"."<< endl;
        }
    }

    // need to add self and all id formals into environment!
    AttrTable.enterscope();
    AttrTable.addid(self, new Symbol(SELF_TYPE));

    // need to check duplicate formals id_name!
    std::unordered_set<Symbol> formal_name;
    for(int index = formals->first(); formals->more(index); index = formals->next(index))
    {
        Formal formal_instance = formals->nth(index);
        Symbol formal_n = formal_instance->get_name();
        Symbol formal_type = formal_instance->get_type();

        // duplicate name!
        if(auto search = formal_name.find(formal_n); search != formal_name.end())
        {
            classtable->semant_error(class_content) << "Duplicate formal_id in method " << get_name() << endl;
        } 
        else
            formal_name.insert(formal_n);

        // check whether formal_type is a valid class_name!
        if(auto search = classtable->classes_list.find(formal_type); search == classtable->classes_list.end())
        {
            classtable->semant_error(class_content) << "Invalid formal type in method: " << get_name() << endl;
        }

        if(formal_n == self)
        {
           classtable->semant_error(class_content) << "Invalid formal name self: " << get_name() << endl; 
        }

        // adding attributes to AttrTable!
        AttrTable.addid(formal_n, new Symbol(formal_type));
    }


    // check whether actual_type conform to return_type.
    Symbol actual_type = expr->check_expr(class_name);

    // trickey here:
    // if return_type == SELF_TYPE
    // then actual_return should also be SELF_TYPE, so shouldn't change return_type!
    if(return_type == SELF_TYPE)
    {
        return_type = class_name;
    }

    // according to the returntypenoexist.test
    // if return_type is undefined type
    // shouldn't do inheritance checking!
    if(is_valid_type)
    {
        if(!classtable->is_inherit_relations(actual_type, return_type, class_name))
        {
            if(actual_type != No_type) 
            {
                std::cout << "*** " << get_name() << " ***" << endl;
                std::cout << "actual_type and return type is " << actual_type << " " << return_type << endl;
                
                classtable->semant_error(class_content) << "return_type and actual type mismatch in method: " << get_name() << endl;
            }
        }
    }

    AttrTable.exitscope();

    if(semant_debug)
    {
        std::cout << "============== end method_class feature ============" << endl;
    }
}

/*
Symbol name;
Symbol type_decl;
Expression init;
*/
void attr_class::check_feature(Symbol class_name)
{
    if(semant_debug)
    {
        std::cout << "=============== checking attr_class feature =============" << endl;
    }

    Class_ class_content = classtable->classes_list[class_name];
    Symbol decl_type = get_type_decl();
    AttrTable.enterscope();
    AttrTable.addid(self, new Symbol(SELF_TYPE));

    Symbol init_type = init->check_expr(class_name);
    // need to judge whether is Attr-Init or Attr-No-Init.
    if(init_type != No_type)
    {
        if(decl_type == SELF_TYPE)
        {
            classtable->semant_error(class_content) << "Can't user SELF_TYPE in attributes!" << endl;
        }
        else 
        {
            if(!classtable->is_inherit_relations(init_type, decl_type, class_name))
            {
                classtable->semant_error(class_content) << "dismatch in attr init!" << endl; 
            }
        }
    }

    AttrTable.exitscope();

    if(semant_debug)
    {
        std::cout << "============== end attr_class feature ============" << endl;
    }
}

// ==================================================================
// helper type checking functions
Symbol assign_class::check_expr(Symbol class_name)
{
    if(semant_debug)
        std::cout << "+++++++++++++++ assign_class::check_expr ++++++++++++" << endl;
    Class_ class_content = classtable->classes_list[class_name];

    // assign_class has two private value: name and expr
    // remember that AttrTable has <name, attr_class> which 
    // has typedecl , need to check with expr inference type!
    Symbol* id_attr = AttrTable.lookup(name);

    // according to self-assignment.test: shouldn't assign to self id!
    if(name == self)
    {
        classtable->semant_error(class_content) << "Cannot assign to 'self'." << endl;
    }

    if(id_attr == NULL)
    {
        classtable->semant_error(class_content) << "target id not in attrtable: " << name << endl;
        type = Object;
        return type;
    }

    Symbol id_symbol = *id_attr;
    Symbol infer_symbol = expr->check_expr(class_name);

    if(!classtable->is_inherit_relations(infer_symbol, id_symbol, class_name))
    {
        if(semant_debug)
        {
            std::cout << "infer_symbol and id_symbol is " << infer_symbol << " " << id_symbol << endl;
            print_inheritance(classtable->get_inheritance(infer_symbol, classtable->classes_list[infer_symbol]));
        }
        // infer_class dismatch id_symbol;
        classtable->semant_error(class_content) << "not a match in assign class: " << id_symbol << " " << infer_symbol << endl;

        // for error handling, assign type to be Object, which will transfer error up to the 
        // root of the AST tree!
        type = Object;
        return type;
    }

    type = infer_symbol;

    if(semant_debug)
        std::cout << "+++++++++++++++ assign_class::check_expr ++++++++++++" << endl;

    return type;
}

/*
   Expression expr;
   Symbol name;
   Expressions actual;
*/
Symbol dispatch_class::check_expr(Symbol class_name)
{
    bool wrong = false;

    // first need to check T0 <= T, that is expr->check_expr() <= type_name
    Class_ class_content = classtable->classes_list[class_name];
    Symbol call_type = expr->check_expr(class_name); 

    // then need to find method in type_name's inherit lists
    // find function pattern!
    std::list<Symbol> inherit_path; 
    if(call_type == SELF_TYPE)
        inherit_path = classtable->get_inheritance(call_type, classtable->classes_list[class_name]);
    else
        inherit_path = classtable->get_inheritance(call_type, classtable->classes_list[call_type]); 
    
    method_class* method = NULL;
    for(auto search = inherit_path.begin(); search != inherit_path.end(); ++search)
    {
        // check method_function in MethodTable, in class >= type_name
        if((method = MethodTable[*search].lookup(name)) != NULL)
        {
            break;
        }
    }

    if(method == NULL)
    {
        wrong = true;
        classtable->semant_error(class_content) << "Wrong in dispatch_class in search for method" << endl;
    }
    else 
    {
        // check for actual lists!
        Formals static_formals = method->get_formals();
        for(int index = actual->first(); actual->more(index); index = actual->next(index))
        {
            Symbol actual_type = actual->nth(index)->check_expr(class_name);
            Symbol ideal_type = static_formals->nth(index)->get_type();
            if(!classtable->is_inherit_relations(actual_type, ideal_type, class_name))
            {
                wrong = true;
                classtable->semant_error(class_content) << "Wrong in dispatch_class in fromal mismatch" << endl;
                break;
            }
        }
    }

    if(wrong)
    {
        type = Object;
        return type;
    }
    else 
    {
        // according to manual, if Tn+1 is SELF_TYPE, that is actual return type 
        // is SELF_TYPE, then should return actual T0;
        if(method->return_method_type() == SELF_TYPE)
        {
            type = call_type;
            return type;
        }
        else 
        {
            type = method->return_method_type();
            return type;
        }
    } 
}

/**
   Expression expr;
   Symbol type_name;
   Symbol name;
   Expressions actual;
*/
Symbol static_dispatch_class::check_expr(Symbol class_name)
{
    if(semant_debug)
    {
        std::cout << "++++++++++++++ static_dispatch_class::check_expr() ++++++++++++++" << endl;
    }
    bool error = false;

    // first need to check T0 <= T, that is expr->check_expr() <= type_name
    Class_ class_content = classtable->classes_list[class_name];
    Symbol call_type = expr->check_expr(class_name);

    if(!classtable->is_inherit_relations(call_type, type_name, class_name))
    {
        if(semant_debug)
        {
            Class_ call_content = classtable->classes_list[call_type];
            print_inheritance(classtable->get_inheritance(call_type, call_content));
            std::cout << "call_type and type_name mismatch:  " << endl;
            std::cout << "[" << call_type << " " << type_name << "]" << endl; 
        }
        error = true;
        classtable->semant_error(class_content) << "Error in static_dispatch_class: call_type mismatch" << endl;
    }

    // then need to find method in type_name's inherit lists
    // find function pattern!
    std::list<Symbol> inherit_path = classtable->get_inheritance(type_name, classtable->classes_list[type_name]);
    method_class* method = NULL;
    for(auto search = inherit_path.begin(); search != inherit_path.end(); ++search)
    {
        // check method_function in MethodTable, in class >= type_name
        if((method = MethodTable[*search].lookup(name)) != NULL)
        {
            break;
        }
    }

    if(method == NULL)
    {
        error = true;
        classtable->semant_error(class_content) << "Wrong in static_dispatch_class in search for method" << endl;
    }
    else 
    {
        // check for actual lists!
        Formals static_formals = method->get_formals();
        for(int index = actual->first(); actual->more(index); index = actual->next(index))
        {
            Symbol actual_type = actual->nth(index)->check_expr(class_name);
            Symbol ideal_type = static_formals->nth(index)->get_type();
            if(!classtable->is_inherit_relations(actual_type, ideal_type, class_name))
            {
                if(semant_debug)
                {
                    std::cout << "actual_type and ideal_type mismatch in formal " << endl;
                    std::cout << "[" << actual_type << " " << ideal_type << "]" << endl; 
                }
                error = true;
                classtable->semant_error(class_content) << "Wrong in static_dispatch_class in fromal mismatch" << endl;
                break;
            }
        }
    }

    if(error)
    {
        type = Object;
        return type;
    }
    else 
    {
        // according to manual, if Tn+1 is SELF_TYPE, that is actual return type 
        // is SELF_TYPE, then should return actual T0;
        if(method->return_method_type() == SELF_TYPE)
        {
            type = call_type;
            return type;
        }
        else 
        {
            type = method->return_method_type();
            return type;
        }
    }

    if(semant_debug)
    {
        std::cout << "++++++++++++++ static_dispatch_class::check_expr() ++++++++++++++" << endl;
    }
}

// need to reserve AttrTable
// but it is an error to assign to self or to bind self in a let, a
// case, or as a formal parameter. It is also illegal to have attributes named self.
/*
   Symbol identifier;
   Symbol type_decl;
   Expression init;
   Expression body;
*/
Symbol let_class::check_expr(Symbol class_name)
{
    Class_ class_content = classtable->classes_list[class_name];

    AttrTable.enterscope();
    Symbol init_type = init->check_expr(class_name);
    AttrTable.addid(identifier, new Symbol(type_decl));

    if(identifier == self)
    {
       classtable->semant_error(class_content) << "Wrong in let_class in binding self to let" << endl;  
    }

    if(init_type != No_type)
    {
        if(type_decl == SELF_TYPE)
        {
            if(!classtable->is_inherit_relations(init_type, class_name, class_name))
            {
            classtable->semant_error(class_content) << "Wrong in let_class in init mismatch" << endl; 
            }
        }
        else 
        {
            if(!classtable->is_inherit_relations(init_type, type_decl, class_name))
            {
                classtable->semant_error(class_content) << "Wrong in let_class in init mismatch" << endl; 
            }
        }
    } 

    type = body->check_expr(class_name);
    AttrTable.exitscope();

    return type;
}

// <id1> : <type1> => <expr1>;
//
// Symbol name;
// Symbol type_decl;
// Expression expr;

//  but it is an error to assign to self or to bind self in a let, a
// case, or as a formal parameter. It is also illegal to have attributes named self.
Symbol branch_class::check_branch(Symbol class_name)
{
   if(semant_debug)
   {
        std::cout << "------- arriving at branch_class! ----------" << endl;
   }
   Class_ class_content = classtable->classes_list[class_name];
   if(name == self)
        classtable->semant_error(class_content) << "error in bind self to case" << endl;
   AttrTable.enterscope();

   AttrTable.addid(name, new Symbol(type_decl));
   Symbol return_type = expr->check_expr(class_name);

   AttrTable.exitscope(); 

   if(semant_debug)
   {
        std::cout << "------- leaving branch_class! ----------" << endl;
   }

   return return_type;
}

// case <expr0> of
//      branch0
//      branch1
//    
// Expression expr;
// Cases cases;
//
// 1. need to make sure that no type has the same type!
// 2. need to make LCA for n-1 type!
Symbol typcase_class::check_expr(Symbol class_name)
{
    Symbol expr_type = expr->check_expr(class_name);
    if(semant_debug)
        std::cout << "arrived at typecase_class::check_expr" << endl;
    Class_ current_class = classtable->classes_list[class_name];

    std::unordered_set<Symbol> decl_bench;
    std::unordered_set<Symbol> actual_bench;

    // find duplicate decl type!
    for(int index = cases->first(); cases->more(index); index = cases->next(index))
    {
        branch_class* temp = (branch_class*) cases->nth(index);
        Symbol decl_type=  temp->get_type_decl();
        Symbol actual_type = temp->check_branch(class_name);
        if(auto search = decl_bench.find(decl_type) != decl_bench.end())
        {
            classtable->semant_error(current_class) << "duplicate decl_type in typecase" << endl;
        }

        decl_bench.insert(decl_type);
        actual_bench.insert(actual_type);
    }

    type = *actual_bench.begin();
    for(auto search = actual_bench.begin(); search != actual_bench.end(); ++search)
    {
        if(semant_debug)
            std::cout << type << endl;
        type = classtable->find_lca(*search, type);
        if(semant_debug)
        {
            std::cout << "(-----------------)" << endl;
            std::cout << type << "  " << *search << endl;
            std::cout << "(-----------------)" << endl;
        }
    }

    if(semant_debug)
    {
       std::cout << "leaving typecase_class::check_expr" << endl; 
       std::cout << type << endl;
    } 

    return type;
}

// two cases for new, one for new SELF_TYPE and one for any other form!
Symbol new__class::check_expr(Symbol class_name)
{
    Class_ current_class = classtable->classes_list[class_name];
    if(type_name != SELF_TYPE)
    {
        if(auto it = classtable->classes_list.find(type_name); it == classtable->classes_list.end())
        {
            classtable->semant_error(current_class) << "'new' used with undefined class " << type_name << "." << endl;
            type = Object;
            return type;
        }
    }
    
    // SELF_TYPE may refer to the class C which it appears or any class conform to C!
    // propagate the type checking!
    // don't forget to decorate the AST tree!
    type = type_name;

    return type;
}

// pred should be Bool
// join(then_exp, else_exp): using lca method!
Symbol cond_class::check_expr(Symbol class_name)
{
    if(semant_debug)
     std::cout << "+++++++++++ cond_class::check_expr +++++++++++++" << endl;

    Class_ class_content = classtable->classes_list[class_name];

    Symbol pred_type = pred->check_expr(class_name);
    Symbol then_type = then_exp->check_expr(class_name);
    Symbol else_type = else_exp->check_expr(class_name);

    if(pred_type != Bool)
    {
        classtable->semant_error(class_content) << "Error in cond_class" << endl;
        type = Object;
        return type;
    }

    if(semant_debug)
    {
        std::cout << then_type << "  " << else_type << endl;
    }

    type = classtable->find_lca(then_type, else_type);

    if(semant_debug)
        std::cout << "+++++++++++ cond_class::check_expr +++++++++++++" << endl;
    return type;
}

// The return value of the Block is the last expression
Symbol block_class::check_expr(Symbol class_name)
{
    for(int index = body->first(); body->more(index); index = body->next(index))
    {
        type = (body->nth(index))->check_expr(class_name);
    }

    return type;
}

// If the predicate is false, the loop terminates and void is returned.
// The predicate must have static type Bool. 
// The body may have any static type. 
// The static type of a loop expression is Object.
Symbol loop_class::check_expr(Symbol class_name)
{
    Class_ class_content = classtable->classes_list[class_name];
    Symbol type1 = pred->check_expr(class_name);
    Symbol type2 = body->check_expr(class_name);

    if(type1 != Bool)
    {
       classtable->semant_error(class_content) << "Error in loop_class" << endl; 
    }

    type = Object;
    return type;
}

// ========================================
// trickey here: type can't inherit int, Str or Bool, so can't be SELF_TYPE;
// type rules for operations: rules see 7.12
Symbol plus_class::check_expr(Symbol class_name)
{
    Class_ class_content = classtable->classes_list[class_name];
    Symbol type1 = e1->check_expr(class_name);
    Symbol type2 = e2->check_expr(class_name);

    if(type1 != Int || type2 != Int)
    {
        classtable->semant_error(class_content) << "Error in plus_class" << endl;
        type = Object;
        return type;
    }

    type = Int;
    return type;
}

Symbol sub_class::check_expr(Symbol class_name)
{
    Class_ class_content = classtable->classes_list[class_name];
    Symbol type1 = e1->check_expr(class_name);
    Symbol type2 = e2->check_expr(class_name);

    if(type1 != Int || type2 != Int)
    {
        classtable->semant_error(class_content) << "Error in sub_class" << endl;
        type = Object;
        return type;
    }

    type = Int;
    return type;
}

Symbol divide_class::check_expr(Symbol class_name)
{
    Class_ class_content = classtable->classes_list[class_name];
    Symbol type1 = e1->check_expr(class_name);
    Symbol type2 = e2->check_expr(class_name);

    if(type1 != Int || type2 != Int)
    {
        classtable->semant_error(class_content) << "Error in divide_class" << endl;
        type = Object;
        return type;
    }

    type = Int;
    return type;
}

Symbol mul_class::check_expr(Symbol class_name)
{
    Class_ class_content = classtable->classes_list[class_name];
    Symbol type1 = e1->check_expr(class_name);
    Symbol type2 = e2->check_expr(class_name);

    if(type1 != Int || type2 != Int)
    {
        classtable->semant_error(class_content) << "Error in mul_class" << endl;
        type = Object;
        return type;
    }

    type = Int;
    return type;
}

Symbol neg_class::check_expr(Symbol class_name)
{
    Class_ class_content = classtable->classes_list[class_name];
    Symbol type1 = e1->check_expr(class_name);
    if(type1 != Int)
    {
        classtable->semant_error(class_content) << "Error in check_class" << endl;
        type = Object;
        return type;
    } 

    type = Int;
    return type;
}

// The wrinkle in the rule for equality is that any types may be freely compared except Int, String
// and Bool, which may only be compared with objects of the same type. 
Symbol eq_class::check_expr(Symbol class_name)
{
    Class_ class_content = classtable->classes_list[class_name];
    Symbol type1 = e1->check_expr(class_name);
    Symbol type2 = e2->check_expr(class_name);

    if(!((type1 == Int && type2 == Int) ||
         (type1 == Bool && type2 == Bool) ||
         (type1 == Str && type2 == Str)))
    {
        if(type1 == Int || type1 == Bool || type2 == Str)
        {
            classtable->semant_error(class_content) << "Error in eq_class" << endl;
            type = Object;
            return type;
        }
    }

    type = Bool;
    return type;
}

Symbol lt_class::check_expr(Symbol class_name)
{
    Class_ class_content = classtable->classes_list[class_name];
    Symbol type1 = e1->check_expr(class_name);
    Symbol type2 = e2->check_expr(class_name);

    if(type1 != Int || type2 != Int)
    {
        classtable->semant_error(class_content) << "Error in lt_class" << endl;
        type = Object;
        return type;
    }

    type = Bool;
    return type;
}

Symbol leq_class::check_expr(Symbol class_name)
{
    Class_ class_content = classtable->classes_list[class_name];
    Symbol type1 = e1->check_expr(class_name);
    Symbol type2 = e2->check_expr(class_name);

    if(type1 != Int || type2 != Int)
    {
        classtable->semant_error(class_content) << "Error in leq_class" << endl;
        type = Object;
        return type;
    }

    type = Bool;
    return type;
}

Symbol comp_class::check_expr(Symbol class_name)
{
    Class_ class_content = classtable->classes_list[class_name];
    if(e1->check_expr(class_name) != Bool)
    {
        classtable->semant_error(class_content) << "Error in comp_class" << endl;
        type = Object;
        return type;
    }

    type = Bool;
    return type;
}

// ========================================
// type rules for constants:  
Symbol bool_const_class::check_expr(Symbol class_name)
{
    if(semant_debug)
        std::cout << "arriving at bool type in class" << class_name << endl;
    // decorate the AST tree
    type = Bool;
    return type;
}

Symbol int_const_class::check_expr(Symbol class_name)
{
    if(semant_debug)
        std::cout << "arriving at int type in class" << class_name << endl;
    type = Int;
    return type;
}

Symbol string_const_class::check_expr(Symbol class_name)
{
    if(semant_debug)
        std::cout << "arriving at string type in class" << class_name << endl;

    type = Str;
    return type;
}

Symbol no_expr_class::check_expr(Symbol class_name)
{
    if(semant_debug)
        std::cout << "arriving at no_type type in class" << class_name << endl;

    type = No_type;
    return type;
}

// don't forget to check expr, as need to decorate the AST tree
Symbol isvoid_class::check_expr(Symbol class_name)
{
    e1->check_expr(class_name);
    type = Bool;
    return type;
}

// O(id) = T -> O,M,C |- Id: T
// need to search AttrTable for T
// trickey : O,M,C |- self: SELF_TYPEc
Symbol object_class::check_expr(Symbol class_name)
{
    if(name == self)
    {
        type = SELF_TYPE;
        return type;
    }

    Class_ class_content = classtable->classes_list[class_name];

    Symbol* target_attr = AttrTable.lookup(name);
    if(target_attr == NULL)
    {
        classtable->semant_error(class_content)<< "No object id in attribute!: " << name << endl; 
        type = Object;
        return type;
    }

    Symbol id_type = *target_attr;
    type = id_type;

    return type;
}

/*   This is the entry point to the semantic checker.

     Your checker should do the following two things:

     1) Check that the program is semantically correct
     2) Decorate the abstract syntax tree with type information
        by setting the `type' field in each Expression node.
        (see `tree.h')

     You are free to first do 1), make sure you catch all semantic
     errors. Part 2) can be done in a second stage, when you want
     to build mycoolc.
 */
void program_class::semant()
{
    initialize_constants();

    /* ClassTable constructor may do some semantic analysis */
    classtable = new ClassTable(classes);
    /* some semantic analysis code may go here */
    if (classtable->errors()) {
	cerr << "Compilation halted due to static semantic errors." << endl;
	exit(1);
    }

    classtable->install_classes_lists(classes);
    if (classtable->errors()) {
	    cerr << "Compilation halted due to static semantic errors." << endl;
	    exit(1);
    } 
    classtable->check_inheritance(classes); 
    if (classtable->errors()) {
	    cerr << "Compilation halted due to static semantic errors." << endl;
	    exit(1);
    }

    classtable->insert_methods();
    classtable->check_method_inheritance();
    classtable->check_ast_type();

    if (classtable->errors()) {
	cerr << "Compilation halted due to static semantic errors." << endl;
	exit(1);
    } 
}


