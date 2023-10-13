#ifndef SEMANT_H_
#define SEMANT_H_

#include <assert.h>
#include <iostream>  
#include <map>
#include <list>
#include "cool-tree.h"
#include "stringtab.h"
#include "symtab.h"
#include "list.h"

#define TRUE 1
#define FALSE 0

class ClassTable;
typedef ClassTable *ClassTableP;

// This is a structure that may be used to contain the semantic
// information such as the inheritance graph.  You may use it or not as
// you like: it is only here to provide a container for the supplied
// methods.

class ClassTable {
private:
  int semant_errors;
  void install_basic_classes();
  ostream& error_stream;

public:
  std::map<Symbol, Class_> classes_list;
  ClassTable(Classes);
  int errors() { return semant_errors; }
  ostream& semant_error();
  ostream& semant_error(Class_ c);
  ostream& semant_error(Symbol filename, tree_node *t);
  void install_classes_lists(Classes classes);
  void check_inheritance(Classes classes);
  bool is_inherit_relations(Symbol child, Symbol parent, Symbol class_name);
  Symbol find_lca(Symbol child, Symbol parent);
  std::list<Symbol> get_inheritance(Symbol class_name, Class_ class_content);
  void insert_methods();
  void check_method_inheritance();
  void check_ast_type();
};


#endif