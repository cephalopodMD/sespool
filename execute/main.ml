(* acl3qb, bgj4uc *)
open Printf;;
module StringMap = Map.Make(String);;
module IntMap = Map.Make(struct type t = int let compare = compare end);;
(***********
 * Classes  
 **********)

class expression_node = 
    object(self)
        val mutable name = ""
        method get_name = name
        method set_name n = name <- n
        val mutable line = 0
        method get_line = line
        method set_line l = line <- l
        val mutable nextExprs = ( [] : expression_node list )
        method get_nextExprs = nextExprs
        method set_exprs e = nextExprs <- e
        method add_expr e = nextExprs <- nextExprs @ e
        val mutable attributes = ( [] : string list)
        method get_attrs = attributes
        method set_attrs a = attributes <- a
    end;;

class cool_class = 
    object(self)
        val mutable name = ""
        val mutable attributes = ( [] : string list ) (* change to attribute type from class map *)
        val mutable initializers = ( [] : expression_node list ) (* The expression trees to initialize respective attributes *)
        val mutable types = ( [] : string list ) (* change to method type from implementation map*)
        method set_name new_name = 
            name <- new_name
        method get_name = name
        method add_attr new_attr =
            attributes <- new_attr :: attributes
        method get_attrs = attributes
        method get_initializers = initializers
        method set_inititalizers init_list = 
            initializers <- init_list
        method add_initializer new_initializer =
            initializers <- new_initializer :: initializers
        method add_type new_types =
            types <- (new_types :: types)
        method get_types =
            types
    end;;

class method_signature = 
    object(self)
        val mutable handle = ""
        val mutable className = ""
        val mutable internal = false
        val mutable param_names = ( [] : string list ) (* change to attribute type from class map *)
        val mutable body = new expression_node (* The expression trees to initialize respective attributes *)
        method set_handle new_handle = 
            handle <- new_handle
        method get_handle = handle
        method set_class new_class = 
            className <- new_class
        method get_class = className
        method set_internal intern =
            internal <- intern
        method is_internal = internal
        method set_body new_body =
            body <- new_body
        method get_body = body
        method set_param_names names =
            param_names <- names
        method get_param_names = param_names
    end;;
    
(*  This class mainly exists in order to differentiate between cool classes and objects.
    When being passed around, it will only maintain a list of attributes, and if a method
    is executed by it, it will look up that method in the implementation map. Errors will
    be shown by setting typeName to "error", which will be a reserved value since all types
    need to start with a capital letter in Cool. The object itself is not given a name since
    the name is context sensitive and is given by the environment. *)
class cool_object = 
    object(self)
        val mutable typeName = ""
        val mutable is_void = true
        val mutable attribute_names = ( [] : string list ) (* a list of all the attribute bindings *)
        val mutable attribute_types = ( [] : string list ) (* a list of all the attribute binding types *)
        val mutable attribute_pointers = ( [] : int list ) (* a list of all the attribute bindings *)
        val mutable int_value = Int32.zero
        val mutable str_value = ""
        val mutable bool_value = false
        method get_type = typeName
        method set_type new_name = 
            typeName <- let index = try (String.index new_name ' ') with Not_found -> (String.length new_name) in
                        String.sub new_name 0 index
        method get_pointers = attribute_pointers
        method set_pointers p = 
            attribute_pointers <- p
        method get_bindings = attribute_names
        method add_binding new_binding = 
            attribute_names <- ( new_binding :: attribute_names )
        method set_bindings new_bindings = 
            attribute_names <- new_bindings
        method get_types = attribute_types
        method add_type new_type = 
            attribute_types <- ( new_type :: attribute_types )
        method set_types new_types = 
            attribute_types <- new_types
        method notVoid = 
            is_void <- false
        method get_int = int_value
        method set_int i = 
            int_value <- i
        method get_str = str_value
        method set_str s = 
            str_value <- s
        method get_bool = bool_value
        method set_bool b = 
            bool_value <- b
        method isVoid = is_void
    end;;

(*************
 * Utilities
 ************)
 
 (* read in a file line by line *)
let read_file filename = 
    let lines = ref [] in
    let chan = open_in filename in
    try
        while true; do
            lines := input_line chan :: !lines
        done; !lines
    with End_of_file ->
        close_in chan;
        List.rev !lines ;;

(* splits a list at an element *)
let split list elem =
    let rec aux elem acc = function
        | [] -> List.rev acc, []
        | h :: t as l -> if h = elem then List.rev acc, l
                         else aux elem (h :: acc) t  in
    aux elem [] list;;

(* splits a list at an index *)
let split_index list index =
    let rec aux index acc = function
        | [] -> List.rev acc, []
        | h :: t as l -> if index = 0 then List.rev acc, l
                         else aux (index-1) (h :: acc) t  in
    aux index [] list;;

(* reimplementation of the List module function *)
let rec indexOf x lst =
    match lst with
    | [] -> -1
    | h :: t -> if x = h then 0 else (1 + indexOf x t)

(********************
 * Helper functions
 *******************)

(* gets the ancestry of a class all the way back to Object *)
let rec lineage class_name parent_map =
    match class_name with
    | "Object" -> [class_name]
    | _ -> class_name :: (lineage (StringMap.find class_name parent_map) parent_map)
    
(* gets the lub of two class names *)
let rec lub parent_map t_1 t_2 = 
    let t_1_lineage = List.rev (lineage parent_map t_1) in
    let t_2_lineage = List.rev (lineage parent_map t_2) in
    let rec find_lub l1 l2 =
        if l1 <> [] && l2 <> [] && (List.hd l1) = (List.hd l2) then
            let lub = find_lub (List.tl l1) (List.tl l2) in
            match lub with
            | "" -> List.hd l1
            | _ -> lub
        else 
            "" in
    find_lub t_1_lineage t_2_lineage

(* checks if a class has another class in its ancestry *)
let conforms_to class_name needed_class parent_map =
    let class_lineage = lineage class_name parent_map in
    List.mem needed_class class_lineage

(*****************************
 * Deserialization functions
 ****************************)

(* giant pattern match to read in an expression from the AST 
 * some expressions are complicated, so they have their own functions 
 *)
let rec readExpression lines = 
    let line_no = List.hd lines in
    (*let expr_result_type = List.nth lines 1 in*) (* unused, so ocaml was yelling *)
    let expr_type = List.nth lines 2 in
    let result = new expression_node in
    result#set_name expr_type;
    result#set_line (int_of_string line_no);
    match expr_type with
    | "assign" -> 
        let assign_lines, rest = split_index lines 5 in
        let expr, rest = readExpression rest in
        result#set_attrs [List.nth assign_lines 4];
        result#set_exprs [expr];
        result, rest
    | "dynamic_dispatch" -> 
        readDynamicDispatch lines result
    | "static_dispatch" -> 
        readStaticDispatch lines result
    | "self_dispatch" -> 
        readSelfDispatch lines result
    | "if" -> 
        let if_lines, rest = split_index lines 3 in
        let expr_1, rest = readExpression rest in
        let expr_2, rest = readExpression rest in
        let expr_3, rest = readExpression rest in
        result#set_exprs [expr_1; expr_2; expr_3];
        result, rest
    | "while" -> 
        let while_lines, rest = split_index lines 3 in
        let expr_1, rest = readExpression rest in
        let expr_2, rest = readExpression rest in
        result#set_exprs [expr_1; expr_2];
        result, rest
    | "block" -> 
        readBlock lines result
    | "new" -> 
        let new_lines, rest = split_index lines 5 in
        result#set_attrs [List.nth new_lines 4];
        result, rest
    | "isvoid" -> 
        let isvoid_lines, rest = split_index lines 3 in
        let expr, rest = readExpression rest in
        result#set_exprs [expr];
        result, rest
    | "plus" -> 
        let plus_lines, rest = split_index lines 3 in
        let expr_1, rest = readExpression rest in
        let expr_2, rest = readExpression rest in
        result#set_exprs [expr_1; expr_2];
        result, rest
    | "minus" -> 
        let minus_lines, rest = split_index lines 3 in
        let expr_1, rest = readExpression rest in
        let expr_2, rest = readExpression rest in
        result#set_exprs [expr_1; expr_2];
        result, rest
    | "times" -> 
        let times_lines, rest = split_index lines 3 in
        let expr_1, rest = readExpression rest in
        let expr_2, rest = readExpression rest in
        result#set_attrs [];
        result#set_exprs [expr_1; expr_2];
        result, rest
    | "divide" -> 
        let divide_lines, rest = split_index lines 3 in
        let expr_1, rest = readExpression rest in
        let expr_2, rest = readExpression rest in
        result#set_exprs [expr_1; expr_2];
        result, rest
    | "lt" -> 
        let lt_lines, rest = split_index lines 3 in
        let expr_1, rest = readExpression rest in
        let expr_2, rest = readExpression rest in
        result#set_exprs [expr_1; expr_2];
        result, rest
    | "le" -> 
        let le_lines, rest = split_index lines 3 in
        let expr_1, rest = readExpression rest in
        let expr_2, rest = readExpression rest in
        result#set_exprs [expr_1; expr_2];
        result, rest
    | "eq" -> 
        let eq_lines, rest = split_index lines 3 in
        let expr_1, rest = readExpression rest in
        let expr_2, rest = readExpression rest in
        result#set_exprs [expr_1; expr_2];
        result, rest
    | "not" -> 
        let not_lines, rest = split_index lines 3 in
        let expr, rest = readExpression rest in
        result#set_exprs [expr];
        result, rest
    | "negate" -> 
        let negate_lines, rest = split_index lines 3 in
        let expr, rest = readExpression rest in
        result#set_exprs [expr];
        result, rest
    | "identifier" -> 
        let id_lines, rest = split_index lines 5 in
        result#set_attrs [List.nth id_lines 4];
        result, rest
    | "integer" -> 
        let integer_lines, rest = split_index lines 4 in
        result#set_attrs [List.nth integer_lines 3];
        result, rest
    | "string" -> 
        let string_lines, rest = split_index lines 4 in
        result#set_attrs [List.nth string_lines 3];
        result, rest
    | "true" -> 
        let true_lines, rest = split_index lines 3 in
        result#set_attrs ["true"];
        result, rest
    | "false" -> 
        let false_lines, rest = split_index lines 3 in
        result#set_attrs ["false"];
        result, rest
    | "let" -> 
        readLet lines result
    | "case" -> 
        readCase lines result
    | _ -> result,[]

(* reads in the AST for a self dispatch expression *)
and readSelfDispatch lines result =
    let dispatch_lines, rest = split_index lines 3 in
    let method_name_lines, rest = split_index rest 2 in
    let expr_count = int_of_string (List.hd rest) in
    (* inner function to read in the formal expressions *)
    let rec read_exprs n_remaining rest = 
        if n_remaining = 0 then
            [], rest
        else 
            let expr, rest = readExpression rest in
            let other_exprs, rest = read_exprs (n_remaining - 1) rest in
            expr :: other_exprs, rest in
    let formals, rest = read_exprs expr_count (List.tl rest) in
    result#set_attrs [List.nth method_name_lines 1];
    result#set_exprs formals;
    result, rest

(* reads in the AST for a dynamic dispatch expression. like self but with a caller expression. *)
and readDynamicDispatch lines result =
    let dispatch_lines, rest = split_index lines 3 in
    let caller_expr, rest = readExpression rest in
    let method_name_lines, rest = split_index rest 2 in
    let expr_count = int_of_string (List.hd rest) in
    (* inner function to read in the formal expressions *)
    let rec read_exprs n_remaining rest = 
        if n_remaining = 0 then
            [], rest
        else 
            let expr, rest = readExpression rest in
            let other_exprs, rest = read_exprs (n_remaining - 1) rest in
            expr :: other_exprs, rest in
    let formals, rest = read_exprs expr_count (List.tl rest) in
    result#set_attrs [List.nth method_name_lines 1];
    result#set_exprs (caller_expr :: formals);
    result, rest

(* reads in the AST for a static dispatch expression. like dynamic but with static_type. *)
and readStaticDispatch lines result =
    let dispatch_lines, rest = split_index lines 3 in
    let caller_expr, rest = readExpression rest in
    let static_type_lines, rest = split_index rest 2 in
    let method_name_lines, rest = split_index rest 2 in
    let expr_count = int_of_string (List.hd rest) in
    (* inner function to read in the formal expressions *)
    let rec read_exprs n_remaining rest = 
        if n_remaining = 0 then
            [], rest
        else 
            let expr, rest = readExpression rest in
            let other_exprs, rest = read_exprs (n_remaining - 1) rest in
            expr :: other_exprs, rest in
    let formals, rest = read_exprs expr_count (List.tl rest) in
    result#set_attrs [List.nth method_name_lines 1; List.nth static_type_lines 1];
    result#set_exprs (caller_expr :: formals);
    result, rest

(* reads in the AST for a let expression *)
and readLet lines result = 
    let let_lines, rest = split_index lines 4 in
    let binding_count = List.nth let_lines 3 in
    (* inner function to read in the bindings *)
    let rec read_exprs n_remaining rest = 
        if n_remaining = 0 then
            [], [], rest
        else 
            (* differentiate between an initialized let binding, and uninitialized *)
            if (List.hd rest) = "let_binding_no_init" then
                let expr, rest = readLetBindingNoInit rest in
                let binding_name = List.hd (expr#get_attrs) in
                let other_bindings, other_exprs, rest = read_exprs (n_remaining - 1) rest in
                binding_name :: other_bindings, expr :: other_exprs, rest 
            else
                let expr, rest = readLetBindingInit rest in
                let binding_name = List.hd (expr#get_attrs) in
                let other_bindings, other_exprs, rest = read_exprs (n_remaining - 1) rest in
                binding_name :: other_bindings, expr :: other_exprs, rest
        in
    let binding_names, binding_exprs, rest = read_exprs (int_of_string binding_count) rest in
    let body_expr, rest = readExpression rest in
    result#set_attrs binding_names;
    result#set_exprs (binding_exprs @ [body_expr]);
    result, rest

(* reads in the AST for an initialized let binding treated as an expression *)
and readLetBindingInit lines =
    let binding_lines, rest = split_index lines 5 in
    let expr, rest = readExpression rest in
    let result = new expression_node in
    result#set_name (List.hd binding_lines);
    result#set_line (int_of_string (List.nth binding_lines 1));
    result#set_attrs [List.nth lines 2; List.nth binding_lines 4];
    result#set_exprs [expr];
    result, rest

(* reads in the AST for a let binding treated as an expression *)
and readLetBindingNoInit lines =
    let binding_lines, rest = split_index lines 5 in
    let result = new expression_node in
    result#set_name (List.hd binding_lines);
    result#set_line (int_of_string (List.nth binding_lines 1));
    result#set_attrs [List.nth lines 2; List.nth binding_lines 4];
    result, rest

(* reads in the AST for a case expression *)
and readCase lines result =
    let case_lines, rest = split_index lines 3 in
    let case_expr, rest = readExpression rest in
    let num_cases, rest = split_index rest 1 in
    (* inner function to read in the cases *)
    let rec read_exprs n_remaining rest = 
        if n_remaining = 0 then
            [], [], rest
        else 
            let case_elem_lines, rest = split_index rest 4 in
            let case_elem = [List.nth case_elem_lines 1; List.nth case_elem_lines 3] in
            let expr, rest = readExpression rest in
            let other_case_elems, other_exprs, rest = read_exprs (n_remaining - 1) rest in
            case_elem @ other_case_elems, expr :: other_exprs, rest in
    let case_elems, exprs, rest = read_exprs (int_of_string (List.hd num_cases)) rest in
    result#set_attrs case_elems;
    result#set_exprs (case_expr :: exprs);
    result, rest

(* reads in the AST for a block expression *)
and readBlock lines result =
    let block_lines, after_block = split_index lines 4 in
    let expr_count = int_of_string (List.nth block_lines 3) in
    (* inner function to read in the expressions *)
    let rec read_exprs n_remaining rest = 
        if n_remaining = 0 then
            [], rest
        else 
            let expr, rest = readExpression rest in
            let other_exprs, rest = read_exprs (n_remaining - 1) rest in
            expr :: other_exprs, rest in
    let exprs, rest = read_exprs expr_count after_block in
    result#set_attrs [string_of_int expr_count];
    result#set_exprs exprs;
    result, rest

(* returns map from class_name to cool_class objects *)
let deserialize_attrs lines =
    let class_name = List.hd lines in
    let num_attrs = int_of_string (List.nth lines 1) in
    let class_map_init, rest = split_index lines 2 in
    let class_obj = new cool_class in 
    class_obj#set_name class_name;
    (* inner function to read in the attribute expressions *)
    let rec aux n rest c_obj =
        if n = 0 then
            c_obj, rest
        else
            let attr_lines, rest = split_index rest 3 in
            let result = new expression_node in
            result#set_name (List.hd attr_lines);
            result#set_attrs [List.nth attr_lines 1; List.nth attr_lines 2];
            if (List.hd attr_lines) = "no_initializer" then
                let result = result in
                c_obj#add_initializer result;
                c_obj#add_attr (List.nth attr_lines 1);
                c_obj#add_type (List.nth attr_lines 2);
                aux (n-1) rest c_obj
            else
                let expr, rest = readExpression rest in
                result#set_exprs [expr];
                c_obj#add_initializer result;
                c_obj#add_attr (List.nth attr_lines 1);
                c_obj#add_type (List.nth attr_lines 2);
                aux (n-1) rest c_obj
        in
    let result_obj, result_rest = aux num_attrs rest class_obj in
    result_obj, result_rest
    
(* returns string to cool_class map *)
let deserialize_class_map class_map_lines =
    (*print_endline("deserializing class map");*)
    let num_classes = int_of_string (List.nth class_map_lines 1) in
    let class_map_init, rest = split_index class_map_lines 2 in
    (* inner function to read in each class *)
    let rec aux n rest = 
        if n = 0 then
            StringMap.empty, rest
        else
            let new_class, rest = deserialize_attrs rest in
            let new_map, rest = aux (n-1) rest in
            (StringMap.add (new_class#get_name) new_class new_map), rest
        in
    let result, rest = aux num_classes rest in
    (*print_endline((string_of_int (List.length (StringMap.bindings result)))^" classes parsed in");*)
    result, rest

let deserialize_method method_lines = 
    (* create a method signature *)
    let signature = new method_signature in
    (* split into first two lines and the rest *)
    let front, rest = split_index method_lines 2 in
    (* get name and num formals from first two lines *)
    let method_name = List.hd front in
    signature#set_handle method_name;
    let num_formals = int_of_string (List.nth front 1) in
    (* split the rest into attribute names and the rest *)
    let param_names, rest = split_index rest num_formals in
    (* add attribute names to the method_signature *)
    signature#set_param_names param_names;
    (* split the rest into original class name and the rest *)
    let class_origin, rest = split_index rest 1 in
    if (List.nth rest 2) = "internal" then
        let body, rest = split_index rest 4 in
        signature#set_internal true;
        signature, rest
    else
        let body_expr, rest = readExpression rest in
        signature#set_body body_expr;
        signature, rest

let deserialize_class_methods class_method_lines imp_map = 
    (* get class name from head *)
    let class_name = List.hd class_method_lines in
    (* get number of methods from 2nd *)
    let num_methods = int_of_string (List.nth class_method_lines 1) in
    (* split into first two lines and the rest *)
    let front, rest = split_index class_method_lines 2 in
    (* recursively get method_signatures for each method and add them to the map *)
    let rec aux n map rest =
        if n = 0 then
            map, rest
        else
            let method_signature, rest = deserialize_method rest in
            method_signature#set_class class_name;
            let new_map = StringMap.add (class_name^"."^method_signature#get_handle) method_signature map in
            aux (n-1) new_map rest
        in
    aux num_methods imp_map rest

(* returns map from class_name to list of (method_name, method_type, [(formal_name, formal_type)], expression) tuples *)
let deserialize_imp_map imp_map_lines = 
    (* get number of classes from head *)
    let num_classes = int_of_string (List.nth imp_map_lines 1) in
    (* get tail of lines *)
    let front, rest = split_index imp_map_lines 2 in
    (* create a map from class.method_name to method_signatures *)
    let imp_map = StringMap.empty in
    (* recursively get methods for classes *)
    let rec aux n map rest = 
        if n = 0 then
            map, rest
        else
            let new_map, rest = deserialize_class_methods rest map in
            aux (n-1) new_map rest 
        in
    let result_map, result_rest = aux num_classes imp_map rest in
    result_map, result_rest

(* returns a map from a class name to its parent. Object has no parent. *)
let deserialize_parent_map parent_map_lines = 
    let front, map_lines = split_index parent_map_lines 2 in
    let num_classes = int_of_string (List.nth front 1) in
    let result = StringMap.empty in
    (* inner function to read in the child parent pairs *)
    let rec aux n lines map =
        match n with
        | 0 -> map, lines
        | _ -> let new_map = StringMap.add (List.hd lines) (List.nth lines 1) map in
            aux (n-1) (List.tl (List.tl lines)) new_map
        in
    aux num_classes map_lines result

(*************************
 * Expression evaluation
 ************************)
 
(* The large switch case for evaluating individual expressions *)
(* Uses the expression_node class above which defines the expression
    tree for execution. Each expression evaluation returns a 3-tuple, 
    where the first element is the returned object, the 2nd element is the
    new store, and the third object is the new next available pointer space. *)
 let rec evaluateExpression (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    match exp#get_name with
    | "assign" -> evaluateAssign exp so store environment depth next parent_map class_map imp_map
    | "dynamic_dispatch" -> evaluateDynamicDispatch exp so store environment depth next parent_map class_map imp_map
    | "static_dispatch" -> evaluateStaticDispatch exp so store environment depth next parent_map class_map imp_map
    | "self_dispatch" -> evaluateSelfDispatch exp so store environment depth next parent_map class_map imp_map
    | "if" -> evaluateIf exp so store environment depth next parent_map class_map imp_map
    | "while" -> evaluateWhile exp so store environment depth next parent_map class_map imp_map
    | "block" -> evaluateBlock exp so store environment depth next parent_map class_map imp_map
    | "new" -> evaluateNew exp so store environment depth next parent_map class_map imp_map
    | "isvoid" -> evaluateIsVoid exp so store environment depth next parent_map class_map imp_map
    | "plus" -> evaluateAdd exp so store environment depth next parent_map class_map imp_map
    | "minus" -> evaluateSubtract exp so store environment depth next parent_map class_map imp_map
    | "times" -> evaluateMultiply exp so store environment depth next parent_map class_map imp_map
    | "divide" -> evaluateDivide exp so store environment depth next parent_map class_map imp_map
    | "lt" -> evaluateLessThan exp so store environment depth next parent_map class_map imp_map
    | "le" -> evaluateLessThanEq exp so store environment depth next parent_map class_map imp_map
    | "eq" -> evaluateEquals exp so store environment depth next parent_map class_map imp_map
    | "not" -> evaluateNot exp so store environment depth next parent_map class_map imp_map
    | "negate" -> evaluateNegate exp so store environment depth next parent_map class_map imp_map
    | "integer" -> evaluateInteger exp so store environment depth next parent_map class_map imp_map
    | "string" -> evaluateString exp so store environment depth next parent_map class_map imp_map
    | "identifier" -> evaluateIdentifier exp so store environment depth next parent_map class_map imp_map
    | "true" -> evaluateTrue exp so store environment depth next parent_map class_map imp_map
    | "false" -> evaluateFalse exp so store environment depth next parent_map class_map imp_map
    | "let" -> evaluateLet exp so store environment depth next parent_map class_map imp_map
    | "let_binding_init" -> evaluateLetBindingInit exp so store environment depth next parent_map class_map imp_map
    | "let_binding_no_init" -> evaluateLetBindingNoInit exp so store environment depth next parent_map class_map imp_map
    | "case" -> evaluateCase exp so store environment depth next parent_map class_map imp_map
    | _ -> evaluationPlaceHolder exp so store environment depth next parent_map class_map imp_map

(* Dummy method which should never actually be called, used for expressions that don't exist *)
and evaluationPlaceHolder (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    print_string (exp#get_name);
    print_string "\n";
    (new cool_object, store, next)

(* Returns a new integer object with the value specified by the expression. *)
and evaluateInteger (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    let value = (List.nth exp#get_attrs 0) in
    let obj = new cool_object in
    obj#notVoid;
    obj#set_int (Int32.of_string value);
    obj#set_type "Int";
    (obj, store, next)

(* Returns a new true boolean object *)
and evaluateTrue (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    let obj = new cool_object in
    obj#notVoid;
    obj#set_bool true;
    obj#set_type "Bool";
    (obj, store, next)

(* Returns a new false boolean object *)
and evaluateFalse (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    let obj = new cool_object in
    obj#notVoid;
    obj#set_bool false;
    obj#set_type "Bool";
    (obj, store, next)

(* Returns a new string object with the value specified by the expression. *)
and evaluateString (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    let value = (List.nth exp#get_attrs 0) in
    let obj = new cool_object in
    obj#notVoid;
    obj#set_str value;
    obj#set_type "String";
    (obj, store, next)
    
(* Returns a new int which is the negation of the value of the expression passed in *)
and evaluateNegate (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    let toEval = (List.nth exp#get_nextExprs 0) in
    let (evaluated, new_store, new_next) = evaluateExpression toEval so store environment depth next parent_map class_map imp_map in
    let obj = new cool_object in
    obj#notVoid;
    obj#set_int (Int32.neg evaluated#get_int);
    obj#set_type "Int";
    (obj, new_store, new_next)    

(* Returns a new boolean which is the logical negation of the value of the expression passed in *)
and evaluateNot (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    let toEval = (List.nth exp#get_nextExprs 0) in
    let (evaluated, new_store, new_next) = evaluateExpression toEval so store environment depth next parent_map class_map imp_map in
    let obj = new cool_object in
    obj#notVoid;
    obj#set_bool (not evaluated#get_bool);
    obj#set_type "Bool";
    (obj, new_store, new_next)    

(* Looks up an identifier in the environment and store then returns the cool_object value *)
and evaluateIdentifier (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    let id = (List.hd exp#get_attrs) in
    if id = "self" then
        (so, store, next)
    else
        let addr =  StringMap.find id environment in
        let value = IntMap.find addr store in
        (value, store, next)

(* Returns a new booleaan object with the value of whether or not the expression passed in evaluates to void *)
and evaluateIsVoid (exp : expression_node) so store environment depth next parent_map class_map imp_map =
    let (evaluated, s1, n1) = evaluateExpression (List.nth exp#get_nextExprs 0) so store environment depth next parent_map class_map imp_map in
    let obj = new cool_object in
    obj#set_bool evaluated#isVoid;
    obj#notVoid;
    obj#set_type "Bool";
    (obj, s1, n1)

(* Checks two Cool objects for equality, returning a boolean object *)
and evaluateEquals (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    (* First, evaluate the two expressions to be compared *)
    let (e1, s1, n1) = evaluateExpression (List.nth exp#get_nextExprs 0) so store environment depth next parent_map class_map imp_map in
    let (e2, s2, n2) = evaluateExpression (List.nth exp#get_nextExprs 1) so s1 environment depth n1 parent_map class_map imp_map in
    if e1#isVoid then (* Handle comparisons on void *)
        if e2#isVoid then
            let obj = new cool_object in
            obj#notVoid;
            obj#set_type "Bool";
            obj#set_bool true;
            (obj, s2, n2)
        else
            let obj = new cool_object in
            obj#notVoid;
            obj#set_type "Bool";
            obj#set_bool false;
            (obj, s2, n2)
    else
        if (compare e1#get_type e2#get_type) = 0 then (* If the types are not the same, return false *)
            if List.mem e1#get_type ["Int"; "String"; "Bool"] then (* These 3 native classes need to be evaluated differently. *)
                let obj = new cool_object in
                obj#notVoid;
                obj#set_type "Bool";
                match e1#get_type with (* Returns the equality of the object's values *)
                | "Int" -> obj#set_bool ((Int32.compare e1#get_int e2#get_int) = 0); (obj, s2, n2)
                | "String" -> obj#set_bool (e1#get_str = e2#get_str); (obj, s2, n2)
                | "Bool" -> obj#set_bool (e1#get_bool = e2#get_bool); (obj, s2, n2)
                | _ -> obj#set_bool false; (obj, s2, n2)
            else
                if e1 == e2 then (* If not one of the special types, check that the two objects point to the same place. *)
                    let obj = new cool_object in
                    obj#notVoid;
                    obj#set_type "Bool";
                    obj#set_bool true;
                    (obj, s2, n2)
                else
                    let obj = new cool_object in
                    obj#notVoid;
                    obj#set_type "Bool";
                    obj#set_bool false;
                    (obj, s2, n2)
        else
            let obj = new cool_object in
            obj#notVoid;
            obj#set_type "Bool";
            obj#set_bool false;
            (obj, s2, n2)

(* Checks two Cool objects for less than, returning a boolean object *)
and evaluateLessThan (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    (* First, evaluate the two expressions to be compared *)
    let (e1, s1, n1) = evaluateExpression (List.nth exp#get_nextExprs 0) so store environment depth next parent_map class_map imp_map in
    let (e2, s2, n2) = evaluateExpression (List.nth exp#get_nextExprs 1) so s1 environment depth n1 parent_map class_map imp_map in
    if (e1#isVoid || e2#isVoid ) then (* Handle void comparison (always false) *)
            let obj = new cool_object in
            obj#notVoid;
            obj#set_type "Bool";
            obj#set_bool false;
            (obj, s2, n2)
    else
        if ((String.compare e1#get_type e2#get_type) = 0) then (* False if different types *)
            if List.mem e1#get_type ["Int"; "String"; "Bool"] then (* Handle native types differently *)
                let obj = new cool_object in
                obj#notVoid;
                obj#set_type "Bool";
                match e1#get_type with
                | "Int" -> obj#set_bool ((Int32.compare e1#get_int e2#get_int) < 0); (obj, s2, n2)
                | "String" -> obj#set_bool (e1#get_str < e2#get_str); (obj, s2, n2)
                | "Bool" -> obj#set_bool (e1#get_bool < e2#get_bool); (obj, s2, n2)
                | _ -> obj#set_bool false; (obj, s2, n2)
            else (* Non-native types always evaluate to false *)
                let obj = new cool_object in
                obj#notVoid;
                obj#set_type "Bool";
                obj#set_bool false;
                (obj, s2, n2)
        else
            let obj = new cool_object in
            obj#notVoid;
            obj#set_type "Bool";
            obj#set_bool false;
            (obj, s2, n2)

(* Checks two Cool objects for less than or equal, returning a boolean object *)
and evaluateLessThanEq (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    (* First, evaluate the two expressions to be compared *)
    let (e1, s1, n1) = evaluateExpression (List.nth exp#get_nextExprs 0) so store environment depth next parent_map class_map imp_map in
    let (e2, s2, n2) = evaluateExpression (List.nth exp#get_nextExprs 1) so s1 environment depth n1 parent_map class_map imp_map in
    if e1#isVoid then (* Handle void *)
        if e2#isVoid then
            let obj = new cool_object in
            obj#notVoid;
            obj#set_type "Bool";
            obj#set_bool true;
            (obj, s2, n2)
        else
            let obj = new cool_object in
            obj#notVoid;
            obj#set_type "Bool";
            obj#set_bool false;
            (obj, s2, n2)
    else
        if (compare e1#get_type e2#get_type) = 0 then (* Reject comparisons of different types *)
            if List.mem e1#get_type ["Int"; "String"; "Bool"] then (* Handle native types differently *)
                let obj = new cool_object in
                obj#notVoid;
                obj#set_type "Bool";
                match e1#get_type with
                | "Int" -> obj#set_bool ((Int32.compare e1#get_int e2#get_int) <= 0); (obj, s2, n2)
                | "String" -> obj#set_bool (e1#get_str <= e2#get_str); (obj, s2, n2)
                | "Bool" -> obj#set_bool (e1#get_bool <= e2#get_bool); (obj, s2, n2)
                | _ -> obj#set_bool false; (obj, s2, n2)
            else
                let obj = new cool_object in
                obj#notVoid;
                obj#set_type "Bool";
                obj#set_bool false;
                (obj, s2, n2)
        else
            let obj = new cool_object in
            obj#notVoid;
            obj#set_type "Bool";
            obj#set_bool false;
            (obj, s2, n2)

(* Evaluates an if statement, returning one of the two branch outputs *)
and evaluateIf (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    let (e1, s1, n1) = evaluateExpression (List.nth exp#get_nextExprs 0) so store environment depth next parent_map class_map imp_map in
    if e1#get_bool then (* Pick the first branch *)
        evaluateExpression (List.nth exp#get_nextExprs 1) so s1 environment depth n1 parent_map class_map imp_map
    else (* Pick the second branch *)
        evaluateExpression (List.nth exp#get_nextExprs 2) so s1 environment depth n1 parent_map class_map imp_map
  
(* Evaluate a block expression -- just calles the helper, which cycles through. *)    
and evaluateBlock (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    evaluateBlockHelper exp#get_nextExprs so store environment depth next parent_map class_map imp_map

(* Loops through all of the block expressions and returns the last one *)
and evaluateBlockHelper  (exp_list : expression_node list) so store environment depth next parent_map class_map imp_map = 
    if (List.length exp_list) = 1 then (* If it is the last one, return it. *)
        evaluateExpression  (List.nth exp_list 0) so store environment depth next parent_map class_map imp_map
    else (* Otherwise, execute it and move on to the next one. *)
        let (e1, s1, n1) = evaluateExpression  (List.nth exp_list 0) so store environment depth next parent_map class_map imp_map in
        evaluateBlockHelper (List.tl exp_list) so s1 environment depth n1 parent_map class_map imp_map

(* Evaluates a divide expression on 2 ints *)
and evaluateDivide (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    (* Evaluate the two input expressions *)
    let (e1, s1, n1) = evaluateExpression (List.nth exp#get_nextExprs 0) so store environment depth next parent_map class_map imp_map in
    let (e2, s2, n2) = evaluateExpression (List.nth exp#get_nextExprs 1) so s1 environment depth n1 parent_map class_map imp_map in
    (* Then, check for division by zero and throw an exception if the divisor is 0. *)
    if ((Int32.compare Int32.zero e2#get_int) = 0) then begin
        Printf.printf "ERROR: %d: Exception: Divide by zero\n" exp#get_line;
        exit 0
    end else
        let obj = new cool_object in
        obj#notVoid;
        obj#set_type "Int";
        obj#set_int (Int32.div e1#get_int e2#get_int);
        (obj, s2, n2)

(* Evaluates multiply expressions *)
and evaluateMultiply (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    (* Evaluate the two input expressions *)
    let (e1, s1, n1) = evaluateExpression (List.nth exp#get_nextExprs 0) so store environment depth next parent_map class_map imp_map in
    let (e2, s2, n2) = evaluateExpression (List.nth exp#get_nextExprs 1) so s1 environment depth n1 parent_map class_map imp_map in
    let obj = new cool_object in
    obj#notVoid;
    obj#set_type "Int";
    obj#set_int (Int32.mul e1#get_int e2#get_int);
    (obj, s2, n2)

(* Evaluates add expressions *)
and evaluateAdd (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    (* Evaluate the two input expressions *)
    let (e1, s1, n1) = evaluateExpression (List.nth exp#get_nextExprs 0) so store environment depth next parent_map class_map imp_map in
    let (e2, s2, n2) = evaluateExpression (List.nth exp#get_nextExprs 1) so s1 environment depth n1 parent_map class_map imp_map in
    let obj = new cool_object in
    obj#notVoid;
    obj#set_type "Int";
    obj#set_int (Int32.add e1#get_int e2#get_int);
    (obj, s2, n2)

(* Evaluates subtraction expressions *)
and evaluateSubtract (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    (* Evaluate the two input expressions *)
    let (e1, s1, n1) = evaluateExpression (List.nth exp#get_nextExprs 0) so store environment depth next parent_map class_map imp_map in
    let (e2, s2, n2) = evaluateExpression (List.nth exp#get_nextExprs 1) so s1 environment depth n1 parent_map class_map imp_map in
    let obj = new cool_object in
    obj#notVoid;
    obj#set_type "Int ";
    obj#set_int (Int32.sub e1#get_int e2#get_int);
    (obj, s2, n2)

(* Evaluates assignment expressions *)
and evaluateAssign (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    (* First, evaluate the expression to be assigned *)
    let (e1, s1, n1) = evaluateExpression (List.nth exp#get_nextExprs 0) so store environment depth next parent_map class_map imp_map in
    let addr = StringMap.find (List.nth exp#get_attrs 0) environment in (* Look up the pointer of the left-hand side identifier in the environment *)
    (e1, (IntMap.add addr e1 s1), n1) (* Return the object that was assigned, with a modified store *)

(* Evaluate while expressions *)
and evaluateWhile (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    (* Evaluate the expression in the predicate of the while *)
    let (e1, s1, n1) = evaluateExpression (List.nth exp#get_nextExprs 0) so store environment depth next parent_map class_map imp_map in
    if e1#get_bool then (* Execute the body if it evaluated to true, otherwise return void *)
        let (e2, s2, n2) = evaluateExpression (List.nth exp#get_nextExprs 1) so s1 environment depth n1 parent_map class_map imp_map; in
        evaluateExpression exp so s2 environment depth n2 parent_map class_map imp_map
    else
        let obj = new cool_object in
        obj#set_type "Object";
        (obj, s1, n1)

(* Evaluates new expressions *)
and evaluateNew (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    if depth = 1000 then begin (* First, check for exceeded stack depth *)
        Printf.printf "ERROR: %d: Exception: Stack overflow in new\n" exp#get_line;
        exit 0
    end else
        let typeName = if (List.nth exp#get_attrs 0) = "SELF_TYPE" then so#get_type else (List.nth exp#get_attrs 0) in (* Retrieve the type, accounting for SELF_TYPE *)
        let template = StringMap.find typeName class_map in (* Use the type to retrieve the class template *)
        let objEnv = StringMap.empty in (* Make a new environment to instantiate the object *)
        (* This line calls a helper method which fills the store and new environment with void copies of every attribute in the new class. *)
        let (new_store, new_env, pointers, new_next) = newHelper1 store objEnv template#get_attrs template#get_types [] next in
        let obj = new cool_object in (* Create the new object *)
        obj#set_bindings template#get_attrs; (* Set all of the variable names to those of the template class *)
        obj#set_pointers pointers; (* Set the pointers to the list returned by the helper method *)
        obj#set_type typeName; 
        obj#notVoid;
        (* Finally, run a helper method to execute all of the attribute initializers in order using the new environment and store *)
        let (final_store, final_next) = newHelper2 (List.rev template#get_initializers) obj new_store new_env (depth+1) new_next parent_map class_map imp_map (List.rev pointers) in
        (obj, final_store, final_next)

(* Fills the environment with class attribute bindings and the store with null copies of them *)
and newHelper1 store environment bindings types pointers next =
    if (List.length bindings) = 0 then
        (store, environment, pointers, next)
    else
        let nextEnv = StringMap.add (List.hd bindings) next environment in (* Add the binding to the environment at the next pointer *)
        let obj = new cool_object in (* Make each void object *)
        if List.mem (List.hd types) ["Int"; "String"; "Bool"] then begin (* Native types keep their initial values but are not void *)
            obj#notVoid;
            obj#set_type (List.hd types);
        end else (* Set everything else to void *)
            obj#set_type (List.hd types);
        newHelper1 (IntMap.add next obj store) nextEnv (List.tl bindings) (List.tl types) (pointers @ [next]) (next+1) (* Move on to the next binding *)

(* Executes all of the attribute initializers *)
and newHelper2 (toEval : expression_node list) so store environment depth next parent_map class_map imp_map pointers =
    if (List.length toEval) = 0 then
        (store, next)
    else
        (* If it has an initializer, run it and use its output store/next. If it does not, then do nothing and move on. *)
        match (List.hd toEval)#get_name with 
        | "initializer" ->  let (e1, s1, n1) = evaluateExpression (List.hd toEval) so store environment depth next parent_map class_map imp_map in
                            newHelper2 (List.tl toEval) so (IntMap.add (List.hd pointers) e1 s1) environment depth n1 parent_map class_map imp_map (List.tl pointers)
        | "no_initializer" -> newHelper2 (List.tl toEval) so store environment depth next parent_map class_map imp_map (List.tl pointers)
        | _ -> newHelper2 (List.tl toEval) so store environment depth next parent_map class_map imp_map (List.tl pointers)

and evaluateLet (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    evaluateLetHelper exp#get_nextExprs exp#get_attrs so store environment depth next parent_map class_map imp_map

and evaluateLetHelper (exp_list : expression_node list) (attr_list : string list) so store environment depth next parent_map class_map imp_map = 
    if (List.length attr_list) = 1 then
        let (e1, s1, n1) = evaluateExpression  (List.nth exp_list 0) so store environment depth next parent_map class_map imp_map in
        evaluateExpression (List.nth exp_list 1) so (IntMap.add n1 e1 s1) (StringMap.add (List.nth attr_list 0) n1 environment) depth (n1+1) parent_map class_map imp_map
    else
        let (e1, s1, n1) = evaluateExpression (List.nth exp_list 0) so store environment depth next parent_map class_map imp_map in
        let binding = (List.nth attr_list 0) in
        evaluateLetHelper (List.tl exp_list) (List.tl attr_list) so (IntMap.add n1 e1 s1) (StringMap.add binding n1 environment) depth (n1+1) parent_map class_map imp_map


and evaluateLetBindingInit (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    evaluateExpression (List.hd exp#get_nextExprs) so store environment depth next parent_map class_map imp_map

and evaluateLetBindingNoInit (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    let obj = new cool_object in
    if List.mem (List.nth exp#get_attrs 1) ["Int"; "String"; "Bool"] then begin
        obj#notVoid;
        obj#set_type (List.nth exp#get_attrs 1);
    end else
        obj#set_type (List.nth exp#get_attrs 1);
    (obj, store, next)

and evaluateCase (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    let (e1, s1, n1) = evaluateExpression  (List.nth exp#get_nextExprs 0) so store environment depth next parent_map class_map imp_map in
    if e1#isVoid then begin
        Printf.printf "ERROR: %d: Exception: Case on void\n" exp#get_line;
        exit 0
    end else
        let ancestors = lineage e1#get_type parent_map in
        let common = List.filter (fun (x : string) -> List.mem x exp#get_attrs) ancestors in
        if (List.length common) = 0 then begin
            Printf.printf "ERROR: %d: Exception: Case with no matching type\n" exp#get_line;
            exit 0
        end else
            let index = indexOf (List.hd common) exp#get_attrs in
            evaluateExpression (List.nth exp#get_nextExprs ((index/2)+1)) so (IntMap.add n1 e1 s1) (StringMap.add (List.nth exp#get_attrs (index-1)) n1 environment) depth (n1+1) parent_map class_map imp_map

(*  This is it. The ultimate face-off. David and Goliath except in this case, David is a young programmer and Goliath is a hulking
    behemoth of an operational semantics expression. Match-ups like this throughout time have been recorded as the climaxes of human history, and
    this will be no different. I only pray that one day, my story will be recorded in the annals of time just as the stories of those who have come before me. *)
and evaluateDynamicDispatch (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    if depth = 1000 then begin
        Printf.printf "ERROR: %d: Exception: Stack overflow in dynamic dispatch\n" exp#get_line;
        exit 0
    end else
        let (new_store, obj_list, new_next) = dispatch_helper1 (List.tl exp#get_nextExprs) so store environment depth next parent_map class_map imp_map [] in
        let (caller, s1, n1) = evaluateExpression (List.hd exp#get_nextExprs) so new_store environment depth new_next parent_map class_map imp_map in
        if caller#isVoid then begin
            Printf.printf "ERROR: %d: Exception: dispatch on void\n" exp#get_line;
            exit 0
        end else
            let callerType = StringMap.find caller#get_type class_map in
            let key = dispatch_helper2 callerType#get_name (List.hd exp#get_attrs) in
            let handle = StringMap.find key imp_map in
            if handle#is_internal then
                dispatchInternal s1 environment next handle#get_handle caller obj_list
            else
                let (store_passable, env_passable, next_passable) = dispatch_helper3 s1 handle#get_param_names callerType#get_attrs caller#get_pointers obj_list n1 in
                evaluateExpression handle#get_body caller store_passable env_passable (depth+1) next_passable parent_map class_map imp_map

and evaluateStaticDispatch (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    if depth = 1000 then begin
        Printf.printf "ERROR: %d: Exception: Stack overflow in static dispatch\n" exp#get_line;
        exit 0
    end else
        let (new_store, obj_list, new_next) = dispatch_helper1 (List.tl exp#get_nextExprs) so store environment depth next parent_map class_map imp_map [] in
        let (caller, s1, n1) = evaluateExpression (List.hd exp#get_nextExprs) so new_store environment depth new_next parent_map class_map imp_map in
        if caller#isVoid then begin
            Printf.printf "ERROR: %d: Exception: dispatch on void\n" exp#get_line;
            exit 0
        end else
            let callerType = StringMap.find caller#get_type class_map in
            let staticType = StringMap.find (List.nth exp#get_attrs 1) class_map in
            let key = dispatch_helper2 staticType#get_name (List.hd exp#get_attrs) in
            let handle = StringMap.find key imp_map in
            if handle#is_internal then
                dispatchInternal s1 environment next handle#get_handle caller obj_list
            else
                let (store_passable, env_passable, next_passable) = dispatch_helper3 s1 handle#get_param_names callerType#get_attrs caller#get_pointers obj_list n1 in
                evaluateExpression handle#get_body caller store_passable env_passable (depth+1) next_passable parent_map class_map imp_map

and evaluateSelfDispatch (exp : expression_node) so store environment depth next parent_map class_map imp_map = 
    if depth = 1000 then begin
        Printf.printf "ERROR: %d: Exception: Stack overflow in self dispatch\n" exp#get_line;
        exit 0
    end else
        let (new_store, obj_list, new_next) = dispatch_helper1 exp#get_nextExprs so store environment depth next parent_map class_map imp_map [] in
        if so#isVoid then begin
            Printf.printf "ERROR: %d: Exception: dispatch on void\n" exp#get_line;
            exit 0
        end else
            let callerType = StringMap.find so#get_type class_map in
            let key = dispatch_helper2 callerType#get_name (List.hd exp#get_attrs) in
            let handle = StringMap.find key imp_map in
            if handle#is_internal then
                dispatchInternal new_store environment next handle#get_handle so obj_list
            else
                let (store_passable, env_passable, next_passable) = dispatch_helper3 new_store handle#get_param_names callerType#get_attrs so#get_pointers obj_list new_next in
                evaluateExpression handle#get_body so store_passable env_passable (depth+1) next_passable parent_map class_map imp_map

(*  The challenger produces a small yet suspicious-looking slingshot from his pouch. Goliath does not look particularly worried about this
    trinket, but little does he know that it is capable of evaluating all of his parameter expressions and returning the results as a list. *)
and dispatch_helper1 (exp_list : expression_node list) so store environment depth next parent_map class_map imp_map obj_list = 
    if (List.length exp_list) = 0 then
        (store, obj_list, next)
    else
        let (e, s, n) = evaluateExpression (List.hd exp_list) so store environment depth next parent_map class_map imp_map in
        dispatch_helper1 (List.tl exp_list) so s environment depth n parent_map class_map imp_map (obj_list @ [e])

(* Goliath lunges at David, not willing to give him a chance to try out any tricks up his sleeve. He cries out, "You cannot lookup based on solely
    the method handle. Methods belong to classes, and proper retrieval requires a class name!" But David was clever and planned ahead for this scenario.
    He swiftly dodges and throws tacks on the ground to prevent an advance from Goliath. These tacks not only stop a frontal assault, but they also produce
    a key which combines the class and method names in order to look up the correct method signature. *)
and dispatch_helper2 str1 str2 =
    String.concat "." [str1; str2] 

(*  This was it, the moment David had been preparing for since before the fight even began. Goliath wasn't aware that David had snuck smooth stones into his
    pouch to shoot with the slingshot. He then put one of these stones into his slingshot and prepared to let it loose. This stone he had prepared beforehand
    was made so strong by his previous call to new. It was able to dig back up the pointers to attributes which has fallen out of scope and re-bind them to the
    correct variable names, which had also been saved. He even managed to sneak in the bindings for method parameters and their values, which could be bound to
    a new store and environment, for devastating impact. *)
and dispatch_helper3 store (param_names : string list) (attr_names : string list) (pointers : int list) (obj_list : cool_object list) next = 
    let new_env = StringMap.empty in
    let attr_env = dispatch_helper3a new_env attr_names pointers in
    let (method_store, method_env, method_next) = dispatch_helper3b store attr_env param_names obj_list next in
    (method_store, method_env, method_next)

(* A helper to the dispatch helper which re-binds all of the attributes. Some tools don't get a long-winded story. *)
and dispatch_helper3a environment (attr_names : string list) (pointers : int list) = 
    if (List.length attr_names) = 0 then
        environment
    else
        let environment = environment in
        dispatch_helper3a (StringMap.add (List.hd attr_names) (List.hd pointers) environment) (List.tl attr_names) (List.tl pointers) 

(* A helper to the dispatch helper which binds all of the parameters. It would be unfair to give a story to 3b and not 3a. *)
and dispatch_helper3b store environment (param_names : string list) (obj_list : cool_object list) next = 
    if (List.length param_names) = 0 then
        (store, environment, next)
    else
        dispatch_helper3b (IntMap.add next (List.hd obj_list) store) (StringMap.add (List.hd param_names) next environment) (List.tl param_names) (List.tl obj_list) (next+1)
    
and dispatchInternal store environment next handle caller param_list = 
    match handle with
    | "abort" -> internalAbort store environment
    | "type_name" -> internalTypeName store next caller
    | "copy" -> internalCopy store next caller
    | "out_string" -> internalOutString store next caller param_list
    | "out_int" -> internalOutInt store next caller param_list
    | "in_string" -> internalInString store next caller
    | "in_int" -> internalInInt store next caller
    | "length" -> internalLength store next caller
    | "concat" -> internalConcat store next caller param_list
    | "substr" -> internalSubstr store next caller param_list
    | _ -> print_string "problem\n"; (caller, store, next)

and internalAbort store environment = 
    (*Printf.printf "%!";*)
    Printf.printf "abort\n";
    exit 0

and internalTypeName store next caller = 
    let obj = new cool_object in
    obj#notVoid;
    obj#set_type "String";
    obj#set_str caller#get_type;
    (obj, store, next)

and internalCopy store next caller = 
    let obj = new cool_object in
    obj#notVoid;
    obj#set_type caller#get_type;
    obj#set_str caller#get_str;
    obj#set_int caller#get_int;
    obj#set_bool caller#get_bool;
    obj#set_bindings caller#get_bindings;
    let (s1, n1, ptrs) = copyHelper store next caller#get_pointers [] in
    obj#set_pointers ptrs;
    obj#set_types caller#get_types;
    (obj, s1, n1)

and copyHelper store next oldPointers newPointers = 
    if (List.length oldPointers = 0) then
        (store, next, newPointers)
    else
        copyHelper (IntMap.add next (IntMap.find (List.hd oldPointers) store) store) (next+1) (List.tl oldPointers) (newPointers @ [next])

and internalOutString store next caller param_list =
    let str = (List.hd param_list)#get_str in
    print_string (Str.global_replace (Str.regexp_string "\\t") "\t" (Str.global_replace (Str.regexp_string "\\n") "\n" str));
    (caller, store, next)

and internalOutInt store next caller param_list =
    let str = (Int32.to_string (List.hd param_list)#get_int) in
    print_string str;
    (caller, store, next)

and internalInString store next caller = 
    let str = try (read_line ()) with End_of_file -> "" in
    let obj = new cool_object in
    if (String.contains str '\x00') then
        obj#set_str ""
    else
        obj#set_str str;
    obj#set_type "String";
    obj#notVoid;
    (obj, store, next)

and internalInInt store next caller = 
    let rec aux str acc =
        if ((str = "") || not (String.contains " -1234567890" str.[0]) || ((acc <> "") && str.[0] = ' ') || ((acc <> "") && str.[0] = '-')) then
            acc
        else if (acc = "") && str.[0] = ' ' then
            let len = String.length str in
            let new_str = String.sub str 1 (len-1) in
            aux new_str acc
        else if (acc = "") && str.[0] = '-' then
            let len = String.length str in
            let new_str = String.sub str 1 (len-1) in
            aux new_str (acc^"-")
        else
            let len = String.length str in
            let new_str = String.sub str 1 (len-1) in
            aux new_str (acc^(String.make 1 str.[0]))
        in
    let str = aux (try (read_line ()) with End_of_file -> "") "" in
    let obj = new cool_object in
    obj#set_int (if str = "" then 
        Int32.zero
    else
        try (Int32.of_string str) with (Failure "int_of_string") -> Int32.zero); 
    obj#set_type "Int";
    obj#notVoid;
    obj, store, next

and internalLength store next caller = 
    let len = (String.length caller#get_str) in
    let obj = new cool_object in
    obj#set_int (Int32.of_int len);
    obj#set_type "Int";
    obj#notVoid;
    (obj, store, next)

and internalConcat store next caller param_list =
    let str = String.concat "" [caller#get_str; (List.hd param_list)#get_str] in
    let obj = new cool_object in
    obj#set_str str;
    obj#set_type "String";
    obj#notVoid;
    (obj, store, next)


and internalSubstr store next caller param_list = 
    let ind1 = Int32.to_int (List.hd param_list)#get_int in
    let ind2 = Int32.to_int (List.nth param_list 1)#get_int in
    if ( (ind1 < 0) || (ind2 > ((String.length caller#get_str)-ind1)) || (ind2 < 0) ) then begin
        Printf.printf "ERROR: 0: Exception: Substring index out of bounds\n";
        exit 0
    end else
        let str = (String.sub caller#get_str ind1 ind2) in
        let obj = new cool_object in
        obj#set_str str;
        obj#set_type "String";
        obj#notVoid;
        (obj, store, next)

(********
 * Main
 *******)
let main = begin
    let lines = read_file Sys.argv.(1) in
    (* load AST into class_map, imp_map, parent_map *)
    let class_map, rest  = deserialize_class_map lines in
    let imp_map, rest    = deserialize_imp_map rest in
    let parent_map, rest = deserialize_parent_map rest in
    (* init S as empty list of expression values (as ints?) *)
    let store = IntMap.empty in
    (* init E as empty map of strings to integers *)
    let environment = StringMap.empty in
    (* init so as Main class map element *)
    let new_main_expr = new expression_node in
    new_main_expr#set_name "new";
    new_main_expr#set_attrs ["Main"];
    let (so, new_store, next) = evaluateExpression new_main_expr (new cool_object) store environment 0 1 parent_map class_map imp_map in
    let main_expr = new expression_node in
    main_expr#set_name "self_dispatch";
    main_expr#set_attrs ["main"];
    main_expr#set_exprs [];
    (* call (new Main).main() *)
    evaluateExpression main_expr so new_store environment 0 next parent_map class_map imp_map
end;;

main;;
