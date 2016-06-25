-- acl3qb
import System.IO
import System.Environment
import Data.List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Debug.Trace


-------------------------------------------
--- Utilities
--      functions used to format data or 
--      otherwise deal with stuff
--- acl3qb, bjg4uc
-------------------------------------------

-- utility methods for treating tuple lists like maps
-- because some people just want to watch the world burn
--tup_list_contains_key :: (Eq a) => [(a,b)] -> a -> Bool
tup_list_contains_key the_list key = 
    (length [x | x<-the_list, (fst x) == key]) > 0
--tup_list_get ::  (Eq a) => [(a,b)] -> a -> (a,b)
tup_list_get the_list key =
    head [x | x<-the_list, (fst x) == key]
    
-- helper function for getting formal types
argt [] = []
argt (a:b:c:d:tl) = d : (argt tl)
-- helper function for getting formal names
argnames :: [[Char]] -> [[Char]]
argnames [] = []
argnames (a:b:c:d:tl) = (b++"\n") : (argnames tl)
-- get a tuple desribing a method
get_method_signature method_lines = 
    let name = method_lines!!2 
        argc = read (method_lines!!3) 
        -- just the types
        args = (take (argc*4) (drop 4 method_lines))
        return_type = method_lines!!(5 + argc*4) in
    (name, return_type, args, method_lines)

-------------------------------------------
--- Error Checking
--      functions devoted to generating  
--      error messages not related to 
--      expressions go here
--- acl3qb
-------------------------------------------

check_bad_formals [] all_classes seen = ""
check_bad_formals (name_l:name:arg_type_l:arg_type:tl) all_classes seen
    | name == "self" = 
        "ERROR: "++name_l++": Type-Check: method with formal parameter named self"
    | arg_type == "SELF_TYPE" = 
        "ERROR: "++name_l++": Type-Check: method with formal parameter of unknown type SELF_TYPE"
    | not (elem arg_type all_classes) =
        "ERROR: "++name_l++": Type-Check: method formal with undefined type"
    | elem name seen =
        "ERROR: "++name_l++": Type-Check: duplicate formal"
    | otherwise = check_bad_formals tl all_classes (name:seen)

check_bad_methods [] all_classes = ""
check_bad_methods ((name, return_type, args, all):tl) all_classes
    | not (elem return_type ("SELF_TYPE":all_classes)) =
        "ERROR: "++(all!!1)++": Type-Check: method return type is undefined"
    | length [1 | (n,r,s,a)<-tl, n==name, r/=return_type] > 0 =
        let second_method = head [a | (n,r,s,a)<-tl, n==name, r/=return_type] in
        "ERROR: "++(second_method!!1)++": Type-Check: redefines method method "++name++" and changes return type"
    | length [1 | (n,r,s,a)<-tl, n==name, (argt s)/=(argt args)] > 0 =
        let second_method = head [a | (n,r,s,a)<-tl, n==name, (argt s)/=(argt args)] in
        "ERROR: "++(second_method!!1)++": Type-Check: redefines method method "++name++" and changes formal types"
    | otherwise =
        let bad_formals = check_bad_formals args all_classes [] in
        if bad_formals /= "" then
            bad_formals
        else
            check_bad_methods tl all_classes

-- check duplicate method in the same class (non-inherited)
check_dup_method_name [] = ""
check_dup_method_name ((name, return_type, args, all):tl)
    | length [1 | (n,r,s,a)<-tl, n==name] > 0 =
        let second_line = head [(a!!1)|(n,r,s,a)<-tl, n==name] in
        "ERROR: "++second_line++": Type-Check: uninherited duplicate method name"
    | otherwise = check_dup_method_name tl

check_bad_attributes :: [[String]] -> [String] -> String
check_bad_attributes [] all_classes = ""
check_bad_attributes (attr : tl) all_classes
    | not (elem (attr!!4) ("SELF_TYPE":all_classes)) =
        "ERROR: "++(attr!!1)++": Type-Check: attribute with undefined type"
    | length [1 | (t:l:n:body)<-tl, n==(attr!!2), (last t) == (last (head attr))] > 0 =
        let second_line = head [l | (t:l:n:body)<-tl, n==(attr!!2), (last t) == (last (head attr))] in
        "ERROR: "++second_line++": Type-Check: redefininition of attribute "
    | otherwise = check_bad_attributes tl all_classes

-- lots of nasty checks, return "" if there is no error
check_bad_inheritance :: [(String,(String, String, [[[String]]], [[[String]]]))] -> [String] -> String
check_bad_inheritance [] all_classes = ""
check_bad_inheritance ((name,(line,inherit,attribs,methods)) : tl) all_classes
    | (name == "Main") && (length [1 | method<-(concat methods),method!!2=="main"] == 0) =
        "ERROR: 0: Type-Check: class Main method main not found"
    | length [method | method<-(concat methods), method!!2=="main", method!!3/="0"] > 0 =
        "ERROR: 0: Type-Check: class Main method main takes parameters"
    | name == "SELF_TYPE" =
        "ERROR: "++line++": Type-Check: class named SELF_TYPE"
    | inherit == "SELF_TYPE" =
        "ERROR: "++line++": Type-Check: class inherits from SELF_TYPE"
    | length [n | (n,(l,i,a,m))<-tl,n==name] > 0 =
        let second_line = head [l | (n,(l,i,a,m))<-tl,n==name] in
        "ERROR: "++second_line++": Type-Check: redefinition of class "++name
    | elem inherit ["Int","String","Bool"] =
        "ERROR: "++line++": Type-Check: "++name++" inherits from Int, String or Bool"
    | not (elem name all_classes) =
        "ERROR: "++line++": Type-Check: "++name++" inherits from an undeclared class"
    | otherwise = 
        let method_signatures = map get_method_signature (concat methods) 
            bad_attribs = check_bad_attributes (concat attribs) all_classes
            bad_methods = check_bad_methods method_signatures all_classes
            dup_methods = check_dup_method_name (map get_method_signature (last ([]:methods))) in
        if dup_methods /= "" then
            dup_methods
        else if bad_attribs /= "" then
            bad_attribs
        else if bad_methods /= "" then
            bad_methods
        else
            check_bad_inheritance tl all_classes


-------------------------------------------
--- Class Map
--      functions devoted to generating the 
--      class map data structures go here
--- acl3qb
-------------------------------------------

-- add lists of inherited methods/attributes to the single item lists of features
get_class_map classes (root_name, (root_line, root_inheritance, root_attribs, root_methods)) =
    let children = [(n,(l,i,a,m)) | (n,(l,i,a,m)) <- classes, i == root_name] in
    if null children then
        [(root_name, (root_line, root_inheritance, root_attribs, root_methods))]
    else
        let others = [(n,(l,i,a,m)) | (n,(l,i,a,m)) <- classes, i /= root_name]
            new_children = map (\(n,(l,i,a,m)) -> (n,(l,i,root_attribs++a, root_methods++m))) children
            descendants = concat (map (\x -> get_class_map others x) new_children) in
        (root_name, (root_line, root_inheritance, root_attribs, root_methods)):descendants

-- helper method for get_class
get_features_lines class_lines result =
    let new_result = ((head result)++[head class_lines]) : (tail result)
        new_lines = tail class_lines in
    if null new_lines then
        [x | x <- reverse (init new_result)]
    else
        case (head new_lines) of
        "attribute_init" -> get_features_lines (tail new_lines) (["initializer"]:new_result)
        "attribute_no_init" -> get_features_lines (tail new_lines) (["no_initializer"]:new_result)
        "method" -> get_features_lines new_lines ([]:new_result)
        _ -> get_features_lines new_lines new_result
-- split class lines into a tuple that describes the class
get_class class_lines =
    case class_lines !! 2 of
    "inherits" ->
        let line = head class_lines
            name = class_lines !! 1
            inheritance = class_lines !! 4
            features = get_features_lines class_lines [[]]
            attribs = [x | x<-features, (head x) /= "method"]
            methods = [x | x<-features, (head x) == "method"] in
        (name, (line, inheritance, [attribs], [methods]))
    "no_inherits" ->
        let line = head class_lines
            name = class_lines !! 1
            inheritance = "Object"
            features = get_features_lines class_lines [[]]
            attribs = [x | x<-features, (head x) /= "method"]
            methods = [x | x<-features, (head x) == "method"] in
        (name, (line, inheritance, [attribs], [methods]))
    
-- just split the array of all lines into classes
get_classes_lines [] result = result
get_classes_lines all_lines result =
    let new_result = ((head result)++[head all_lines]) : (tail result)
        new_lines = tail all_lines in
    if (length new_lines) < 3 then
        get_classes_lines new_lines new_result
    else
        case (new_lines !! 2) of
            "inherits" -> get_classes_lines new_lines ([] : new_result)
            "no_inherits" -> get_classes_lines new_lines ([] : new_result)
            _ -> get_classes_lines new_lines new_result
                

-------------------------------------------
--- Implementation Map
--      functions devoted to generating the 
--      implementation map string go here
--- acl3qb
-------------------------------------------

-- get implementation map string for one method
--method_imp_map :: [String] -> String -> (String,String)
method_imp_map method_lines defining_class_name class_map = 
    let (name, return_type, args, all) = get_method_signature method_lines
        argc = length (argt args)
        --anotate body expressions of method with types
        argnames_lines = concat (argnames args)
        body_start = 4+argc*4 in
    if elem defining_class_name ["Object", "Int", "Bool", "String", "IO"] then
        let body = drop body_start all
            body_lines = concat (map (\x -> x++"\n") body) in
        (name, name++"\n"++(show argc)++"\n"++argnames_lines++defining_class_name++"\n"++body_lines)
    else
        let parentMap = makeClassMap [(c,i) | (c, (l, i, a, m)) <- class_map] Map.empty
            attrMap = Map.fromList (concat [makeAttrMap c (concat a) | (c, (l,i,a,m)) <- class_map])
            methodMap = Map.fromList (concat [makeMethodMap c (concat m) | (c, (l,i,a,m)) <- class_map])
            (err, pl, nl, t) = typeCheckMethod attrMap methodMap parentMap defining_class_name [] method_lines
            annotated_body_lines = concat (map (\x -> x++"\n") (drop (body_start+2) pl)) in
        (name, name++"\n"++(show argc)++"\n"++argnames_lines++defining_class_name++"\n"++annotated_body_lines)

-- get implementation map string for a whole class
class_imp_map_lines (name,(line,inherit,attribs,methods)) class_map defined =
    -- get the imp map for methods in the current root class
    -- add new (non overridden) methods to the already defined method list
    -- override methods in the current root classes method imp map by taking first defined version already defined
    let uninherited_map = map (\x -> method_imp_map x name class_map) (last methods)
        new_defined = defined++[x | x<-uninherited_map, not (tup_list_contains_key defined (fst x))]
        overridden_uninherited_map = map (\x -> tup_list_get new_defined (fst x)) uninherited_map in
    if elem name ["Object"] then
        overridden_uninherited_map
    else
        -- recurse to inherited classes
        -- remove methods from overridden_uninherited_map duplicated in the inherited_imp_map
        let inheritance = tup_list_get class_map inherit
            inherited_imp_map = class_imp_map_lines inheritance class_map new_defined 
            final_uninherited_map = [x | x<-overridden_uninherited_map, not (tup_list_contains_key inherited_imp_map (fst x))] in
        inherited_imp_map++final_uninherited_map

-- get implementation map string for all classes
class_imp_map (name,(line,inherit,attribs,methods)) class_map = 
    let imp_map = class_imp_map_lines (name,(line,inherit,attribs,methods)) class_map []
        imp_map_lines = concat (map snd imp_map) in
    name ++ "\n" ++ (show (length imp_map)) ++ "\n" ++ imp_map_lines

-- get full implementation map string
full_imp_map class_map = 
    let imp_maps = map (\x -> class_imp_map x class_map) class_map in
    (show (length class_map)) ++ "\n" ++ (concat imp_maps)

check_non_inheritance class_names [] = ""
check_non_inheritance class_names classes_lines =
    let inherits = ((head classes_lines) !! 2) in
        if inherits == "no_inherits" then
            check_non_inheritance class_names (tail classes_lines)
        else if (elem ((head classes_lines) !! 4) class_names) then
            check_non_inheritance class_names (tail classes_lines)
        else
            "ERROR: "++((head classes_lines) !! 3)++": Type-Check: inherits from unknown class"


-------------------------------------------
--- Expression Type Checking
--      functions used to type check 
--      expressions, methods, & attributes
--      as well as report errors
--- bjg4uc
-------------------------------------------

-- Constructs the list of tuples which forms the attribute map (class map)
makeAttrMap :: String -> [[String]] -> [((String, String), String)]
makeAttrMap className attrs = 
    if length attrs == 0 then -- Base case
        [] 
    else -- Call recursively on self with current attribute added to the list
        ((className, ((head attrs) !! 2)), ((head attrs) !! 4)) : (makeAttrMap className (tail attrs))

--Construct the list of tuples which form the method map (implementation map)
makeMethodMap :: String -> [[String]] -> [((String, String), (String,[String]))]
makeMethodMap className [] = []
makeMethodMap className methods = 
    let (name, return_type, args, method_lines) = get_method_signature (head methods) in
        ((className, name), (return_type, (argt args))) : (makeMethodMap className (tail methods))

--Type checks not expressions
typeCheckNot :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckNot attrMap methodMap classMap className prevLines nextLines = 
    --Recursively check whatever comes next
    let (err, pl, nl, t) = exprCheck attrMap methodMap classMap className (prevLines ++ [head nextLines] ++ ["Bool"] ++ [(nextLines !! 1)]) (drop 2 nextLines) in
        if err /= 0 then -- Propagate errors
            (err, pl, nl, t)
        else
            if t == "Bool" then -- Not can only be applied to a bool
                (err, pl, nl, t)
            else -- Send the asociated error message
                (1, ["ERROR: "++(head nextLines)++": Type-Check: Non-boolean expression passed to not"], [], "ERROR")

--Type check for negate expressions
typeCheckNegate :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckNegate attrMap methodMap classMap className prevLines nextLines = 
    -- Recursively check whatever comes next
    let (err, pl, nl, t) = exprCheck attrMap methodMap classMap className (prevLines ++ [head nextLines] ++ ["Int"] ++ [(nextLines !! 1)]) (drop 2 nextLines) in
        if err /= 0 then -- Propagate errors
            (err, pl, nl, t)
        else
            if t == "Int" then -- Only ints can be negated
                (err, pl, nl, t)
            else -- Send the error message associated
                (1, ["ERROR: "++(head nextLines)++": Type-Check: Non-integer expression passed to negate"], [], "ERROR")

--Type checks isvoid expressions, which are pretty simple.
typeCheckIsVoid :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckIsVoid attrMap methodMap classMap className prevLines nextLines = 
    -- Recursive check of following expression
    let (err, pl, nl, t) = exprCheck attrMap methodMap classMap className (prevLines ++ [head nextLines] ++ ["Bool"] ++ [(nextLines !! 1)]) (drop 2 nextLines) in
        (err, pl, nl, "Bool") -- Return whatever it was with type bool. No errors can come from just the isvoid.

--Type checks arithmetic operators (+, -, *, /)
typeCheckArithmetic :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckArithmetic attrMap methodMap classMap className prevLines nextLines =
    -- Recursive expression call twice on the AST
    let (err, pl, nl, t) = exprCheck attrMap methodMap classMap className (prevLines ++ [head nextLines] ++ ["Int"] ++ [(nextLines !! 1)]) (drop 2 nextLines) in
        if err == 0 then -- Check for an error each time
            let (err1, pl1, nl1, t1) = exprCheck attrMap methodMap classMap className pl nl in
                if err1 /= 0 then
                    (err1, pl1, nl1, t1)
                else -- If no errors
                    if (t1 == "Int") && (t == "Int") then -- Confirm that both are ints
                        (err1, pl1, nl1, t1)
                    else -- Otherwise throw an error
                        (1, ["ERROR: "++(head nextLines)++": Type-Check: Attempting arithmetic on non-integers"], [], "ERROR")
        else
            (err, pl, nl, t)

-- Type checks identifiers using the attribute map (class map)
typeCheckIdentifier :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckIdentifier attrMap methodMap classMap className prevLines nextLines = 
    -- First, it has to find the type of the identifier by looking it up.
    let varType = Maybe.fromMaybe "error" (Map.lookup (className, (nextLines !! 3)) attrMap) in
        if varType == "error" then -- If it could not find the id, throw an error
            (1, ["ERROR: "++(head nextLines)++": Type-Check: Unbound identiifier"], [], "ERROR")
        else -- Otherwise return with its type appended
            (0, prevLines++[head nextLines]++[varType]++[(nextLines !! 1)]++[(nextLines !! 2)]++[(nextLines !! 3)], drop 4 nextLines, varType)

-- Type check an equality expression
typeCheckEquality :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckEquality attrMap methodMap classMap className prevLines nextLines = 
    -- Check two successive expressions as the two operands
    let (err, pl, nl, t) = exprCheck attrMap methodMap classMap className (prevLines ++ [head nextLines] ++ ["Bool"] ++ [(nextLines !! 1)]) (drop 2 nextLines) in
        if err == 0 then
            let (err1, pl1, nl1, t1) = exprCheck attrMap methodMap classMap className pl nl in
                if err1 /= 0 then
                    (err1, pl1, nl1, t1)
                else -- If no errors
                    let specialCase = ["Int", "String", "Bool"] in -- All of these have to match type
                        if (elem t specialCase) || (elem t1 specialCase) then
                            if t == t1 then -- If it is one of those and the types match
                                (err1, pl1, nl1, "Bool")
                            else -- If either one is a special case and the types don't match
                                (1, ["ERROR: "++(head nextLines)++": Type-Check: Comparison of invalid types"], [], "ERROR")
                        else -- If it is not a special case
                            (err1, pl1, nl1, "Bool")
        else
            (err, pl, nl, t)

-- Helper to check a block expression that loops over all of the expressions
typeCheckBlockHelper :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> Int -> (Int, [String], [String], String)
typeCheckBlockHelper attrMap methodMap classMap className prevLines nextLines left = 
    -- First, type-check the expression
    let (err, pl, nl, t) = exprCheck attrMap methodMap classMap className prevLines nextLines in
        if err == 0 then -- If there is no error
            if left /= 1 then -- If it's not the last one, then repeat.
                typeCheckBlockHelper attrMap methodMap classMap className pl nl (left-1)
            else -- Else return the type of the last expression evaluated
                (err, pl, nl, t)
        else -- Propagate errors
            (err, pl, nl, t)

-- Type checks block expressions
typeCheckBlock :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckBlock attrMap methodMap classMap className prevLines nextLines = 
    -- Run the helper function
    let (err, pl, nl, t) = typeCheckBlockHelper attrMap methodMap classMap className prevLines (drop 3 nextLines) (read (nextLines !! 2)) in
        if err == 0 then -- Propagate errors through
            typeCheckBlockHelper attrMap methodMap classMap className (prevLines++[head nextLines]++[t]++[(nextLines !! 1)]++[(nextLines !! 2)]) (drop 3 nextLines) (read (nextLines !! 2))
        else
            (err, pl, nl, t)

-- Type checks while expressions
typeCheckWhile :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckWhile attrMap methodMap classMap className prevLines nextLines = 
    -- Type-check the first expression, knowing the overall type will be object
    let (err, pl, nl, t) = exprCheck attrMap methodMap classMap className (prevLines ++ [head nextLines] ++ ["Object"] ++ [(nextLines !! 1)]) (drop 2 nextLines) in
        if err == 0 then -- Check for errors and then check the next expression
            let (err1, pl1, nl1, t1) = exprCheck attrMap methodMap classMap className pl nl in
                if t == "Bool" then -- First expression has to be bool; type of second doesn't matter.
                    if err1 == 0 then -- No errors
                        (err1, pl1, nl1, "Object")
                    else -- Propagate error
                        (err1, pl1, nl1, t1)
                else
                    (1, ["ERROR: "++(head nextLines)++": Type-Check: Loop predicate not of type Bool"], [], "ERROR")
        else
            (err, pl, nl, t)

-- Type check an assignment expression
typeCheckAssign :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckAssign attrMap methodMap classMap className prevLines nextLines = 
    -- First, lookup the type of the identifier on the left of the assignment.
    let varType = Maybe.fromMaybe "error" (Map.lookup (className, (nextLines !! 3)) attrMap) in
        if varType == "error" then -- Unbound identifier
            (1, ["ERROR: "++(nextLines !! 2)++": Type-Check: Invalid identifier in assignment"], [], "ERROR")
        else -- If it finds the identifier, check the expression.
            let (err, pl, nl, t) = exprCheck attrMap methodMap classMap className prevLines (drop 4 nextLines) 
                realVarType = if varType == "SELF_TYPE" then className else varType -- Get the type of the class if the variable has SELF_TYPE
                realTypeT = if t == "SELF_TYPE" then className else t in -- Get the real type of the expression if it is of SELF_TYPE
                if err == 0 then -- If no error
                    if checkConformance classMap realTypeT realVarType then -- Check the conformance of the static types
                        -- Still use SELF_TYPE in the annotation however
                        exprCheck attrMap methodMap classMap className (prevLines++[head nextLines]++[t]++[(nextLines !! 1)]++[(nextLines !! 2)]++[(nextLines !! 3)]) (drop 4 nextLines)
                    else -- Report error if the conformance fails
                        (1, ["ERROR: "++(head nextLines)++": Type-Check: Assignment does not conform"], [], "ERROR")
                else
                    (err, pl, nl, t)

-- Type check new expressions
typeCheckNew :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckNew attrMap methodMap classMap className prevLines nextLines = 
    -- Get the type of the class passed to new
    if (Map.member ((nextLines !! 3), "L") classMap) then
        (0, prevLines++[(head nextLines)]++[(nextLines !! 3)]++[(nextLines !! 1)]++[(nextLines !! 2)]++[(nextLines !! 3)], (drop 4 nextLines), (nextLines !! 3))
    else
        if (nextLines !! 3) == "SELF_TYPE" then -- Check to allow SELF_TYPE
            (0, prevLines++[(head nextLines)]++["SELF_TYPE"]++[(nextLines !! 1)]++[(nextLines !! 2)]++[(nextLines !! 3)], (drop 4 nextLines), "SELF_TYPE")
        else -- If not SELF_TYPE and not in the class map (parent map), then it does not exist.
            (1, ["ERROR: "++(nextLines !! 2)++": Type-Check: Unkown type in new"], [], "ERROR")

-- Type check if expressions
typeCheckIf :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckIf attrMap methodMap classMap className prevLines nextLines = 
    -- Type check the if with a two-pass system because the type of the if is not known initially
    -- Type check the three parts in a row
    let (errP, plP, nlP, tP) = exprCheck attrMap methodMap classMap className prevLines (drop 2 nextLines)
        (err1, pl1, nl1, t1) = exprCheck attrMap methodMap classMap className plP nlP
        (err2, pl2, nl2, t2) = exprCheck attrMap methodMap classMap className pl1 nl1 in
            if errP == 0 then -- Error check
                if (tP == "Bool") then -- The predicate must be of type bool, then re-check with the known type, the LUB of the second and third expressions
                    let (errPn, plPn, nlPn, tPn) = exprCheck attrMap methodMap classMap className (prevLines++[(head nextLines)]++[findLub className classMap t1 t2]++[(nextLines !! 1)]) (drop 2 nextLines) in
                        let (err1n, pl1n, nl1n, t1n) = exprCheck attrMap methodMap classMap className plPn nlPn in
                            if err1n == 0 then -- Error check
                                let (err2n, pl2n, nl2n, t2n) = exprCheck attrMap methodMap classMap className pl1n nl1n in
                                    (err2n, pl2n, nl2n, (findLub className classMap t1 t2)) -- Return the correct if statement
                            else -- Propagate errors
                                (err1n, pl1n, nl1n, t1n)
                else -- Throw error for non-boolean predicate
                    (1, ["ERROR: "++(head nextLines)++": Type-Check: If statement predicate does not evaluate to Bool"], [], "ERROR")
            else
                (errP, plP, nlP, tP)

-- Type check let branches with initializers
letCheckHelperInit :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], Map.Map (String, String) String)
letCheckHelperInit attrMap methodMap classMap className prevLines nextLines = 
    -- Check the type of the new identifier
    if (Map.member ((nextLines !! 4), "L") classMap) || ((nextLines !! 4) == "SELF_TYPE") then
        let varType = (nextLines !! 4) -- If it exists, set the type
            -- Type check the expression that initializes it.
            (err, pl, nl, t) = exprCheck attrMap methodMap classMap className (prevLines ++ (take 5 nextLines)) (drop 5 nextLines) 
            realType1 = if t == "SELF_TYPE" then className else t
            realType2 = if varType == "SELF_TYPE" then className else varType in
            if err == 0 then
                if checkConformance classMap realType1 realType2 then -- Check conformance, accounting for SELF_TYPE
                    (0, pl, nl, (Map.insert (className, (nextLines !! 2)) varType attrMap)) -- Add this variable to the attribute map
                else
                    (1, ["conformance"], [], attrMap) -- Propagate a conformance error. The main let expression has the line number.
            else
                (err, pl, nl, attrMap) -- Propagate other errors
    else -- If the type of the variable does not fit
        (1, ["ERROR: "++(nextLines !! 3)++": Type-Check: Unknown type in let"], [], attrMap) 

-- Type check let branches without initializers
letCheckHelperNoInit :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], Map.Map (String, String) String)
letCheckHelperNoInit attrMap methodMap classMap className prevLines nextLines = 
    -- Check the type of the new identifier
    if (Map.member ((nextLines !! 4), "L") classMap) || ((nextLines !! 4) == "SELF_TYPE") then
        let varType = (nextLines !! 4) in -- If the identifier exists
            (0, (prevLines++(take 5 nextLines)), (drop 5 nextLines), (Map.insert (className, (nextLines !! 2)) varType attrMap))
    else -- If the type does not exist
        (1, ["ERROR: "++(nextLines !! 3)++": Type-Check: Unknown type in let"], [], attrMap) 

-- Helper method to select which helper method to use
letCase :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], Map.Map (String, String) String)
letCase attrMap methodMap classMap className prevLines nextLines =
    case (head nextLines) of -- Pick based on the first line
            "let_binding_init" -> letCheckHelperInit attrMap methodMap classMap className prevLines nextLines
            "let_binding_no_init" -> letCheckHelperNoInit attrMap methodMap classMap className prevLines nextLines

-- Main helper method to loop through let branches
letCheckHelper :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> Int -> (Int, [String], [String], Map.Map (String, String) String)
letCheckHelper attrMap methodMap classMap className prevLines nextLines n = 
    if n == 0 then -- Base case
        (0, prevLines, nextLines, attrMap)
    else if n == 1 then -- Additional base case
        letCase attrMap methodMap classMap className prevLines nextLines
    else -- If n > 1
        -- Type check the next branch
        let (err, pl, nl, newMap) = letCase attrMap methodMap classMap className prevLines nextLines in
            if err == 0 then -- Loop if no errors
                letCheckHelper newMap methodMap classMap className pl nl (n-1)
            else -- Otherwise propagate errors
                (err, pl, nl, newMap)

-- Main method to type check let expressions, uses a two-pass system since type is not initially known
typeCheckLet :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckLet attrMap methodMap classMap className prevLines nextLines = 
    -- Call the helper in order to evaluate all of the branches and make a new attribute map
    let (err, pl, nl, newMap) = letCheckHelper attrMap methodMap classMap className (prevLines++(take 3 nextLines)) (drop 3 nextLines) (read (nextLines !! 2)) in
        if err == 0 then -- If no errors in the branches
            let (errE, plE, nlE, tE) = exprCheck newMap methodMap classMap className pl nl in
                if errE == 0 then
                    -- Do a second pass, now knowing the type of the let
                    let (err2, pl2, nl2, newMap2) = letCheckHelper attrMap methodMap classMap className (prevLines++[head nextLines]++[tE]++[(nextLines !! 1)]++[(nextLines !! 2)]) (drop 3 nextLines) (read (nextLines !! 2)) in
                        exprCheck newMap2 methodMap classMap className pl2 nl2
                else
                    (errE, plE, nlE, tE)
        else -- Print the specified error
            if ((head pl) == "conformance") then
                (1, ["ERROR: "++(head nextLines)++": Type-Check: Conformance error in let binding"], [], "ERROR")
            else
                (err, pl, nl, "error")

-- Helper method to type check the parameters in a dispatch
typeCheckParameters :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> [String] -> Int -> (Int, [String], [String], String)
typeCheckParameters attrMap methodMap classMap className prevLines nextLines paramTypes 0 = (0, prevLines, nextLines, "void") -- Base case
typeCheckParameters attrMap methodMap classMap className prevLines nextLines paramTypes n = 
    if n == 1 then -- Non-trivial base case, one parameter left
        let (err, pl, nl, t) = exprCheck attrMap methodMap classMap className prevLines nextLines -- Check the expression
            realTypeT = if t == "SELF_TYPE" then className else t -- Account for SELF_TYPE
            realTypeP = if (head paramTypes) == "SELF_TYPE" then className else (head paramTypes) in
            if checkConformance classMap realTypeT realTypeP then -- Make sure the type conforms to the expected parameter
                (err, pl, nl, t)
            else
                (1, ["param"], [], "error") -- Propagate a conformance error if the parameter does not conform
    else -- Continuing case
        let (err, pl, nl, t) = exprCheck attrMap methodMap classMap className prevLines nextLines -- Check the expression
            realTypeT = if t == "SELF_TYPE" then className else t -- Account for SELF_TYPE
            realTypeP = if (head paramTypes) == "SELF_TYPE" then className else (head paramTypes) in
            if checkConformance classMap realTypeT realTypeP then -- Make sure the type conforms to the expected parameter
                if err == 0 then
                    typeCheckParameters attrMap methodMap classMap className pl nl (tail paramTypes) (n-1)
                else
                    (err, pl, nl, t)
            else
                (1, ["param"], [], "error") -- Propagate a conformance error if the parameter does not conform

-- Method to type-check static dispatch statements. It's a lot of Haskell, but it's broken up pretty clearly.
typeCheckStaticDispatch :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckStaticDispatch attrMap methodMap classMap className prevLines nextLines = 
    -- First, type-check the callee expression
    let (errE, plE, nlE, tE) = exprCheck attrMap methodMap classMap className prevLines (drop 2 nextLines) in
        if errE == 0 then -- Check for an error in the callee expression
            let exprType = if (tE == "SELF_TYPE") then className else tE -- Account for SELF_TYPE
                staticType = (nlE !! 1) in -- The static type is denoted in static dispatch
                if checkConformance classMap exprType staticType then -- Make sure the expression is of some sub-type of the static type
                    let (methodType, paramTypes) = (Maybe.fromMaybe ("error", []) (Map.lookup (staticType, (nlE !! 3)) methodMap)) in -- Get the type of the method
                        if methodType /= "error" then -- Check that the method signature exists
                            if (read (nlE !! 4)) == (length paramTypes) then -- Check that it is being passed the correct number of parameters
                                let (errP, plP, nlP, tP) = typeCheckParameters attrMap methodMap classMap className plE (drop 5 nlE) paramTypes (length paramTypes) -- Call helper method to type-check params
                                    realMethodType = if (methodType == "SELF_TYPE") then tE else methodType in -- Account for SELF_TYPE methods
                                    if errP == 0 then 
                                        -- Do a second pass now knowing the type of the method and knowing it all will type-check correctly
                                        let (err1, pl1, nl1, t1) = exprCheck attrMap methodMap classMap className (prevLines++[(head nextLines)]++[realMethodType]++[(nextLines !! 1)]) (drop 2 nextLines) 
                                            (err2, pl2, nl2, t2) = typeCheckParameters attrMap methodMap classMap className (pl1++(take 5 nl1)) (drop 5 nl1) paramTypes (length paramTypes) in
                                                (err2, pl2, nl2, realMethodType)
                                    else
                                        if (head plP) == "param" then -- Allow parameter errors to propagate
                                            (1, ["ERROR: "++(nlE !! 0)++": Type-Check: Parameter of unexpected type"], [], "ERROR")
                                        else
                                            (errP, nlP, plP, tP)
                            else
                                (1, ["ERROR: "++(nlE !! 2)++": Type-Check: Incorrect number of method parameters"], [], "ERROR")
                        else
                            (1, ["ERROR: "++(nlE !! 2)++": Type-Check: Unknown method identifier in static dispatch"], [], "ERROR")
                else
                    (1, ["ERROR: "++(head nextLines)++": Type-Check: Calling expression does not conform to static type in dispatch"], [], "ERROR")
        else
            (errE, plE, nlE, tE)

-- Method to type-check dynamic dispatch expressions
typeCheckDynamicDispatch :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckDynamicDispatch attrMap methodMap classMap className prevLines nextLines =
    -- First, type-check the callee expression
    let (errE, plE, nlE, tE) = exprCheck attrMap methodMap classMap className prevLines (drop 2 nextLines) in
        if errE == 0 then -- Check for an error in the callee expression
            let exprType = if (tE == "SELF_TYPE") then className else tE -- Account for SELF_TYPE
                (methodType, paramTypes) = (Maybe.fromMaybe ("error", []) (Map.lookup (exprType, (nlE !! 1)) methodMap)) in -- Get the type of the method
                if methodType /= "error" then -- Check that the method signature exists
                    if (read (nlE !! 2)) == (length paramTypes) then -- Check that it is being passed the correct number of parameters
                        let (errP, plP, nlP, tP) = typeCheckParameters attrMap methodMap classMap className plE (drop 3 nlE) paramTypes (length paramTypes) -- Call the helper to check params
                            realMethodType = if (methodType == "SELF_TYPE") then tE else methodType in
                            if errP == 0 then
                                -- Do a second pass now knowing the type of the method and knowing it all will type-check correctly
                                let (err1, pl1, nl1, t1) = exprCheck attrMap methodMap classMap className (prevLines++[(head nextLines)]++[realMethodType]++[(nextLines !! 1)]) (drop 2 nextLines) 
                                    (err2, pl2, nl2, t2) = typeCheckParameters attrMap methodMap classMap className (pl1++(take 3 nl1)) (drop 3 nl1) paramTypes (length paramTypes) in
                                        (err2, pl2, nl2, realMethodType)
                            else
                                if (head plP) == "param" then -- Allow parameter errors to propagate
                                    (1, ["ERROR: "++(nlE !! 0)++": Type-Check: Parameter of unexpected type"], [], "ERROR")
                                else
                                    (errP, nlP, plP, tP)
                    else
                        (1, ["ERROR: "++(nlE !! 0)++": Type-Check: Incorrect number of method parameters"], [], "ERROR")
                else
                    (1, [("ERROR: "++(head nlE)++": Type-Check: Unknown method identifier in dynamic dispatch")], [], "ERROR")
        else
            (errE, plE, nlE, tE)

-- Method to type-check self dispatch expressions. Unlike dynamic and static dispatch, it does not need 2 passes.
typeCheckSelfDispatch :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckSelfDispatch attrMap methodMap classMap className prevLines nextLines =
    let (methodType, paramTypes) = (Maybe.fromMaybe ("error", []) (Map.lookup (className, (nextLines !! 3)) methodMap)) in -- Get the type of the method
        if methodType /= "error" then -- Check that the method signature exists
            if (read (nextLines !! 4)) == (length paramTypes) then -- Check that it is being passed the correct number of parameters
                -- Call the helper function to type-check the parameters
                let (err, pl, nl, t) = typeCheckParameters attrMap methodMap classMap className (prevLines++[(nextLines !! 0)]++[methodType]++(drop 1 (take 5 nextLines))) (drop 5 nextLines) paramTypes (length paramTypes) in
                    if err == 0 then -- If no errors in the parameters
                        (err, pl, nl, methodType)
                    else
                        if (head pl) == "param" then -- Allow parameter errors to propagate
                            (1, ["ERROR: "++(nextLines !! 0)++": Type-Check: Parameter of unexpected type"], [], "ERROR")
                        else
                            (err, pl, nl, t)
            else
                (1, ["ERROR: "++(head nextLines)++": Type-Check: Incorrect number of method parameters"], [], "ERROR")
        else
            (1, [("ERROR: "++(head nextLines)++": Type-Check: Unknown method identifier in self dispatch")], [], "ERROR")

-- Helper method to type-check the branches of a case statement
typeCheckBranches :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> [String] -> Int -> (Int, [String], [String], String)
typeCheckBranches attrMap methodMap classMap className prevLines nextLines typesSeen n =
    if n == 1 then -- Base case for 1 branch
        let newMap = (Map.insert (className, (nextLines !! 1)) (nextLines !! 3) attrMap) in -- Add the case identifier to the attribute map
            if (elem (nextLines !! 3) typesSeen) then -- Check for no repeat types
                (1, [("ERROR: "++(head nextLines)++": Type-Check: Two branches in case of same type")], [], "ERROR")
            else
                if (nextLines !! 3) == "SELF_TYPE" then -- Check for SELF_TYPE
                    (1, [("ERROR: "++(head nextLines)++": Type-Check: SELF_TYPE not allowed in case branch")], [], "ERROR")
                else -- After error checking, check the expression with the new map
                    exprCheck newMap methodMap classMap className (prevLines++(take 4 nextLines)) (drop 4 nextLines)
    else
        let newMap = (Map.insert (className, (nextLines !! 1)) (nextLines !! 3) attrMap) -- Add the case identifier to the attribute map
            (errE, plE, nlE, tE) = exprCheck newMap methodMap classMap className (prevLines++(take 4 nextLines)) (drop 4 nextLines) in -- Check the following expression
                if (elem (nextLines !! 3) typesSeen) then -- Check for no repeat types
                    (1, [("ERROR: "++(head nextLines)++": Type-Check: Two branches in case of same type")], [], "ERROR")
                else
                    if (nextLines !! 3) == "SELF_TYPE" then -- Check for SELF_TYPE
                        (1, [("ERROR: "++(head nextLines)++": Type-Check: SELF_TYPE not allowed in case branch")], [], "ERROR")
                    else
                        if errE == 0 then
                            let (errNext, plNext, nlNext, tNext) = typeCheckBranches attrMap methodMap classMap className plE nlE (typesSeen++[(nextLines !! 3)]) (n-1) in -- Recursively call self to loop
                                if errNext == 0 then -- Propagate errors
                                    (errNext, plNext, nlNext, (findLub className classMap tE tNext)) -- The LUB of all the parts is equal to the cumulative LUB
                                else
                                    (errNext, plNext, nlNext, tNext)
                        else
                            (errE, plE, nlE, tE)
-- Main method to type-check a case expression, has to use 2 passes because the type of the case is not known initially
typeCheckCase :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckCase attrMap methodMap classMap className prevLines nextLines =
    -- Type-check the first expression
    let (err1, pl1, nl1, t1) = exprCheck attrMap methodMap classMap className prevLines (drop 2 nextLines) in
        if err1 == 0 then -- If no errors
            let (errB, plB, nlB, tB) = typeCheckBranches attrMap methodMap classMap className pl1 (drop 1 nl1) [] (read (head nl1)) in -- Use the helper to type-check the brances
                if errB == 0 then -- If no errors, do second pass
                    let (err2, pl2, nl2, t2) = exprCheck attrMap methodMap classMap className (prevLines++(take 1 nextLines)++[tB]++[(nextLines !! 1)]) (drop 2 nextLines) in
                        typeCheckBranches attrMap methodMap classMap className (pl2++[(head nl2)]) (drop 1 nl2) [] (read (head nl2))
                else
                    (errB, plB, nlB, tB)
        else
            (err1, pl1, nl1, t1)
{-
    This method is the general purpose expression-checking method which calls all the other expression checking methods.

    It takes as parameters:
        An attribute map (Officially called the class map)
        A method map (Officially called the implementation map)
        A class map (Officially called the inheritance map)
        The name of the class it is currently type-checking
        A list of all lines which have previously been parsed
        A list of all lines which still need to be parsed
    
    It returns a tuple containing:
        An int which represents whether or not the method returned an error. 0 is no error, and 1 is an error.
        A list of strings representing the updated list of lines which need to be parsed
        A list of strings representing the updated list of lines which have been parsed
        A string which is the type of whatever expression was just checked

    This form of expression checking is unique because it reads in the abstract syntax tree and produces the annotated AST as it type-checks.
    For this reason, it passes around the lines previously read, which are annotated, and the lines which need to be read, which serve as the input.
    This method does occasionally require that certain expression checks do 2 passes since their type is not known initially, which is shown in methods such as typeCheckLet
-}
exprCheck :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
exprCheck attrMap methodMap classMap className prevLines nextLines = 
    case (nextLines !! 1) of
        "assign" -> typeCheckAssign attrMap methodMap classMap className prevLines nextLines
        "dynamic_dispatch" -> typeCheckDynamicDispatch attrMap methodMap classMap className prevLines nextLines
        "static_dispatch" -> typeCheckStaticDispatch attrMap methodMap classMap className prevLines nextLines
        "self_dispatch" -> typeCheckSelfDispatch attrMap methodMap classMap className prevLines nextLines
        "if" -> typeCheckIf attrMap methodMap classMap className prevLines nextLines
        "while" -> typeCheckWhile attrMap methodMap classMap className prevLines nextLines
        "block" -> typeCheckBlock attrMap methodMap classMap className prevLines nextLines
        "new" -> typeCheckNew attrMap methodMap classMap className prevLines nextLines
        "isvoid" -> typeCheckIsVoid attrMap methodMap classMap className prevLines nextLines
        "plus" -> typeCheckArithmetic attrMap methodMap classMap className prevLines nextLines
        "minus" -> typeCheckArithmetic attrMap methodMap classMap className prevLines nextLines
        "times" -> typeCheckArithmetic attrMap methodMap classMap className prevLines nextLines
        "divide" -> typeCheckArithmetic attrMap methodMap classMap className prevLines nextLines
        "lt" -> typeCheckEquality attrMap methodMap classMap className prevLines nextLines
        "le" -> typeCheckEquality attrMap methodMap classMap className prevLines nextLines
        "eq" -> typeCheckEquality attrMap methodMap classMap className prevLines nextLines
        "not" -> typeCheckNot attrMap methodMap classMap className prevLines nextLines
        "negate" -> typeCheckNegate attrMap methodMap classMap className prevLines nextLines
        "integer" -> (0, prevLines++[head nextLines]++["Int"]++[(nextLines !! 1)]++[(nextLines !! 2)], drop 3 nextLines, "Int")
        "string" -> (0, prevLines++[head nextLines]++["String"]++[(nextLines !! 1)]++[(nextLines !! 2)], drop 3 nextLines, "String")
        "identifier" -> typeCheckIdentifier attrMap methodMap classMap className prevLines nextLines
        "true" -> (0, prevLines++[head nextLines]++["Bool"]++[(nextLines !! 1)], drop 2 nextLines, "Bool")
        "false" -> (0, prevLines++[head nextLines]++["Bool"]++[(nextLines !! 1)], drop 2 nextLines, "Bool")
        "let" -> typeCheckLet attrMap methodMap classMap className prevLines nextLines
        "case" -> typeCheckCase attrMap methodMap classMap className prevLines nextLines
        _ -> (1, [""], [], "IMPOSSIBRU")

-- Helper function to type-check cool methods which type-checks its parameters and builds the new attribute map.
-- To build the attribute map, it has an attribute map in its return 4-tuple instead of a type.
methodCheckHelper :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> Int -> (Int, [String], [String], Map.Map (String, String) String)
methodCheckHelper attrMap methodMap classMap className prevLines nextLines n = 
    if n == 0 then -- Base case for no parameters
        (0, prevLines, nextLines, attrMap)
    else if n == 1 then -- Non-trivial base case for 1 parameter
        if Map.member ((nextLines !! 3), "L") classMap then -- Check that the type exists
            (0, (prevLines++(take 4 nextLines)), (drop 4 nextLines), (Map.insert (className, nextLines !! 1) (nextLines !! 3) attrMap)) -- Return the new attribute map
        else -- Else throw an error
            (1, ["ERROR: "++(nextLines !! 2)++": Type-Check: Unknown type in method parameters"], [], attrMap)
    else -- Main looping structure
        let (err, pl, nl, newMap) = methodCheckHelper attrMap methodMap classMap className (prevLines++(take 4 nextLines)) (drop 4 nextLines) (n-1) in -- Call self recursively immediately to loop
            if err /= 0 then -- Check for errors in the other parameters
                (err, pl, nl, newMap)
            else
                if Map.member ((nextLines !! 3), "L") classMap then -- Check that the type exists
                    (0, pl, nl, (Map.insert (className, (nextLines !! 1)) (nextLines !! 3) newMap)) -- Return the new attribute map
                else
                    (1, ["ERROR: "++(nextLines !! 2)++": Type-Check: Unknown type in method parameters"], [], attrMap) 

-- Main function to type-check Cool methods
typeCheckMethod :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckMethod attrMap methodMap classMap className prevLines nextLines =
    -- Immediately call the helper method to check the parameters and get the new attribute map
    let (errAttr, plAttr, nlAttr, newAttrMap) = methodCheckHelper attrMap methodMap classMap className (prevLines ++ (take 4 nextLines)) (drop 4 nextLines) (read (nextLines !! 3)) in
        if errAttr == 0 then
            let finalAttrMap = Map.insert (className, "self") "SELF_TYPE" newAttrMap in -- Add self to the attribute map
                let (err, pl, nl, t) = exprCheck finalAttrMap methodMap classMap className (plAttr++(take 2 nlAttr)) (drop 2 nlAttr) in -- Type-check the method body
                    let realType = if (t == "SELF_TYPE") then className else t in -- Account SELF_TYPE in the method body type
                    if err == 0 then -- Check for errors in the method body
                        if (nlAttr !! 1) == "SELF_TYPE" then -- If it returns SELF_TYPE, then they both have to be SELF_TYPE
                            if (nlAttr !! 1) == t then
                                (err, pl, nl, t)
                            else
                                (1, ["ERROR: "++(nextLines !! 1)++": Type-Check: Method body does not match expected type"], [], "ERROR")
                        else -- Otherwise, just check conformance
                            if checkConformance classMap realType (nlAttr !! 1) then
                                (err, pl, nl, (nlAttr !! 1))
                            else
                                (1, ["ERROR: "++(nextLines !! 1)++": Type-Check: Method body does not match expected type"], [], "ERROR")
                    else
                        (err, pl, nl, t)
        else
            (errAttr, plAttr, nlAttr, "ERROR")

-- Helper method to type-check attributes without an initializing expression
typeCheckAttributeNoInit :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckAttributeNoInit attrMap methodMap classMap className prevLines nextLines = 
    if (Map.member ((nextLines !! 4), "L") classMap) || ((nextLines !! 4) == "SELF_TYPE") then -- Check that the type exists
        (0, prevLines++(take 5 nextLines), (drop 5 nextLines), (nextLines !! 4)) -- If it does, return it.
    else -- Otherwise, report an error
        (1, ["ERROR: "++(nextLines !! 3)++": Type-Check: Unknown attribute type"], [], "ERROR")

-- Helper method to type-check attributes with an initializing expression
typeCheckAttributeInit :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckAttributeInit attrMap methodMap classMap className prevLines nextLines = 
    let (err, pl, nl, t) = typeCheckAttributeNoInit attrMap methodMap classMap className prevLines nextLines in -- First just check it as though there was no initializer
        if err == 0 then
            let (errE, plE, nlE, tE) = exprCheck attrMap methodMap classMap className pl nl  -- Then type-check the expression
                realType1 = if (t == "SELF_TYPE") then className else t -- Account for SELF_TYPE
                realType2 = if (tE == "SELF_TYPE") then className else tE in
                if errE == 0 then
                    if checkConformance classMap realType2 realType1 then -- Check that the types conform
                        (errE, plE, nlE, tE)
                    else
                        (1, ["ERROR: "++(nextLines !! 1)++": Type-Check: Attribute initializer does not conform to its type"], [], "ERROR")
                else
                    (errE, plE, nlE, tE)

        else
            (err, pl, nl, t)

-- Method to type-check all atributes which calls either helper method
typeCheckAttribute :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckAttribute attrMap methodMap classMap className prevLines nextLines = 
    if (nextLines !! 2) == "self" then -- Dis-allow attributes named self
        (1, ["ERROR: "++(nextLines !! 1)++": Type-Check: Attribute declared has name self"], [], "ERROR")
    else
        case (head nextLines) of -- Call the helper methods
            "attribute_no_init" -> typeCheckAttributeNoInit attrMap methodMap classMap className prevLines nextLines
            "attribute_init" -> typeCheckAttributeInit attrMap methodMap classMap className prevLines nextLines

-- Helper method to select which class property type checker to use
classCase :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
classCase attrMap methodMap classMap className prevLines nextLines = 
    case (head nextLines) of -- Check which kind of property it is
        "attribute_no_init" -> typeCheckAttribute attrMap methodMap classMap className prevLines nextLines
        "attribute_init" -> typeCheckAttribute attrMap methodMap classMap className prevLines nextLines
        "method" -> typeCheckMethod attrMap methodMap classMap className prevLines nextLines

-- Helper method to loop through all class properties and type-check them
typeCheckClassHelper:: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> Int -> (Int, [String], [String], String)
typeCheckClassHelper attrMap methodMap classMap className prevLines nextLines 0 = (0, prevLines, nextLines, "void")
typeCheckClassHelper attrMap methodMap classMap className prevLines nextLines n = 
    if n == 1 then -- /base case where n = 1
        classCase attrMap methodMap classMap className prevLines nextLines
    else
        let (err, pl, nl, t) = classCase attrMap methodMap classMap className prevLines nextLines in -- Call class case to type-check next property
            if err == 0 then
                typeCheckClassHelper attrMap methodMap classMap className pl nl (n-1) -- Call self recursively to loop
            else
                (err, pl, nl, t)

-- The body of this function just removes the class header and then calls its helper on the remaining list of attributes and methods.
typeCheckClass :: Map.Map (String, String) String -> Map.Map (String, String) (String, [String]) -> Map.Map (String, String) [String] -> String -> [String] -> [String] -> (Int, [String], [String], String)
typeCheckClass attrMap methodMap classMap className prevLines nextLines = 
    if (nextLines !! 2) == "no_inherits" then 
        typeCheckClassHelper attrMap methodMap classMap className (prevLines++(take 4 nextLines)) (drop 4 nextLines) (read (nextLines !! 3))
    else
        typeCheckClassHelper attrMap methodMap classMap className (prevLines++(take 6 nextLines)) (drop 6 nextLines) (read (nextLines !! 5))

-- Check the conformance of one type to another using a class map
checkConformance :: Map.Map (String, String) [String] -> String -> String -> Bool
checkConformance classMap mustConform conformTo =
    let lst = Maybe.fromMaybe [] (Map.lookup (conformTo, "C") classMap) in -- Get the list of sub-classes of the type it has to conform to, to check if it conforms to any sub-classes
        if elem mustConform (lst++[conformTo]) then -- Check conformance of self and immediate sub-classes
            True
        else
            foldr (\a b -> (checkConformance classMap mustConform a) || b) False lst  -- Check conformance on all sub-classes

-- A method to find the least upper bound of two types using a class map
findLub :: String -> Map.Map (String, String) [String] -> String -> String -> String
findLub className classMap class1 class2 = 
    if class1 == class2 then -- Provision which exists almost entirely for the sake of SELF_TYPE
        class1
    else
        let type1 = if class1 == "SELF_TYPE" then className else class1 -- Check for SELF_TYPE
            type2 = if class2 == "SELF_TYPE" then className else class2
            lst1 = Maybe.fromMaybe [type1] (Map.lookup (type1, "L") classMap) -- This maybe will never give the default
            lst2 = Maybe.fromMaybe [type2] (Map.lookup (type2, "L") classMap) in
        head (filter (\x -> elem x lst2) lst1) -- Get a list of all the shared ancestors, in order from closest to furthest and then pick the closest

-- Function to format the class map which is used for conformance and LUB (also known as the inheritance map)
makeClassMap :: [(String, String)] -> Map.Map (String, String) [String] -> Map.Map (String, String) [String]
makeClassMap tupleList map = Map.unionWith (++) (makeConformMap tupleList map) (makeLubMap tupleList map) -- Combine the output of the two composite functions

-- Make a map from a list of tuples which is used for conformance checking. The second string in the tuple matches it to the conformance-checking list
makeConformMap :: [(String, String)] -> Map.Map (String, String) [String] -> Map.Map (String, String) [String]
makeConformMap [] current = current -- Base case for empty tuple list
makeConformMap tupleList current = 
    let sub = fst (head tupleList)
        super = snd (head tupleList) in
            if Map.member (super, "C") current then
                makeConformMap (tail tupleList) (Map.insert (super, "C") ((current Map.! (super, "C"))++[sub]) current) -- Build the map so its list contains all conforming classes
            else
                makeConformMap (tail tupleList) (Map.insert (super, "C") [sub] current) -- Make the list if it does not exist

-- Make a map from a list of tuples which is used for LUB checking. The second string in the tuple matches it to the LUB-checking list
makeLubMap :: [(String, String)] -> Map.Map (String, String) [String] -> Map.Map (String, String) [String]
makeLubMap [] current = current -- Base case for empty tuple list
makeLubMap tupleList current = 
    let sub = fst (head tupleList)
        super = snd (head tupleList) in
            if Map.member (sub, "L") current then -- Check if the sub-class is already in
                if Map.member (super, "L") current then -- If the super exists, set the sub's list to the concatenation of their lists
                    makeLubMap (tail tupleList) (Map.insert (sub, "L") ((current Map.! (sub, "L"))++(current Map.! (super, "L"))) current)
                else -- If the super does not exist, add it to the sub's list
                    makeLubMap (tail tupleList) (Map.insert (sub, "L") ((current Map.! (sub, "L"))++[super]) current)
            else
                if Map.member (super, "L") current then -- If the super exists, add the sub concatenated to the super's list
                    makeLubMap (tail tupleList) (Map.insert (sub, "L") ( sub : (current Map.! (super, "L"))) current)
                else -- If neither are in, add the sub and super to the sub's list
                    makeLubMap (tail tupleList) (Map.insert (sub, "L") [sub, super] current)

-- Helper method to retrieve an error message from a list of class type-check outputs
getErrorMessage :: [(Int, [String], [String], String)] -> String
getErrorMessage [] = ""
getErrorMessage classRets = 
    let (err, pl, nl, t) = head classRets in
        if err == 0 then
            getErrorMessage (tail classRets) -- Call self recursively if no error
        else
            head pl -- Return the error if there is one

---------------------------------------------
--- Main Function
--      do all IO, program halting, etc. here
--- acl3qb, bjg4uc
---------------------------------------------

main = do

    -- Haskell file input
    args <- getArgs
    let file_name = head args
    handle <- openFile file_name ReadMode
    all_input_as_one_string <- hGetContents handle
    let all_input_as_lines = lines all_input_as_one_string
        all_lines = tail all_input_as_lines
        classes_lines = get_classes_lines all_lines [[]]

        -- default methods
        abort = ["method","0","abort","0","0","Object","internal","Object.abort"]
        copy = ["method","0","copy","0","0","SELF_TYPE","internal","Object.copy"]
        type_name = ["method","0","type_name","0","0","String","internal","Object.type_name"]
        str_concat = ["method","0","concat","1","0","s","0","String","0","String","internal","String.concat"]
        str_length = ["method","0","length","0","0","Int","internal","String.length"]
        str_substr = ["method","0","substr","2","0","i","0","Int","0","l","0","Int","0","String","internal","String.substr"]
        in_int = ["method","0","in_int","0","0","Int","internal","IO.in_int"]
        in_string = ["method","0","in_string","0","0","String","internal","IO.in_string"]
        out_int = ["method","0","out_int","1","0","x","0","Int","0","SELF_TYPE","internal","IO.out_int"]
        out_string = ["method","0","out_string","1","0","x","0","String","0","SELF_TYPE","internal","IO.out_string"]
        
        -- list of classes without inherited features, organized as tuples
        classes = [
            ("Object", ("0", "", [], [[abort, copy, type_name]])),
            ("Int", ("0", "Object", [], [[]])),
            ("String", ("0", "Object", [], [[str_concat, str_length, str_substr]])),
            ("Bool", ("0", "Object", [], [[]])),
            ("IO", ("0", "Object", [], [[in_int,in_string,out_int,out_string]]))
            ] ++ (map get_class classes_lines)
         
        class_names = [fst x | x <- classes] -- Names of all the classes
        class_map = get_class_map (tail classes) (head classes) -- Add inherited features
        sorted_map = sort class_map
        bad_inheritance = check_bad_inheritance sorted_map class_names -- Check for inheritance errors
    if (check_non_inheritance class_names classes_lines) /= "" then -- Check for inheritance from classes that don't exist
        putStrLn (check_non_inheritance class_names classes_lines)
    else if bad_inheritance /= "" then 
        putStrLn bad_inheritance
    else if not (elem "Main" class_names) then -- Check for main class
        putStrLn "ERROR: 0: Type-Check: class Main not found"
    else if (length classes) > (length class_map) then -- Check for an inheritance cycle by comparing number of classes to reach inheritance tree nodes from Object
        putStrLn "ERROR: 0: Type-Check: 'I'm my own grandpa'"
    else do
    let outfile = (take ((length file_name)-3) file_name)++"type" -- Format the name of the output file
        parentMap = makeClassMap [(c,i) | (c, (l, i, a, m)) <- class_map]  Map.empty -- Make the parent map which will be used for type-checking
        attrMap = Map.fromList (concat [makeAttrMap c (concat a) | (c, (l,i,a,m)) <- class_map]) -- Make the attribute map
        methodMap = Map.fromList (concat [makeMethodMap c (concat m) | (c, (l,i,a,m)) <- class_map]) -- Make the method map
        aast = map (\x -> typeCheckClass attrMap methodMap parentMap (x !! 1) [] x) (reverse classes_lines) -- Write the annotated abstract syntax tree
        parsed = concat [done | (err, done, parse, t) <- aast] -- Concatenate the parts of the annotated AST together
        errorMessage = getErrorMessage aast --Check for errors
    if errorMessage == "" then do -- If there was no error
        writeFile outfile ""
        -- print the class map
        appendFile outfile "class_map\n" -- Label
        appendFile outfile ((show (length classes))++"\n") -- Number of classes

        mapM (\(n,(l,i,a,m)) -> do -- Complicated map to print the attributes of the classes
            let new_a = [(aa:ac:tl) | (aa:ab:ac:ad:tl) <- (concat a)] -- Gets just the attributes part of the class list
            appendFile outfile (n++"\n")
            appendFile outfile ((show (length new_a))++"\n")
            -- This 2-line fix type-checks all of the expressions in the class map.
            -- It maps an expression check onto the whole list of attributes and then gets the lines from that.
            let tuples = map (\x -> if (length x) > 3 then exprCheck attrMap methodMap parentMap n (take 3 x) (drop 3 x) else (0, (take 3 x), [], "empty attr")) new_a 
            let newer_a = [pl | (err, pl, nl, t) <- tuples]
            mapM (\x -> appendFile outfile x) (map unlines newer_a) -- Map to append to file
            ) sorted_map

        -- print the implementation map
        appendFile outfile "implementation_map\n"
        appendFile outfile (full_imp_map sorted_map)

        -- print the parent map
        appendFile outfile "parent_map\n"
        appendFile outfile ((show ((length classes) - 1))++"\n")
        mapM (\(n,(l,i,a,m)) -> do
            if n /= "Object" then
                appendFile outfile (n++"\n"++i++"\n")
            else
                return ()
            ) sorted_map
        
        appendFile outfile ((show (length classes_lines))++"\n")
        appendFile outfile (intercalate "\n" parsed) -- Print the annotated AST which newlines after each line
    else
        putStrLn errorMessage -- If there is an error, print it
    -- dummy return
    return ()