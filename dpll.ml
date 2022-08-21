open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]

(********************************************************************)

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral i à vrai *)
let simplifie i clauses =
    (* Retourne vrai si l'élément `x` est présent dans la liste `l`, sinon faux. *)
    let rec present x l = match l with
      | [] -> false
      | y :: l' -> if x = y then true else present x l' in
    (* Filtre supprimant les clauses contenant `i`. *)
    let filter_true l = if present i l then None else Some l in
    (* Récupere la liste des clauses ne contenant pas `i`. *)
    let false_clauses = filter_map (filter_true) clauses in


    (* Filtre supprimant le littéral inverse de `i`. *)
    let filter_neg x = if x = (~-i) then None else Some x in
    (* Filtre supprimant les éléments inverse de `i` dans la clause. *)
    let filter_false l = filter_map (filter_neg) l in
    (* Retourne une liste de liste `ll` filtré par le filtre `f` *)
    let rec ll_filtering f ll = match ll with
      | [] -> []
      | l' :: ll' -> (f l') :: (ll_filtering f ll') in
    (* Retourne la simplification des clauses de `false_clauses` par l'inverse `i`. *)
    let double_inverted_clauses = ll_filtering filter_false false_clauses in


    (* Inverse l'ordre des clauses de `double_inverted_clauses` pour réordonner (voir `filter_map`). *)
    let inverted_clauses = filter_map (function l -> Some l) double_inverted_clauses in
    (* Inverse l'ordre des littéraux dans une clause. *)
    let filter_invert l = filter_map (function x -> Some x) l in
    (* Inverse les clauses de `inverted_clauses` pour réordonner. *)
    ll_filtering filter_invert inverted_clauses

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* un clause vide est insatisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
(* let () = print_modele (solveur_split systeme []) *)
(* let () = print_modele (solveur_split coloriage []) *)

(* solveur dpll récursif *)
    
(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)
let unitaire clauses =
  (* Retourne vrai si une clause est unitaire, sinon faux. *)
  let is_unit l = match l with
    | _ :: [] -> true
    | _ -> false in

  (* Retourne un littéral si la clause est unitaire, sinon lève une exception. *)
  let rec search_unit ll = match ll with
    | [] -> raise Not_found
    | l' :: ll' -> if is_unit l' then List.hd l' else search_unit ll' in
  (* Effectue la recherche de clause unitaire sur `clauses`. *)
  search_unit clauses

(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)
let pur clauses =
  (* Récupère une liste de littéraux en concaténant tous les littéraux des sous-listes de `clauses`.
     Il est possible d'apercevoir des répétitions. *)
  let list_litteraux = List.concat clauses in
  (* Retourne vrai si l'inverse du littéral `x` n'est pas dans la liste `l`. *)
  let rec is_pur x l = match l with
	| [] -> true
	| y::t -> if y = (~-x) then false else is_pur x t in
  (* Retourne un littéral pur si la liste en contient un ou lève une exception sinon. *)
  let rec list_parcour l l_init = match l with
	| [] -> raise (Failure "pas de littéral pur")
	| x::t -> if is_pur x l_init then x else list_parcour t l_init in
  (* Effectue la recherche de littéral pur sur la liste des littéraux. *)
  list_parcour list_litteraux list_litteraux
  

(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  (* Retourne `interpretation` si clauses est égal à l'ensemble vide (car il est satisfiable). *)
  if clauses = [] then Some interpretation else
  (* Retourne `None` si l'une des clauses est vide (car une clause vide est insatisfisable). *)
  if mem [] clauses then None else

  (* Simplifie les clauses unitaires par leur littéral. *)
  try let unit_litteral = unitaire clauses in solveur_dpll_rec (simplifie unit_litteral clauses) (unit_litteral::interpretation) with
    Not_found -> 

      (* Simplifie les littéraux pures par le littéral en question. *)
  		try let pur_clauses = pur clauses in solveur_dpll_rec (simplifie pur_clauses clauses) (pur_clauses::interpretation) with
  			Failure _ -> 

  				(* Heuristique de branchement. *) 
  				let l = hd (hd clauses) in
  				let branche = solveur_dpll_rec (simplifie l clauses) (l::interpretation) in
  				match branche with
  				| None -> solveur_dpll_rec (simplifie (-l) clauses) ((-l)::interpretation)
  				| _    -> branche

(* tests *)
(* let () = print_modele (solveur_dpll_rec systeme []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)

let () =
  (* Vérifie si un argument (fichier DIMACS) est passé en argument. *)
  if Array.length Sys.argv > 1 then 
    (* Si c'est le cas, on effectue l'algorithme DPLL sur ce fichier. *)
    let clauses = Dimacs.parse Sys.argv.(1) in
    print_modele (solveur_dpll_rec clauses [])
  else
    (* Sinon on ne fait rien. *)
    print_string "usage: ./dpll file.cnf\n"
