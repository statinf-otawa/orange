(* cextraireboucle -- use Frontc CAML change loop to normelized loop, construct instructions to eval abstract store, construct flowfact
**
** Project:	O_Range
** File:	cextraireboucle.ml
i** Version:	1.1
** Date:	11.7.2008
** Author:	Marianne de Michiel
*)

open Cabs
open Frontc

let version = "cextraireboucle Marianne de Michiel"

open Cprint
open Cexptostr
open Cvarabs
open Cvariables
open Constante
open Coutput
open Increment
open Printf

let out_dir = ref "."

let files: string list ref = ref []
let names : (string ref) list ref =  ref[]

let add_file filename =
	files := List.append !files [filename]

let transfo_into_ref (filename:string)=[(ref filename)]

let add_name (filename:string) =
	names := List.append !names (transfo_into_ref filename)

let fich name =
	let size=String.length name in
	( ((String.get name (size-2))=='.') && ((String.get name (size-1))=='c' )) 

let rec  sort_list_file_and_name li= 
	match li with
	[e] ->  if (fich e) then add_file (e) else add_name (e)
	|e::l -> if (fich e) then begin add_file (e) ; sort_list_file_and_name l end else begin add_name (e) ; sort_list_file_and_name l end
	|[]-> failwith ("parsing out")

let set_out_dir rdir =
	out_dir := rdir

let use_partial = ref []
let add_use_partial name =
       use_partial := name :: (!use_partial)

							

let is_in_use_partial name =
	let rec is_in up_list =
	        match up_list with
        		| up_name :: t ->
	        		(up_name = name) || (is_in t)
                        | [] -> false
        in (is_in !use_partial)

let (mainFonc :string ref ref) =ref( ref "")
let (evalFunction:( string ref) list ref)= (ref [])

let maj hd tl =
	begin
	mainFonc := ref hd;
	evalFunction := (List.append !evalFunction tl)
	end
	

let nonamedForTypeDef = ref ""
let  fileCour = ref "nodef" 
let  numLine = ref 0
let isExactForm = ref false
let nomFctCour = ref !(!mainFonc)

let aUneFctNotDEf = ref false   
(* les expressions caracterisant une boucle for *)
	let expressionDinitFor = ref NOTHING

	let expressionCondFor = ref NOTHING
	let listeDesInstCourantes = ref []
	let listeDesInstGlobales = ref []
	(*let alreadyAffectedGlobales = ref [] *)(* pas chez Clément*)
	let listeAffectInit = ref []

	let trueList = ref []
	let falseList = ref []

(* pour les boucles *)
	let idBoucle = ref 0
	let idBoucleEng = ref 0
	let idIf = ref 0
	let idSwitch = ref 0
	let nbImbrications = ref 0
	let nbImbricationsMaxAppli = ref 0
	let borne = ref NOTHING
	let increment = ref NOTHING
	let initialisation = ref NOTHING
	
	type listeDesIdDeBoucle = int list
	type elementCorpsFonction =
		IDBOUCLE of int * string list * string list *string*int(*  fic*line *)
	|	IDAPPEL of int * expression *inst list *string  * string list * string list *string*int(*  fic*line *)
	|	IDIF of string * inst list * elementCorpsFonction list (*then*)* inst list* elementCorpsFonction list(*else*)* string list * string list
	
	type refAppel = string * int (* id fichier numline*)

	let listAssosTypeDefArrayIDsize  = ref [(" ", NOSIZE)]
	 
	(*let listeAssosPtrNameType = ref []*)
	let setAssosIDTYPEINIT = ref []

	(*let setAssosIDBasetype name typ =
	if (List.mem_assoc name !listAssocIdType)= false then 
			listAssocIdType := List.append !listAssocIdType [(name, get_base_typeEPS typ)]   *)


	

	let existAssosTypeDefArrayIDsize  name  = (List.mem_assoc name !listAssosTypeDefArrayIDsize)
	let setAssosTypeDefArrayIDsize  name size = 
		if existAssosTypeDefArrayIDsize name = false then listAssosTypeDefArrayIDsize := List.append   [(name, size)]   !listAssosTypeDefArrayIDsize 	

	let getAssosTypeDefArrayIDsize name  = if existAssosTypeDefArrayIDsize name then (List.assoc name !listAssosTypeDefArrayIDsize) else NOSIZE
	
	let listLoopIdRef = ref []
	let listIdCallFunctionRef =ref  []
	let exitsAssosIdLoopRef id = List.mem_assoc id !listLoopIdRef
	let setAssosIdLoopRef id refe = if exitsAssosIdLoopRef id = false then listLoopIdRef := List.append   [(id, refe)]   !listLoopIdRef

	let getAssosIdLoopRef id = if exitsAssosIdLoopRef id then List.assoc id !listLoopIdRef else ("",0)

	let print_AssosIdLoopRef l=
		List.iter (fun (a, (f,num)) -> Printf.printf "Loop %d fichier %s ligne %d \n" a f num) l 	
	let print_listIdCallFunctionRef l=
		List.iter (fun (a, (f,num)) -> Printf.printf "Function %d fichier %s ligne %d \n" a f num) l 	

	let exitsAssosIdCallFunctionRef id = List.mem_assoc id !listIdCallFunctionRef
	let getAssosIdCallFunctionRef id = if  exitsAssosIdCallFunctionRef id  then List.assoc id !listIdCallFunctionRef else ("",0)
	let setAssosIdCallFunctionRef id refe = if exitsAssosIdCallFunctionRef id = false then listIdCallFunctionRef := List.append   [(id, refe)]   !listIdCallFunctionRef

	let getListOfLine = (!listIdCallFunctionRef, !listLoopIdRef)
	let setListOfLine lc ll=listLoopIdRef:=ll;  listIdCallFunctionRef:=lc
	
	let rec getArraysize typ =
        match typ with
			ARRAY (t, dim) -> 
				let size =
					match calculer  (EXP(dim)) !infoaffichNull  [] 1 with  
						ConstInt(s)	-> let dime = int_of_string  s in (*Printf.printf "%d \n"dim; *) [dime]
						|_			-> [] in
				List.append (getArraysize t) size
			| 	_ -> []

let listOfArrayType = ref [](*[(" ", NO_TYPE)]*)

	let existAssosArrayType   name  = (List.mem_assoc name !listOfArrayType)
	let setAssosArrayType   name typ = 
		if existAssosArrayType name = false then listOfArrayType := List.append   [(name, typ)]   !listOfArrayType 	

	let getAssosAssosArrayType name  = if existAssosArrayType name then (List.assoc name !listOfArrayType) else NO_TYPE


	
	let rec nbItems l  = if l = [] then 0 else nbItems (List.tl l) +1 

	let majAssosArrayIDsize name typ exp=
	(*Printf.printf "dans majAssosArrayIDsize %s\n" name;*)
	let liste = getArraysize typ in
	setAssosArrayType   name typ ;
	(*List.iter(fun dim-> Printf.printf "%d  " dim; )liste;*)
	if liste <> [] then
	begin
		if List.tl liste != [] then  setAssosArrayIDsize name (MSARRAY liste)
		else  setAssosArrayIDsize name (SARRAY  (List.hd liste))
	end
	else if exp = NOTHING then setAssosArrayIDsize name NOSIZE
		 else
		 begin
			match exp with CONSTANT(CONST_COMPOUND s) -> setAssosArrayIDsize name (SARRAY  (nbItems s)) |_->setAssosArrayIDsize name NOSIZE
		 end



	let majTypeDefAssosArrayIDsize name typ exp=
	(*Printf.printf "dans majTypeDefAssosArrayIDsize %s\t" name;*)
	let liste = getArraysize typ in
	(*List.iter(fun dim-> Printf.printf "%d  " dim; )liste;Printf.printf "\n" ;*)
	if liste <> [] then
	begin
		if List.tl liste != [] then  setAssosTypeDefArrayIDsize name (MSARRAY liste)
		else  setAssosTypeDefArrayIDsize name (SARRAY  (List.hd liste))
	end
	else   setAssosTypeDefArrayIDsize name NOSIZE 

		

	let print_AssosArrayIDsize l=
		List.iter (fun (a, b) -> Printf.printf "%s  " a; 
					match b with 
						 NOSIZE -> Printf.printf "NOSIZE\n"
						| SARRAY (v) -> Printf.printf "SINGLE ARRAY %d\n" v
						| MSARRAY (l) ->  Printf.printf "MULTI ARRAY ";List.iter(fun dim-> Printf.printf "%d  " dim; )l ;Printf.printf "\n"
				   ) l 	

	(*let print_AssosPtrTypeList l=
		List.iter (fun (a, b) -> Printf.printf "%s  " a;  print_base_type b true; new_line()  ) l 	*)
	
type variation =
{
	borneInf : expression;
	borneSup : expression;
	increment : expression;
	direction : sens;
	operateur :  binary_operator ;
	afterindirect : bool;
}

let new_variation i s inc d op b=
{
	borneInf =i;
	borneSup =s;
	increment =inc;
	direction = d;
	operateur = op;
	afterindirect = b; (* if indirect and after *)
} 
	
	type boucleInfo =
	{
		typeBoucle : string;
		nomEnglobante : int;
		identifiant : int;
		lesVariablesNbIt :string list;  (* liste des variables de la condition ou modifiant la condition*)
		degreb :int; 
		conditionConstante : bool; (*exemple while 1...*)
		conditionMultiple : bool;
		conditionI :expression;
		boucleOuAppelB : elementCorpsFonction list;
		infoVariation : variation;
		estPlus : bool;
	}
	
	type infoInitBoucleFor =
	{
		variable : string;
		valeur : expression;
	}
	
	let new_infoInitBoucleFor id exp =
	{
		variable = id;
		valeur = exp;
	}
		
	type boucleFor =
	{
		boucleInitiale : boucleInfo;
		lesVariablesInit : string list ; 
		valInit : infoInitBoucleFor;
		c :expression; (* increment du for *)
		n :expression; (* borne sup du for *)
	}

	type boucleWhileOuDoWhile =
	{
		boucleI : boucleInfo;
		initialisation :expression list; (* increment du for *)
		incrementations :expression list; (* borne sup du for *)
	}
		
	type boucle =
		BOUCLEFOR of boucleFor
		| AUTRE of boucleWhileOuDoWhile
		
	let new_bouclef   b  = BOUCLEFOR(b)
	let new_boucleA i = AUTRE(i)
	
	type listeDesBoucles = boucle list

	type infoBorneDeBoucle =
	{
		laBoucle : boucle;
		expressionBorne : expression;
		lesAffectationsB : listeDesInst;
		isExactExp : bool;
	}
			
	type nidDeBoucle =
	{
		condN : expression;	
		infoNid : infoBorneDeBoucle; 
		varDeBoucleNid : string;
		lesAffectationsBNid : listeDesInst; (* les modif des var *)
		listeTripletNid : (int list * abstractStore list *nidDeBoucle)list; 
	}
	
	let new_NidDeBoucle c i v la lc =
	{
		condN = c;
		infoNid =i;
		varDeBoucleNid =v;
		lesAffectationsBNid =la;
		listeTripletNid =lc;	
	}		
	
	let new_infoBorneDeBoucle b exp liste exact=
	{
		laBoucle = b;
		expressionBorne = exp;
		lesAffectationsB = liste;
		isExactExp = exact;
	}
	
	let new_boucleInfoVide =
	{
		typeBoucle ="";
		nomEnglobante =0;
		identifiant =0;
		lesVariablesNbIt =[];  
		degreb =0; 
		conditionConstante  = true; (*exemple while 1...*)
		conditionMultiple =false;
		conditionI =NOTHING;
		boucleOuAppelB = [];
		infoVariation = new_variation NOTHING NOTHING NOTHING NONMONOTONE ADD false;
		estPlus = true;
	}

	let new_boucleInfo typeb id l deg eng  condcte cond multiple liste vari b= 
	{
		typeBoucle = typeb;
		nomEnglobante = eng;
		identifiant = id;
		lesVariablesNbIt = l;
		degreb = deg;
		conditionConstante = condcte; (*exemple while 1...*)
		conditionI = cond;
		conditionMultiple =multiple;
		boucleOuAppelB = liste;
		infoVariation = vari;
		estPlus =b;
	}
	
	let new_boucleWhileOuDoWhile b linit linc =
	{
		boucleI =b;
		initialisation =linit; (* increment du for *)
		incrementations =linc; (* borne sup du for *)
	}

	let  new_infoBorneDeBoucleVide =
	{
		laBoucle = new_boucleA (new_boucleWhileOuDoWhile new_boucleInfoVide [] []) ;
		expressionBorne = NOTHING;
		lesAffectationsB = [];
		isExactExp = false;
	}
	
	let new_NidDeBoucleVide = 
	{
		condN = NOTHING;		
		infoNid =new_infoBorneDeBoucleVide;
		varDeBoucleNid ="";
		lesAffectationsBNid =[];
		listeTripletNid =[];
		
	}
	let new_boucleFor b liste var init exp2 exp3  =
	{
		boucleInitiale = b;
		lesVariablesInit = liste; 
		valInit = new_infoInitBoucleFor var init (*chaineInit*); (*nom var du for*)
		c = exp3; (* increment du for si X deviendra une liste*)
		n =exp2; (* borne sup du for *)
	}

	let noeudCourant = ref new_NidDeBoucleVide
	let listeNoeudCourant = ref []
	let listeBouclesImbriquees = ref []
	let listeDesBouclesDuNidCourant = ref  [] (* en fait il faut une liste et une pile*)
	let listeTripletNidCourant = ref []
	let listeTripletNidCourantPred = ref []
		
	let getBoucleIdB b =
		match b with 
		BOUCLEFOR  bf ->  bf.boucleInitiale.identifiant
		| AUTRE    bi->	bi.boucleI.identifiant
						
	let getBoucleInfoB b =
		match b with
		BOUCLEFOR (bf) -> bf.boucleInitiale
		| AUTRE (ba) -> ba.boucleI
		
	type listeDesAssosBoucleBorne = infoBorneDeBoucle list
	let idFonction = ref 0
	let idAppel = ref 0	
	type typeListeAppels = expression list
	let listeDesNomsDeFonction = ref []
	
	type typeCorpsFonction =
	{
		(*listeDesBouclesDansCorps: listeDesIdDeBoucle;	*)
		boucleOuAppel : elementCorpsFonction list;
		corpsS : statement;	
		(*listeDesAppelDeFonctionsDansCorps : typeListeAppels ;*)
	}
	
	type typeES =
	  ENTREE of string
	| SORTIE of string
	| ENTREESORTIE of string
	
	type listeDesES = typeES list
	
	type typeInfofonction =
	{  nom : string;
		declaration : single_name;
		corps : typeCorpsFonction;
		lesAffectations : listeDesInst;
		listeES : listeDesES;
	}
	
	let getCorpsFonction f = f.corps
	(*let getListeDesBouclesFonction f = f.corps.listeDesBouclesDansCorps*)
	
	type listeDesFonctions = (int * typeInfofonction) list

(* pour le document *)
	type document =
	{
		laListeDesBoucles:listeDesBoucles ;
		laListeDesFonctions:listeDesFonctions;
		laListeDesAssosBoucleBorne : listeDesAssosBoucleBorne;
		laListeDesNids : nidDeBoucle list;
	}
  
	let new_document lb lf la ln=
	{
		laListeDesBoucles = lb;
		laListeDesFonctions = lf;
		laListeDesAssosBoucleBorne =la;
		laListeDesNids = ln;
	}
	
	let add_fonction  (n,f) liste= if (List.mem_assoc n liste)= false then 	List.append liste [(n,f)]	else liste
	let doc = ref (new_document [] [] [] [])
	let enumCour = ref NO_TYPE


module TreeList = struct
  type tree = Doc of tree list
         | Function of (string * bool * bool * bool) * tree list (* function name, inloop, executed, extern *)
         | Call of (string * int * int * string * bool * bool * bool *expression*expression) * tree list (* function name, relative call ID, line num, source file, inlopo, executed, extern *)
         | Loop of (int * int * string * bool * expressionEvaluee * expressionEvaluee * expression * expression * expression * sens *expression *expression) * tree list (* loop id, line, source file, exact, max, toatl, exp max, exp total *)

 
  
  type t = tree * tree list  (* current, ancestor stack *)
  let null = (Doc [], [])
  exception TreeBuildException
  
  let addChild node : tree -> tree = function
     (Doc children) -> (Doc (node::children)) 
    |Function (x, children) -> Function (x, (node::children))
    |Call (x, children) -> Call (x, (node::children))
    |Loop (x, children) -> Loop (x, (node::children))
    
  let onBegin = function
      (Doc [], [] ) as x -> x
      | _ -> raise TreeBuildException
        

  let onEnd = function
      (Doc _, []) as x -> x
      | _ -> raise TreeBuildException
  
  let onFunction res name inloop executed extern   = match res with
      (current, stack) -> 
        let newCurrent = Function ((name,inloop,executed,extern ), []) in
	(newCurrent, current::stack)      

  let onLoop res loopID line source exact maxcount totalcount maxexp totalexp expinit sens et ef= match res with
      (current, stack) -> 
        let relativize valname = 
	  try
	    Scanf.sscanf valname "bIt-%d" (fun x -> (sprintf "bIt-%d" (x-1)))
	  with Scanf.Scan_failure str -> valname
	  in
        let maxexp = mapVar relativize maxexp in
	let totalexp = mapVar relativize totalexp in
        let newCurrent = 
	   Loop ((loopID - 1, line, source, exact, maxcount,  totalcount, ( maxexp),( totalexp), expinit, sens, et, ef), []) in
	(newCurrent, current::stack)   
     
  
  let onCall res name numCall line source inloop executed extern lt lf = match res  with
      (current, stack) -> 
        let newCurrent = Call ((name, numCall, line, source, inloop, executed, extern,lt , lf ), []) in
	(newCurrent, current::stack)   

  let onFunctionEnd = function
      (current, item::stack) -> (addChild current item), stack
      |(_, []) -> raise TreeBuildException
        	
  let onReturn = onFunctionEnd
  let onLoopEnd = onFunctionEnd 
  
  let concat _ _ = failwith "pas supporte\n";


end ;;


open TreeList


type compInfo = {name:string; absStore: typeListeAS; compES:listeDesES; expBornes:TreeList.tree}



let rec getItemList dec result=
if dec = [] then result
else
begin
	let (head, others) = (List.hd dec, List.tl dec) in
	let nl =get_name_group head in
	getItemList others (List.append result nl)
end

and get_name_group (typ, _, names) = makeListItem (get_base_typeEPS typ) names []


and makeListItem typ names result =
if names =[] then result
else
begin
	let ((id, t, _, _), others) = (List.hd names, List.tl names) in
	makeListItem typ others (List.append result [(id, get_base_typeEPS  t)])
end

and get_base_typeEPS  ntyp = 
	match ntyp with
	 PROTO (typ, _, _)| OLD_PROTO (typ, _, _)| PTR typ | RESTRICT_PTR typ | ARRAY (typ, _) | CONST typ | VOLATILE typ | GNU_TYPE (_, typ) | TYPE_LINE (_, _, typ) ->   get_base_typeEPS typ 
	| FLOAT (_) | DOUBLE (_) |NO_TYPE -> FLOAT_TYPE
	| NAMED_TYPE id  ->   TYPEDEF_NAME(id)
	| STRUCT (id, dec) -> 
			 	 
			let nid = if id ="" then 
				((*Printf.printf "NONAMMED STRUCT %s_T\n"!nonamedForTypeDef; *)Printf.sprintf "%s_T"  !nonamedForTypeDef) else id in
			
			if  (List.mem_assoc nid !listAssosIdTypeTypeDec)= false then 
					listAssosIdTypeTypeDec := List.append !listAssosIdTypeTypeDec [(nid,  newDecTypeSTRUCTORUNION (getItemList dec []))];
						
						let newType = STRUCT_TYPE (nid) in
						(*printfBaseType newType;*)
						newType
			
	| UNION (id, dec) ->   
			let nid = if id ="" then ((*Printf.printf "NONAMMED UNION %s_T\n"!nonamedForTypeDef;*) Printf.sprintf "%s_T"  !nonamedForTypeDef) else id in
			if  (List.mem_assoc nid !listAssosIdTypeTypeDec)= false then 
					listAssosIdTypeTypeDec := List.append !listAssosIdTypeTypeDec [(nid, newDecTypeSTRUCTORUNION (getItemList dec []))]; 					  
						UNION_TYPE (nid) 
	| ENUM (id, items) -> enumCour := ntyp; INT_TYPE
	| _->   INT_TYPE

	

	let setAssosPtrNameType  name t =if (List.mem_assoc name !listeAssosPtrNameType)= false then  listeAssosPtrNameType := List.append   [(name,get_base_typeEPS t)]   !listeAssosPtrNameType 	
	let existAssosPtrNameType  name  = (List.mem_assoc name !listeAssosPtrNameType)
	let getAssosPtrNameType name  = (List.assoc name !listeAssosPtrNameType)


(* fonction de recherche booleenne *)
	let rec estProto typ =
		match typ with
		  PROTO (_, _, _) | OLD_PROTO (_, _, _) ->	true
		| GNU_TYPE (_, typ) ->estProto typ
		| _ -> false
	
	let rec estPtrOuTableau typ =
	  match typ with
	  PTR _| RESTRICT_PTR _ | ARRAY (_, _) -> true
	| CONST typ -> estPtrOuTableau typ
	| VOLATILE typ -> estPtrOuTableau typ
	| GNU_TYPE (_, typ) ->estPtrOuTableau typ
	| _ -> false

	let rec isPtrType typ =
(*Printf.printf "isPtrType\n";*)
	  match typ with
	  PTR _| RESTRICT_PTR _ -> true
	| CONST typ -> isPtrType typ
	| VOLATILE typ -> isPtrType typ
	| GNU_TYPE (_, typ) ->isPtrType typ
	| ARRAY (typ, _) -> isPtrType typ
	| _ -> (*Printf.printf "isPtrType default\n";*)false
			
	
(* pour les fonctions *)
	
let  rec reecrireCAll var liste =
List.map (fun e -> 
	match e with
			IDBOUCLE (_,_,_,_,_) -> e
		|	IDAPPEL (i , expression, l,_,lt,lf,fic,lig) -> IDAPPEL (i , expression, l,var,lt,lf,fic,lig) 
		|	IDIF (var,instthen, treethen,instelse, treeelse,lt,lf) ->IDIF (var,instthen, reecrireCAll var treethen,instelse, reecrireCAll var treeelse,lt,lf) 

) liste


let nomFonctionDeExp exp = match exp with  VARIABLE (s)->s  | _->""

(* pour les boucles *)
let new_ListeDesBoucles oldList newBoucle = List.append oldList newBoucle
let aBoucleEnglobante bInfo = if bInfo.degreb != 1 then true else false

let existeBoucle id =
	List.exists (fun bou -> 
			match bou with 
			BOUCLEFOR  bf -> bf.boucleInitiale.identifiant = id
			| AUTRE    bi->	bi.boucleI.identifiant = id
			) !doc.laListeDesBoucles 
			
	let rechercheBoucle id =
		List.find (fun bou -> 
			match bou with 
				BOUCLEFOR  bf -> bf.boucleInitiale.identifiant = id
				| AUTRE    bi->	bi.boucleI.identifiant = id
			) !doc.laListeDesBoucles 

	let existeAssosBoucleBorne id =
		List.exists (fun bou -> 	(getBoucleIdB bou.laBoucle) = id) !doc.laListeDesAssosBoucleBorne 
	let rechercheAssosBoucleBorne id =
		List.find (fun bou ->	 (getBoucleIdB bou.laBoucle) = id) !doc.laListeDesAssosBoucleBorne 	
				
(* pour les fonctions *)

	let new_CorpsFonction  bloc lbOa  =
	{
	(*	listeDesBouclesDansCorps = listeB;	*)
		boucleOuAppel = lbOa;
		corpsS = bloc;
		(*listeDesAppelDeFonctionsDansCorps = l;*)
	} 
	let listeBoucleOuAppelCourante = ref []
	
	let new_Infofonction n dec c l liste=
	{
		nom = n ;
		declaration =dec ;
		corps = c;
		lesAffectations = l;
		listeES = liste;
	}
	
	let new_entree s= ENTREE (s)
	let new_sortie s = SORTIE (s)
	let new_ES s = ENTREESORTIE (s)

	let listeRes = ref []


(* we have to show how to consider union and struct type *)

	(*let setIdInitType name typei = if List.mem name *)
	let setAssosIDBasetype name typ =
	if (List.mem_assoc name !listAssocIdType)= false then 
	begin
			
			listAssocIdType := List.append !listAssocIdType [(name, get_base_typeEPS typ)]   ;
			setAssosIDTYPEINIT := List.append  [(name,  typ)]  !setAssosIDTYPEINIT;
	end

let rec  prodListSize l =
if l = [] then ConstInt ("1")
else  evalexpression(	Prod (ConstInt (Printf.sprintf "%d" (List.hd l)), prodListSize (List.tl l) ))

let rec getItemType dec result=
if dec = [] then result
else
begin
	let (head, others) = (List.hd dec, List.tl dec) in
	let nl =get_type_group head in 
	let aux = if others = [] then "" else "," in
	getItemType others ( result ^ nl ^ aux)
end

and get_type_group (typ, _, names) = makeListType (get_baseinittype typ) names ""

and makeListType typ names result =
if names =[] then result
else
begin
	let ((id, t, _, _), others) = (List.hd names, List.tl names) in
	let aux = if others = [] then (get_baseinittype t) else (get_baseinittype t)^"," in
	makeListType typ others (result^ aux)
end

and get_baseinittype typ =
	match typ with
	NO_TYPE ->   "int"
	| VOID ->    "void"
	| CHAR sign ->   ((get_sign sign) ^ "char")
	| INT (size, sign) ->   ((get_sign sign) ^ (get_size size) ^ "int")
	| BITFIELD (sign, _) ->   ((get_sign sign) ^ "int")
	| FLOAT size ->   ((if size then "long " else "") ^ "float")
	| DOUBLE size ->   ((if size then "long " else "") ^ "double")
	| NAMED_TYPE id ->		"type_mamed_" ^ id
	| ENUM (id, items) -> 	if id = "" then  Printf.sprintf "ENUM_OF_NBITEMS_%d" (nbItems items)  else "ENUM_" ^  id  
	| STRUCT (id, dec) ->  if id = "" then  "struct_{" ^ (getItemType dec "")  ^ "}" else "struct_" ^ id 
	| UNION (id, dec) ->  	if id = "" then  "union_{" ^ (getItemType dec "")  ^ "}" else "union_" ^ id
	| PROTO (typ, _, _) -> "proto"
	| OLD_PROTO (typ, _, _) -> "proto"
	| PTR typ -> "PTR"
	| RESTRICT_PTR typ -> "PTR"
	| ARRAY (t, _) -> let liste = getArraysize typ in
			let nbelt =
						(if liste != [] then  
						begin
							if List.tl liste != [] then 
							begin 
								(match expressionEvalueeToExpression (prodListSize liste)  with
													CONSTANT (CONST_INT (s))->" *" ^ s
													| _->"* unkown_size")  
							end
							else  Printf.sprintf "* %d"  (List.hd liste)
						end
						else "" ) in
						   
							
			get_baseinittype t ^nbelt
	| CONST typ -> get_baseinittype typ
	| VOLATILE typ -> get_baseinittype typ
	| GNU_TYPE (attrs, typ) ->  "gnuType"
	| TYPE_LINE (_, _, _type) ->"TypeLine"



	
	let 	rec creerListeParamES (pars : single_name list) =
		if pars = [] then begin if !vDEBUG then Printf.printf"aucun param \n";()end
		else
		begin	(*	Printf.printf"traitement liste param creerListeParamES\n";*)
			let courant = List.hd pars in
			let (typ, _, name) = courant in
			let (nom, estPtrOuTab) = traiter_single_name name typ in
			if nom != "" then 
			begin 
				setAssosIDBasetype nom typ;
				
			end;

		(*	Printf.printf "liste des variables et leur type\n";
			List.iter (fun (id,typ) -> Printf.printf "VARIABLE %s " id ; Printf.printf "de type "; printfBaseType typ; new_line()) !listAssocIdType;
			Printf.printf "fin liste des variables et leur type\n";*)
			if	(estPtrOuTab= false) then 		
				listeRes :=  List.append !listeRes [new_entree nom]  
			else 		
			begin
				(*if isPtrType typ then  *)
				begin
					(*Printf.printf "ajoute tab\n";*)
					if existAssosPtrNameType  nom = false then begin setAssosPtrNameType  nom typ;  end;
				end	;
				listeRes :=  List.append !listeRes [new_ES nom]	;	
			end		;	
			creerListeParamES (List.tl pars) 
		end
		
	and traiter_single_name name typ =
		let (id, typeAux, _, _) = name in
		(id, (estPtrOuTableau typeAux) || (estPtrOuTableau typ) )

		
	let creerListeES proto  =
		let (typ,_,name) = proto in	(*(typ, sto, name)*)		
		let (id, parametres, _, _) = name in		(*(id nom fonction, typ, attr, exp) *)
		let base = get_base_type parametres in
		match base with
		 PROTO (_, pars, ell) -> 	(*Printf.printf "DANS CREER LISTE DES ES PROTO\n";*)
				creerListeParamES pars ; 
				if ell then if !vDEBUG then Printf.printf "suite non traitee actuellement";()
		| OLD_PROTO (_, _, ell)(*(typ, pars, ell)*) -> (* dans ce cas comment sait_on entree ou sortie ???*)
				if !vDEBUG then Printf.printf "OLD PROTO non traitee actuellement";
				if ell then if !vDEBUG then Printf.printf "suite non traitee actuellement";
				()
		| _ -> ()
		
	let entrees = ref []
	let sorties = ref []

							
	let existeNomFonctionDansListe nom  =
	        (List.exists (fun (_,nomF,_) -> (nomF = nom) ) !listeDesNomsDeFonction    )
	
	(* la fonction est dans la liste par précondition *)
	let tupleNumNomFonctionDansListe nom  = List.find (fun (_,nomF,_) ->  (nomF = nom)  ) !listeDesNomsDeFonction  
	
	let ajouteNomDansListeNomFonction nom proto=
		if  (existeNomFonctionDansListe nom = false) then (* un nouveau nom de fonction *)
		begin				
			idFonction := !idFonction + 1;
			listeDesNomsDeFonction := (List.append !listeDesNomsDeFonction [(!idFonction, nom,proto)] )
		end
		
	(* si la fonction est déjà déclarée rien sinon ajouter la fonction a la liste ...*)
	(* pour savoir si la fonction est dans la liste il faut rechercher son nom...*)
	(* on suppose que le code est correct donc pas de multiple declarations *)
	(* on garde le dernier proto car la declaration definition contient forcement le nom des parametres pas la
	declaration simple *)
	(* donc liste associations nom fonction numero lorsqu'on rencontre une declaration simple et si definition
	alors creation de la declaration ce quin implique de modifier les structures*)
	
	(* une fonction a un nom, un nombre de degre d'imbrication	 
		a terme on pourrait imaginer : d'ajouter des infos sur les boucles, valeurs de retour (bornes min et max...)*)
	(* la fonction existe code correct ! elle pourrait être dans une bibliothèque donc appel sans def possible*) 
	
	let existeFonction nom  =
	        (List.exists (fun (_, f) -> (nom = f.nom) ) !doc.laListeDesFonctions  )
	let rechercheFonction nom = List.find (fun (_, f) -> (nom = f.nom) ) !doc.laListeDesFonctions   
		
	let 	rec majAuxFct listeTraitee  listeATraiter nom =
	if listeATraiter = []	then 	(listeTraitee)
	else		
		let couple = List.hd listeATraiter in
		let (num, func) = couple in
		if (nom = func.nom) then 
		begin 
			(List.append  
				(List.append 
					listeTraitee	
					[
						(	
							num, 
							(new_Infofonction  func.nom func.declaration 
								( new_CorpsFonction 		 func.corps.corpsS !listeBoucleOuAppelCourante) 
							!listeDesInstCourantes
							func.listeES
							)
						)
					])
				(List.tl listeATraiter) 
				)
			end
			else
				(majAuxFct 	(List.append listeTraitee [couple]) (List.tl listeATraiter) nom )

(* hypothèse seule variable de l'expression modifiée par la boucle est name *)
let printResPow v k a b =
Printf.printf "ispow : %s\n" v; 
print_expression k 0; new_line();
print_expression a 0;new_line();
print_expression b 0;new_line()


let rec isPowCte name expr = (* return isPow, contante pow, sign cte mul (CONSTANT (CONST_INT "1")) plus*)
	(*Printf.printf "appel de isPowCte %s\n" name ; print_expression expr 0;new_line();*)
	match expr with
		NOTHING -> (false, NOTHING, NOTHING, NOTHING)
		| UNARY (op, exp) ->
				let (rep, n,c,a) = isPowCte name exp in
				if rep = false  then (false, n, c, a)
				else
				begin
					match op with
					MINUS ->   	(true, n, BINARY (MUL, c, CONSTANT (CONST_INT "-1")) ,BINARY (MUL, a, CONSTANT (CONST_INT "-1")))
					| PLUS ->  	(true, n, c, a)
					| _ ->      (false, NOTHING, NOTHING, NOTHING)
				end
		| BINARY (op, exp1, exp2) ->
			
			let app2 = List.mem name  (listeDesVarsDeExpSeules exp2) in
			let app1 = List.mem name  (listeDesVarsDeExpSeules exp1) in

			let (rep1, n1, c1, a1) = if app1 then isPowCte name exp1 else   (false, NOTHING, NOTHING, NOTHING)  in
			let (rep2, n2, c2, a2) = if app2 then isPowCte name exp2 else  (false, NOTHING, NOTHING, NOTHING)  in
			(match op with
				ADD	 | SUB	->
					if app2 = false && app1 = false then (false,  CONSTANT (CONST_INT "0"),   CONSTANT (CONST_INT "0"), expr)
					else
					begin
						if app1 && app2 = false then (rep1, n1, c1, BINARY (op, a1, exp2)) 
						else  
						begin
							if app1 = false && app2 then (rep2, n2, c2, BINARY (op, exp1, a2)) 
							else
							begin
								if rep1 && rep2 then 
								begin
									let val1 = calculer (EXP n1) !infoaffichNull  []  1 in 
									let val2 = calculer (EXP n2) !infoaffichNull  []  1 in 
									if val1 = val2 then (true, n1, BINARY (op, c1, c2), BINARY (op, a1, a2)) else  (false, NOTHING, NOTHING, NOTHING)
								end 
								else     (false, NOTHING, NOTHING, NOTHING) 
							end
						end
					end
								
				| MUL	   	->  
					if app2 = false && app1 = false then (false,  CONSTANT (CONST_INT "0"),   CONSTANT (CONST_INT "0"), expr)
					else
					begin
						if app1 && app2 = false then (rep1, n1, BINARY (op, c1, exp2), BINARY (op, a1, exp2)) 
						else  
						begin
							if app1 = false && app2 then (rep2, n2, BINARY (op,  exp1, c2), BINARY (op, exp1, a2)) 
							else
							begin
								if rep1 && rep2 then 
								begin
									let val1 = estNul ( calculer (EXP a1) !infoaffichNull  [] 1) in 
									let val2 = estNul ( calculer (EXP a2) !infoaffichNull  [] 1) in 
									if val1 && val2  then (true, BINARY (ADD,n1,n2), BINARY (op, c1, c2), CONSTANT (CONST_INT "0")) 
									else  (false, NOTHING, NOTHING, NOTHING)
								end 
								else     (false, NOTHING, NOTHING, NOTHING) 
							end
						end
					end
		
				| DIV		->  
					if app2 = false && app1 = false then (false,  CONSTANT (CONST_INT "0"),   CONSTANT (CONST_INT "0"), expr)
					else
					begin
						if app1 && app2 = false then (rep1, n1, BINARY (op, c1, exp2), BINARY (op, a1, exp2)) 
						else  
						begin (*like A/apow(x,n,c,a) for the moment if a != 0 nocomp *)
							if app1 = false && app2 then 
							begin

								if estNul ( calculer (EXP a2) !infoaffichNull  [] 1) then
									(rep2, UNARY (MINUS, n2) , BINARY (op,  exp1, c2), CONSTANT (CONST_INT "0")) 
								else  (false, NOTHING, NOTHING, NOTHING) 
							end
							else
							begin
								if rep1 && rep2 then 
								begin
									let val1 = estNul ( calculer (EXP a1) !infoaffichNull  [] 1) in 
									let val2 = estNul ( calculer (EXP a2) !infoaffichNull  [] 1) in 
									if val1 && val2  then (true, BINARY (SUB,n1,n2), BINARY (op, c1, c2), CONSTANT (CONST_INT "0")) 
									else  (false, NOTHING, NOTHING, NOTHING)
								end 
								else     (false, NOTHING, NOTHING, NOTHING) 
							end
						end
					end
				| _	->    (false, NOTHING, NOTHING, NOTHING) )
			
			| QUESTION (_, _, _) ->	 (false, NOTHING, NOTHING, NOTHING) 
			| CAST (_, e) ->		isPowCte name e 
			| CALL (exp, args) ->	
				(match exp with
					 VARIABLE("pow10") -> 
						let val1 =  List.hd args in
						if  List.mem name  (listeDesVarsDeExpSeules val1) then
						begin
							let (rep1, n1, c1, a1) =   isPowCte name val1    in
							if estNul ( calculer (EXP a1) !infoaffichNull  [] 1) then 
								(rep1, BINARY (MUL, n1, CONSTANT (CONST_INT "10")),CALL (VARIABLE("pow10"),[c1]),  CONSTANT (CONST_INT "0")) 
							else   (false, NOTHING, NOTHING, NOTHING) 
						end
						else (false, NOTHING, NOTHING, CALL (VARIABLE("pow10"),[val1]))

				|VARIABLE("pow") ->
						let val1 =  List.hd args in
						let val2 =  List.hd (List.tl args) in
						let app2 = List.mem name  (listeDesVarsDeExpSeules val2) in
						if app2 then (false, NOTHING, NOTHING, NOTHING)
						else
						begin
							
							if  List.mem name  (listeDesVarsDeExpSeules val1) then
							begin
								let (rep1, n1, c1, a1) =   isPowCte name val1    in
								if estNul ( calculer (EXP a1) !infoaffichNull  [] 1) then 
									(rep1, BINARY (MUL, n1, val2),CALL (VARIABLE("pow"),List.append [c1] [val2]),  CONSTANT (CONST_INT "0")) 
								else   (false, NOTHING, NOTHING, NOTHING) 
							end
							else (false, NOTHING, NOTHING, CALL (VARIABLE("pow"),List.append [val1] [val2]))
						end 
				|_->(false, NOTHING, NOTHING, NOTHING) 		 
			)
			| COMMA _ 			->	 (false, NOTHING, NOTHING, NOTHING) 
			| CONSTANT cst -> 		(false, NOTHING, NOTHING, CONSTANT cst)											
			| VARIABLE (s) ->	 
					if name <> s then (false, NOTHING, NOTHING,  VARIABLE (s)) 
					else (true, CONSTANT (CONST_INT "1"), CONSTANT (CONST_INT "1"), CONSTANT (CONST_INT "0"))
			| _ ->(false, NOTHING, NOTHING, NOTHING) 



let 	calculForIndependant typeB borne init inc esttypeopPlus  afterindirect=
(*Printf.printf "calculForIndependant\n" ;*)
(*if afterindirect then Printf.printf "mettre a jour after indirect %s\n" typeB;*)
if borne = NOTHING then 
begin 
	(*Printf.printf "boucle borne non def\n";*)
	NOTHING
end
else
begin
	let 	expBorne =
	 	(if 	esttypeopPlus then
		 begin
			let exp2 =   (*CALL(VARIABLE("partieEntiereInf"),  [*)borne (*])*) in
			(*if typeB != "dowhile"   then*)
			BINARY (	DIV, (BINARY	(SUB,exp2, init)), inc)	
		 end
		 else
		 begin
			let expsup =   CALL(VARIABLE("log"),  [borne ]) in
			let expinf =   CALL(VARIABLE("log"),  [ CALL(VARIABLE("partieEntiereSup"),[init ] ) ]) in
			let expinc =   CALL(VARIABLE("log"),  [inc ]) in
			BINARY (	DIV, (BINARY (SUB,expsup,expinf)), expinc)	
			

		 end) in	
		let exp = (CALL	(VARIABLE("partieEntiereInf"), [(BINARY (ADD, expBorne, (CONSTANT (CONST_INT "1")))) ])) in
		if afterindirect then 	BINARY	(ADD, exp, (CONSTANT (CONST_INT "1")))	else exp	
end

let analyseInc infoVar appel typeopPlusouMUL contexte =

	let incrementEval =  (applyStoreVA(applyStoreVA   (EXP(infoVar.increment)) appel)contexte)  in
	let valinc = calculer incrementEval  !infoaffichNull  [](*appel*) (-1) in	

	let op = infoVar.operateur in 
	let sensinc = 
			if estNoComp valinc then NDEF 
			else 	if typeopPlusouMUL (*op +or -*) then 
						if estNul valinc then INCVIDE else if estStricPositif valinc then POS  else NEG
						else (*op *or /*)
						begin
							let varMoinsUn = (evalexpression (Diff( valinc,  ConstInt("1")))) in
							if estStricPositif valinc then
							begin
									if estNul varMoinsUn then	  INCVIDE else   if estStricPositif varMoinsUn then POS else  NEG
							end
							else NOVALID
						end
			in
(valinc, op, sensinc)

let expressionType exp =
	if estNoComp exp then INDEFINEDV 
	else if estNul exp then INTEGERV else if estInt exp then INTEGERV else if estFloat exp then FLOATV else INDEFINEDV 




let nombreIT id =
	if existeAssosBoucleBorne id then begin let bou = rechercheAssosBoucleBorne id in (bou.expressionBorne) end
	else (NOTHING)

	(* en fait on peut ne pas dépendre de la boucle englobante mais avoir la condition ou l'init fct d'une 
	var de la boucle englobante *)
	(* soi cette variable est MULTIPLE alors on prendra son max soit elle est single et on fait un sygma*)
	(* on ne peut donc pas le calculer ici*)
	
let getBorneBoucleFor s  borne init incr esttypeopPlus after= calculForIndependant s borne init incr esttypeopPlus after(*incInit*)
								
let rec afficherBoucleInfo b =
	new_line ();
	Printf.printf  "/*\t\tBoucle id %d\n" b.identifiant;
	if (aBoucleEnglobante b) then
	begin
		if (existeBoucle b.nomEnglobante) then
		begin
			Printf.printf "\n\n/*  INFO BOUCLE ENGLOBANTE : */\n";
			let boucleEnglobante = rechercheBoucle  b.nomEnglobante in	
			let infoBoucleEng = getBoucleInfoB boucleEnglobante in	
			afficherBoucleInfo infoBoucleEng;
			Printf.printf "\n\n/* FIN INFO BOUCLE ENGLOBANTE */\n/*"
		end
	end
	else Printf.printf  "\t\tpas de boucle englobante\n";
	Printf.printf  "\t\ttype : %s\n" b.typeBoucle;
	Printf.printf  "\t\tnb degre imbrication : %d\n" b.degreb;
	Printf.printf "\t\tliste des variables de la condition : "  ;
	afficherListeVarExp  b.lesVariablesNbIt ;
	Printf.printf "\n*/" 		

let afficherAssosBoucleBorne b =
	Printf.printf "\n\t\tnombre d it boucle %d =  " (getBoucleIdB b.laBoucle) ;
	print_expression b.expressionBorne 0 ;new_line ()

let afficherBorne id =
	if existeAssosBoucleBorne id then afficherAssosBoucleBorne (rechercheAssosBoucleBorne id)
	else ()

let  afficherBoucleFor boucleFor =
	afficherBoucleInfo boucleFor.boucleInitiale;				
	new_line ();
	Printf.printf  "\n/*\t\tDans boucle nom variable de boucle %s\n"  boucleFor.valInit.variable;
	Printf.printf "\t\tliste des variables de l'init : "  ;
	afficherListeVarExp  boucleFor.lesVariablesInit ;
	Printf.printf "\n\t\tvaleur de %s a l'init : "  boucleFor.valInit.variable  ;
	print_expression boucleFor.valInit.valeur 0;new_line ();
	Printf.printf "\t\tvaleur de la borne : "  ;
	print_expression boucleFor.n 0;new_line ();
	Printf.printf "\t\tvaleur de increment : \n" ;  
  	print_expression boucleFor.c 0 ;new_line ();						
	afficherBorne boucleFor.boucleInitiale.identifiant		
	
let  afficherBoucle b =	
	match b with 
		BOUCLEFOR bf -> 	Printf.printf "\n/* BOUCLE FOR : */\n"; afficherBoucleFor bf ; Printf.printf "\n/* FIN BOUCLE FOR : */\n"
		| AUTRE    bi->		Printf.printf "\n/* BOUCLE AUTRE : */\n"; afficherBoucleInfo bi.boucleI ; Printf.printf "\n/* FIN BOUCLE AUTRE : */\n"
				

let afficherListeBoucleSousNid l =
	if l = [] then Printf.printf "\n"
	else
		begin	
			if l <> [] then
			begin
				Printf.printf "\nLISTE DES BOUCLES DU SOUS NID : \n";
				List.iter (fun e -> Printf.printf "\t %d" e) l;
				Printf.printf "\nFIN LISTE DES BOUCLES DU SOUS NID : \n"
			end
			else Printf.printf "\nAUCUNE BOUCLE DU SOUS NID : \n"
		end
		
let afficherInfoBorneDeBoucle i =
	afficherBoucle	i.laBoucle ;
	Printf.printf "\n/* \t BORNE   */\n";
	print_expression i.expressionBorne 0 ;new_line ();	
	if i.lesAffectationsB = [] then Printf.printf "\n"
	else
		begin		
			Printf.printf "\n \t\t\t AFFECTATIONS   \n";	
			afficherLesAffectations	i.lesAffectationsB ; new_line ();
			Printf.printf "\n \t\t\t FIN AFFECTATIONS   \n";new_line ()
		end
		
let rec afficherNid n =
	Printf.printf "\n \t\tINFO BORNE NOEUD COURANT :  \n";
	afficherInfoBorneDeBoucle n.infoNid;
	Printf.printf "\n \t\tFIN INFO BORNE NOEUD COURANT :  \n";
	Printf.printf "\n \t\tVARIABLE NOEUD COURANT :  %s \n"		n.varDeBoucleNid ;
	Printf.printf  "\n\t\tLISTE DES AFFECTATIONS DE LA BOUCLE\n";
	afficherLesAffectations n.lesAffectationsBNid ;	
	if n.listeTripletNid = [] then Printf.printf "\n"
	else
		begin
			Printf.printf "\n\t\t\t SOUS NID : \n";
			afficherSousNid	n.listeTripletNid;
			Printf.printf "\n\t\t\t FIN SOUS NID : \n"
		end

		
and afficherSousNid sn =
if (sn = [] )	then Printf.printf "\n"
else
	List.iter (fun (l,aS,n) ->
			Printf.printf "\t\t\t\t"; afficherListeBoucleSousNid l; 
			Printf.printf "\n\t\t\t\t";afficherListeAS aS; 
			afficherNid n) sn

let rec afficherNidRes n =
	Printf.printf "\n \t\tINFO BORNE NOEUD COURANT :  \n";
	afficherInfoBorneDeBoucle n.infoNid;
	Printf.printf "\n \t\tFIN INFO BORNE NOEUD COURANT :  \n";
	Printf.printf "\n \t\tVARIABLE NOEUD COURANT :  %s \n"		n.varDeBoucleNid ;
	Printf.printf  "\n\t\tLISTE DES AFFECTATIONS DE LA BOUCLE\n";
	(*afficherLesAffectations n.lesAffectationsBNid ;*)	
	if n.listeTripletNid = [] then Printf.printf "\n"
	else
		begin
			Printf.printf "\n\t\t\t SOUS NID : \n";
			afficherSousNid	n.listeTripletNid;
			Printf.printf "\n\t\t\t FIN SOUS NID : \n"
		end
		
and afficherSousNidRes sn =
if (sn = [] )	then Printf.printf "\n"
else
	List.iter (fun (l,aS,n) ->
			Printf.printf "\t\t\t\t"; afficherListeBoucleSousNid l; 
			(*Printf.printf "\n\t\t\t\t";afficherListeAS aS; *)
			afficherNid n) sn


let afficherNidDeBoucle doc	=
if !doc.laListeDesNids <> [] then
begin
	Printf.printf "\n/*\t LISTE DES NID DE BOUCLE DU DOCUMENT :*/\n";
	List.iter (fun n ->  Printf.printf "\n/*\t NID :*/\n" ; afficherNid n) !doc.laListeDesNids;
	Printf.printf "\n/* \t FIN LISTE DES NIDS DE BOUCLES DU DOCUMENT  */\n"
end
let afficherNidDeBoucleRes doc	=
if !doc.laListeDesNids <> [] then
begin
	Printf.printf "\n/*\t LISTE DES NID DE BOUCLE DU DOCUMENT :*/\n";
	List.iter (fun n ->  Printf.printf "\n/*\t NID :*/\n" ; afficherNidRes n) !doc.laListeDesNids;
	Printf.printf "\n/* \t FIN LISTE DES NIDS DE BOUCLES DU DOCUMENT  */\n"
end
		
let getNomBoucleMereDuNid n = (getBoucleInfoB (n.infoNid.laBoucle)).identifiant

let existeNid  id  =
List.exists	 (fun n -> ((getBoucleInfoB (n.infoNid.laBoucle)).identifiant = id) ) !doc.laListeDesNids

let rechercheNid id  =
List.find (fun n -> ((getBoucleInfoB (n.infoNid.laBoucle)).identifiant = id)  ) !doc.laListeDesNids
								
					
(*evaluation des bornes*)
let afficherLesBornesDeBoucle doc = List.iter	(fun b ->  afficherAssosBoucleBorne b  )	!doc.laListeDesAssosBoucleBorne
			
(* fin des affichages *)		 
let listeDesRes = ref []

let creerListeDesAffectNbItBoucleFct listeDesIdBoucleDsFct = 
List.iter(fun numB -> listeDesRes := List.append !listeDesRes [new_instVar 	("__NBITBFOR__"^(string_of_int (numB))) (EXP(nombreIT numB)) ]
		)		listeDesIdBoucleDsFct	

let aBEnglobanteBoucle b =
	match b with 
		BOUCLEFOR  bf ->  (aBoucleEnglobante bf.boucleInitiale)
		| AUTRE    bi->	(aBoucleEnglobante bi.boucleI)			

(*let getBoucleInfoEnglobantBI bI = (getBoucleInfoB (rechercheBoucle bI.nomEnglobante))*)
				
let rec estUnitaireExpression expre =
		 match expre with
			NOTHING -> true
			| UNARY (_, _)| BINARY (_, _, _) | QUESTION (_, _, _) ->false
			| CAST (_, exp) ->				estUnitaireExpression  exp
			| CALL (_, _) | COMMA _ ->					false
			| CONSTANT cst -> (	match cst with
									CONST_INT i ->		if i = "1" || i ="-1" then true else false
									| CONST_FLOAT r ->	if r = "1" || r ="-1" then true else false
									| RCONST_INT i ->		if i = 1 || i = -1 then true else false
									| RCONST_FLOAT r ->	if r = 1.0 || r = -1.0 then true else false
									| CONST_CHAR _ | CONST_STRING _| CONST_COMPOUND _->false)
			| VARIABLE _ ->		false
			| _ -> false

(*listeDesVarDeExp exp*)
let lesVarBoucle num =( listeDesVarsDeExpSeules (nombreIT num))

(* une seule affectation dans une expression*)
let rec rechercheVarBoucleFor var init  =
(*	Printf.printf  "\n analyseInitFor \n"; print_expression init 1 ;new_line ();*)
match init	with
NOTHING ->   ()
| UNARY (op, n) ->
	if get_estAffect init then 
	( match n with
		VARIABLE (v) -> 
			if var <> v then listeAffectInit := List.append !listeAffectInit  [(v,expressionDinitFor)]
			else
			begin
				(match op with
				PREINCR| 	POSINCR ->expressionDinitFor :=BINARY(ADD,n,CONSTANT(CONST_INT("1")))
				|PREDECR |POSDECR->	expressionDinitFor :=BINARY(SUB,n,CONSTANT(CONST_INT("1")))
				| _ ->()
				)
			end
		|_->()
	)
	else ()
| BINARY (op, exp1, exp2) ->
	if get_estAffect init then 
		(match exp1 with
		VARIABLE v ->  
			if var<> v then 
				listeAffectInit := List.append !listeAffectInit [(v,expressionDinitFor)]
			else
				(match op with
				  ASSIGN ->    		expressionDinitFor :=exp2
				| ADD_ASSIGN -> 	expressionDinitFor :=BINARY(ADD,exp2,exp1)
				| SUB_ASSIGN ->  	expressionDinitFor :=BINARY(SUB,exp1,exp2)
				| MUL_ASSIGN -> 	expressionDinitFor :=BINARY(MUL,exp1,exp2)
				| DIV_ASSIGN -> 	expressionDinitFor :=BINARY(DIV,exp1,exp2)
				| MOD_ASSIGN ->  	expressionDinitFor :=BINARY(MOD,exp1,exp2)
				| BAND_ASSIGN -> 	expressionDinitFor :=BINARY(AND,exp1,exp2)
				| BOR_ASSIGN -> 	expressionDinitFor :=BINARY(OR,exp1,exp2)
				| XOR_ASSIGN ->  	expressionDinitFor :=BINARY(XOR,exp1,exp2)
				| SHL_ASSIGN ->  	expressionDinitFor :=BINARY(SHL,exp1,exp2)
				| SHR_ASSIGN -> 	expressionDinitFor :=BINARY(SHR,exp1,exp2)
				|_ -> expressionDinitFor := VARIABLE(var);  ()	)
				|_->expressionDinitFor := VARIABLE(var);())
	else ()
| COMMA exps ->	List.iter(fun ex-> rechercheVarBoucleFor var ex)exps							
|_ -> () (*initialisation :="";*)


let traiterEQ init borne var c =
	(*if !opEstPlus then (*incrément type +/-constant*)
	begin
		match !estPosInc with 
			INCVIDE -> (CONSTANTE , NOTHING, NOTHING, EQ, false, var, c)(* si init = borne toujours sinon 0*)	
			|POS|NEG-> (CONSTANTE , NOTHING, (CONSTANT (CONST_INT "1")), EQ, false, var, c)(* si init = borne 1 sinon 0*)
			|_ ->  (CROISSANT , (CONSTANT (CONST_INT "1")), NOTHING, EQ, true, var, c)
		end (*incrément type *// constant*)
	else
	begin*)
		match !estPosInc with
			INCVIDE -> (CONSTANTE , NOTHING, NOTHING, EQ, false, var, c)(* sic=1 alors init = borne toujours sinon 0*)	
			|POS|NEG-> (CONSTANTE , NOTHING, (CONSTANT (CONST_INT "1")), EQ, false, var, c)(* si init = borne 1 sinon 0*)
			|_ ->  (CROISSANT , (CONSTANT (CONST_INT "1")), NOTHING, EQ, true, var, c)
		(*end*)

let traiterNEQ init borne var c =

		match !estPosInc with
			INCVIDE  -> (CONSTANTE , NOTHING, NOTHING, NE, false, var, c)(* case constant = 1 then si init = borne 1 sinon 0*)
			|POS -> (CROISSANT , init,   BINARY (SUB, borne, !vEPSILON) , LT, false, var, BINARY(LT, VARIABLE(var), borne))
			(* case constant > 1  si init = borne toujours sinon 0*)
			|NEG ->  (*isExactForm := false;(NONMONOTONE , NOTHING, NOTHING, NE, true, var, c)*) (DECROISSANT , BINARY (ADD, borne, !vEPSILON) ,   init , GT, false, var, BINARY(GT, VARIABLE(var), borne))
			|_ ->   (CROISSANT , init, borne, NE, true, var, c)
		(*end*)
	
let changeCompOp op =
		match op with
			LT ->  GE (* from < to >= *)
			| LE ->  GT (*from <= to > *)
			| GT ->  LE(*  from >to <=*)
			| GE -> LT
			(*| EQ -> NE
			| NE -> EQ*)
			| _->  op

let arrayShown = ref true

let isDivInc exp =
	let val1 = calculer (EXP exp) !infoaffichNull [] 1 in 
	if val1 = NOCOMP  then false
	else
	begin
		let varMoinsUn = calculer (EXP (BINARY(SUB,exp, CONSTANT  (CONST_INT "1")))) !infoaffichNull [] 1 in 
		 
		if estStricPositif varMoinsUn then false
		else true
	end

let listADD = ref []
let listADDInc = ref []
let rec rechercheListeDesVarDeBoucle listeVCond aS =
if listeVCond = [] then begin (*Printf.printf "fin liste variable \n"	;*) [] end
else
begin
(*Printf.printf "variable courante :%s\n"	(List.hd listeVCond);*)
	if (estDef (List.hd listeVCond)  aS)	then  List.append [List.hd listeVCond]  (rechercheListeDesVarDeBoucle (List.tl listeVCond) aS)
	else rechercheListeDesVarDeBoucle (List.tl listeVCond) aS
end		


let rec  rechercheConditionBinary init varinit op exp1 exp2 listeinit avant dans cte t c lv l inst=
(*	Printf.printf "rechercheConditionBinary\n";	 print_expression (BINARY (op, exp1, exp2)) 0; new_line();*)
	let l2 =  (listeDesVarsDeExpSeules exp2) in
	let inter2 =  intersection l2  l  in

(*List.iter(fun x-> Printf.printf"%s\n" x)l2;*)
	let l1 =  (listeDesVarsDeExpSeules exp1) in
	let inter1 =  intersection l1 l  in		
	let (var, liste) = 
		if List.mem varinit l1 || List.mem varinit l2 then 
				(varinit,listeinit) 
		else 	if  listeinit = [] then  (varinit,listeinit) 
				else ((List.hd listeinit), (List.tl listeinit)) in
		
(*List.iter(fun x-> Printf.printf"%s\n" x)l1;			*)									
	let (isLoopCtee2, isOnlyVare2) =  if inter2 = [] then (true, false) else if  List.tl inter2 = [] then (false, true) else (false, false) in
	let (isLoopCtee1, isOnlyVare1) =  if inter1 = [] then (true, false) else if  List.tl inter1 = [] then (false, true) else (false, false) in
(*Printf.printf "rechercheConditionBinary\n";	 print_expression (BINARY (op, exp1, exp2)) 0; new_line();*)
	let (sens1, a1,b1, unitairea1, b1nul) = traiterAffineForm  exp1 var l in
	(*print_affine sens1 a1 b1 var;*)
	let (sens2, a2,b2,unitairea2, b2nul) = traiterAffineForm  exp2 var l in
	(*print_affine sens2 a2 b2 var;*)
(*Printf.printf "rechercheConditionBinary\n";	 print_expression (BINARY (op, exp1, exp2)) 0; new_line();*)
	if isLoopCtee2 && isLoopCtee1 || sens1 =  NONMONOTONE || sens2 = NONMONOTONE || (isLoopCtee2 = false && isLoopCtee1 =false)  then
	begin
(*Printf.printf "rechercheConditionBinary cas 1\n";	 *)
		if op = AND then traiterANDCOND init var exp1 exp2  liste avant dans cte t (BINARY(op,exp1, exp2)) lv l inst
		else 
		begin

			let testA = if !arrayShown = false then 
						begin arrayShown := true ; (*Printf.printf "traiterTab\n"; *)traiterArray  exp1 exp2 liste avant dans cte t c lv l inst end 
						else NOTHING in
			if testA = NOTHING then	
			begin
				(*Printf.printf"recPow %s\n" var;*)
				recherchePow init var op exp1 exp2 liste avant dans cte t c lv l isLoopCtee1 isLoopCtee2 inst
			end
			else 
			begin
			(*Printf.printf"pas recPow\n";*)
				isExactForm := false;
				traiterARRAYANDCOND init var testA op exp1 exp2  liste avant dans cte t c lv l isLoopCtee1 isLoopCtee2 inst
			end
		end			
	end
	else
	begin
		if isLoopCtee2 then
		begin
(*Printf.printf "rechercheConditionBinary cas 2\n";	*)
			let nop = if sens1 = CROISSANT then op else changeCompOp op in
			let ne2 = 
				if  b1nul then
					if (unitairea1 && sens1 = CROISSANT)   then exp2
					else BINARY(DIV, exp2,a1)  
				else if unitairea1 && sens1 = CROISSANT then BINARY(SUB, exp2,b1)
					 else BINARY(DIV,BINARY(SUB, exp2,b1),a1) in
			let ne = BINARY(nop,exp1, ne2) in
			match nop with
			(* si exp2 est cte OK sinon il faut verifier qu'elle n'est pas modifiee par la boucle et rechercher sa valeur idem ds  pour exp1*)
			LT ->  (CROISSANT,init,BINARY(SUB, ne2,!vEPSILON), LT, false, var,ne) (*i<exp2, i in [init, exp2-1] *)	 
			| LE -> (CROISSANT,  init ,  ne2 ,  LE, false, var,ne) (*i <= exp2 i in [init, exp2 ]  *)
			| GT -> (DECROISSANT, BINARY (ADD, ne2, !vEPSILON), init , GT,false , var, ne) (* i>exp2, i in [exp2+1, init ]*)
			| GE -> (DECROISSANT,  ne2  ,  init , GE,false, var, ne) (*>= i =inf, i in [exp2, init ]  *)
			| AND -> traiterANDCOND init var exp1 exp2 liste avant dans cte t  (BINARY(op,exp1, exp2)) lv l inst
			| OR -> (NONMONOTONE , NOTHING, NOTHING, XOR, true, var ,BINARY(op,exp1, exp2))
			| EQ ->  
					let ((*isindirect,inc,var, before*)isindirect,inc,_,_,isMultiInc) =  getLoopVarInc var inst in		
					if isMultiInc then isExactForm := false;
					if isindirect then Printf.printf "EQ cas 2 indirect change\n";
							(match  inc  with 
							NODEFINC -> 
								 
								let (isAssignedOK, assign, isConditionnal, ltrue, lfalse, ifvar) = containBoolxAssignementBody var  inst inst in
								if isAssignedOK then 
									(*let (_,_,_,_,_,_,_, _,_) =getBooleanAssignementInc  assign isConditionnal ltrue lfalse  init var op exp1 exp2 liste avant dans cte t c lv l inst ifvar in ()*)
								(CROISSANT , NOTHING, NOTHING, EQ, true, var, ne) else traiterEQ init ne2  var ne

							|_->traiterEQ init ne2  var ne)
			
			| NE -> let ((*isindirect,inc,var, before*)isindirect,inc,_,_,isMultiInc) =  getLoopVarInc var inst in
					if isMultiInc then isExactForm := false;
					if isindirect then Printf.printf "NE cas 2 indirect change\n";

					(match  inc  with 
							NODEFINC -> (* pas trouvé d'increment peut être condition = var booleenne *)
								
								let (isAssignedOK, assign, isConditionnal, ltrue, lfalse , ifvar) = containBoolxAssignementBody var  inst inst in
								if isAssignedOK then 
									(*let (_,_,_,_,_,_,_, _,_) =getBooleanAssignementInc  assign isConditionnal ltrue lfalse  init var op exp1 exp2 liste avant dans cte t c lv l inst ifvar in ()*)(CROISSANT , NOTHING, NOTHING, NE, true, var, ne) else traiterNEQ init ne2  var ne

							|_->traiterNEQ init ne2  var ne)
					
			| _-> isExactForm := false;(*| BAND -> | XOR ->| BOR ->*) if !vDEBUG then Printf.printf   "\terreur test for non traite\n";
					(NONMONOTONE , NOTHING, NOTHING, XOR,true, var, BINARY(op,exp1, exp2))
		end
		else
		begin
			if isLoopCtee1 then
			begin
			(*	Printf.printf "rechercheConditionBinary cas 3\n";	*)
				let nop = if sens2 = CROISSANT then op else changeCompOp op in
				let ne1 = 
					if  b2nul then
						if unitairea2 && sens2 = CROISSANT then exp1
						else BINARY(DIV, exp1,a2)  
					else if unitairea2 && sens2 = CROISSANT then BINARY(SUB, exp1,b2)
						else  BINARY(DIV,BINARY(SUB, exp1,b2),a2) 
				in
				let ne = BINARY(nop,ne1, exp2) in

				match op with
					LT 	-> 	(DECROISSANT ,BINARY (ADD, ne1, !vEPSILON), init , LT,false, var, ne) (*exp1 < i i in [exp1+1,init]*)
					| LE ->	(DECROISSANT, ne1 , init , LE,false, var, ne) (*exp1<=i, i in [exp1, init ]*)
					| GT -> (CROISSANT, init , BINARY (SUB, ne1, !vEPSILON),GT,false, var, BINARY(op,exp1, exp2))(*exp1 > i, i in [init ,exp1-1 ] *)
					| GE -> (CROISSANT, init ,ne1  , GE,false, var, ne) (*exp1 >= i, i in [ init , exp1 ] *)
					| AND -> traiterANDCOND init var exp1 exp2 liste avant dans cte t (BINARY(op,exp1, exp2)) lv l inst
					| OR -> (NONMONOTONE , NOTHING, NOTHING, XOR, true, var, BINARY(op,exp1, exp2))
					| EQ -> let ((*isindirect,inc,var, before*)isindirect,inc,_,_,isMultiInc) =  getLoopVarInc var inst in
							if isMultiInc then isExactForm := false;
				
							(*if isindirect then Printf.printf "EQ cas 2 indirect change\n";*)
							(match  inc  with 
							NODEFINC -> (* pas trouvé d'increment peut être condition = var booleenne *)
								(*Printf.printf "cas 3 EQ peut être booleen\n";*)
								let (isAssignedOK, assign, isConditionnal, ltrue, lfalse, ifvar) = containBoolxAssignementBody var  inst inst in
								if isAssignedOK then 
									(*let (_,_,_,_,_,_,_, _,_) =getBooleanAssignementInc  assign isConditionnal ltrue lfalse  init var op exp1 exp2 liste avant dans cte t c lv l inst ifvar in ()*)
								(CROISSANT , NOTHING, NOTHING, EQ, true, var, ne) else traiterEQ init ne1 var ne

							|_->traiterEQ init ne1 var ne)
							
							 
					| NE ->  let ((*isindirect,inc,var, before*)isindirect,inc,_,_,isMultiInc) =  getLoopVarInc var inst in
							 if isMultiInc then isExactForm := false;
					
						   (* if isindirect then Printf.printf "NE cas 3 indirect change\n";*)
							(match  inc  with 
							NODEFINC -> (* pas trouvé d'increment peut être condition = var booleenne *)
								(*Printf.printf "cas 3 NE peut être booleen\n";*)
								let (isAssignedOK, assign, isConditionnal, ltrue, lfalse , ifvar) = containBoolxAssignementBody var  inst inst in
								if isAssignedOK then 
									(*let (_,_,_,_,_,_,_, _,_) =getBooleanAssignementInc  assign isConditionnal ltrue lfalse  init var op exp1 exp2 liste avant dans cte t c lv l inst ifvar in ()*)
										(CROISSANT , NOTHING, NOTHING, NE, true, var, ne) else traiterNEQ init ne1 var ne

							|_->traiterNEQ init ne1 var ne)
					
						   
					| _-> isExactForm := false;(* | BAND -> | XOR ->| BOR ->*) if !vDEBUG then Printf.printf   "\terreur test for non traite\n";
								(NONMONOTONE , NOTHING, NOTHING, XOR,true, var, BINARY(op,exp1, exp2))
			end
			else begin 
						isExactForm := false;(*if !vDEBUG then Printf.printf   "\terreur test for non traite\n"; *)
						(NONMONOTONE , NOTHING, NOTHING, XOR, true, var,BINARY (op,exp1, exp2))
				end
		end
end


and containBoolxAssignementBody x  body completList =
(* x isAssignedOk ? assignement, isConditionnalAssignment, conditionTrueList, conditionFalseList, ifVar *)
				(*getOnlyBoolAssignment := true;*)
				let las = evalStore (new_instBEGIN(body)) [] [] in
				(*getOnlyBoolAssignment := false;*)
				if existAffectVDsListeAS x las then
				begin
					let extinc =  rechercheAffectVDsListeAS x las  in
					(match extinc with 
						MULTIPLE -> 
							let (isAssigned, onlyIntoIf, exp, listTrue, listFalse, ifVar) = 
											containBoolxAssignementIntoConditionnal x  body completList		in
							
							if isAssigned 
								&&  onlyIntoIf 
								&& ( exp <> NOTHING) then 	(true, exp, true, listTrue, listFalse, ifVar) 
							else 	(false, NOTHING, true, [],[],"")
						 | EXP (e) -> 
							if e = NOTHING then  
								(false, NOTHING,false, [],[],"")  
							else ((*Printf.printf "%s isassigned into as  \n" x;*) (true, e ,false, [],[],"")) 
					)
 				end
				else (false,NOTHING ,false, [],[],"") 

and getBooleanAssignementInc  assign isConditionnal ltrue lfalse  init var o e1 e2 liste avant dans cte t c lv l inst ifvar=(* voir indirect*)
let isBoolEq = (match o with EQ-> false |_-> true) in
(*getOnlyBoolAssignment := true;*)
(*Printf.printf "getBooleanAssignementInc  \n"; *)
(* ici il faudra tester si l'operateur est EQ ou NE*)
let cas =evalStore (new_instBEGIN(inst)) [] [] in
(*getOnlyBoolAssignment := false;*)
(*afficherListeAS cas;*)
opEstPlus:= true;  

if isConditionnal = false then
	match assign with
	BINARY(op, exp1, exp2)-> (*Printf.printf "getBooleanAssignementInc : binary a etudier\n";*) (* forme x= i>10*)

(*print_expression assign 0;flush(); new_line();space(); new_line();*)
		let listeVCond =  listeDesVarsDeExpSeules  assign in  
		let listeVDeBoucle =  	rechercheListeDesVarDeBoucle  listeVCond 	dans in
		
		let nop = if isBoolEq then changeCompOp op else op in
		let comp = BINARY (AND, BINARY ( o, e1, e2) ,BINARY (nop, exp1, exp2))  in

		let varCond1 = if listeVDeBoucle = [] then var else List.hd listeVDeBoucle in
		let (assign,after)= rechercheAffectVDsListeASAndWhere varCond1 var cas false in
(*print_expression (BINARY(nop, exp1, exp2)) 0;flush(); new_line();space(); new_line();*)




		let (croissant,borneInf,borneSup,operateur,multiple,nnvar,nexp)= 
			rechercheConditionBinary (VARIABLE(varCond1)) varCond1 nop exp1 exp2 (union l listeVDeBoucle) avant dans cte t comp lv (union l listeVDeBoucle) inst in
		(*Printf.printf " getBooleanAssignementInc apres rechercheConditionBinary nouvelle variable %s + indirect %s\n" nnvar var;*)

		
		let (inc, before, isplus,iscomp,varDep)=
				analyseIncFor varCond1 (BINARY(ASSIGN,VARIABLE(varCond1),assign)) inst cas true inst [] in	
		
		

(*Printf.printf " getBooleanAssignementInc apres rechercheConditionBinary nouvelle variable %s if false + indirect %s if varDep %s \n" nnvar ifvar varDep;*)
		let (inc, before) =
		if varDep = varCond1 then 
			if inc = NOTHING then (NOTHING, after=false) else ( inc,after=false )  
		else (NOTHING, true) in

		expressionDinitFor := assign;
		if croissant = CROISSANT then
				begin
					borne:=borneSup; initialisation:=borneInf; 
				end
				else begin  borne:=borneInf; initialisation:=borneSup; end;

		(*if (croissant = NONMONOTONE) then Printf.printf "condition depend de deux variables ??? \n" 
		else
		begin
			print_expression borneInf 0;flush(); new_line();space(); new_line();
			print_expression borneSup 0;flush(); new_line();space(); new_line();
			print_expression inc 0;flush(); new_line();space(); new_line();
			if before then Printf.printf "before\n" else Printf.printf "after\n";
			print_expression assign 0;flush(); new_line();space(); new_line();
		end; *)(croissant,borneInf,borneSup,op,multiple,varDep,nexp, inc,before)
	|_-> (*Printf.printf "NO LOOP BOUND EXPRESSION sans if\n"; *)(NONMONOTONE , NOTHING, NOTHING, o, true, var, BINARY ( o, e1, e2), NOTHING, true)
else
begin

	if ltrue = [] then 
	begin
		let ass = rechercheAffectVDsListeAS ifvar cas in
		match (*List.hd lfalse*)ass with
		EXP(BINARY(op, exp1, exp2))-> (*Printf.printf "getBooleanAssignementInc : binary a etudier\n";*) (* forme x= i>10*)

		(*print_expression (BINARY(op, exp1, exp2)) 0;flush(); new_line();space(); new_line();*)



		let listeVCond =  listeDesVarsDeExpSeules  (List.hd lfalse) in  
		let listeVDeBoucle =  	rechercheListeDesVarDeBoucle  listeVCond 	dans in
		let nop = if isBoolEq then changeCompOp op else op in
		let comp = BINARY (AND, BINARY ( o, e1, e2) ,BINARY (nop, exp1, exp2))  in

		let varCond1 = if listeVDeBoucle = [] then var else List.hd listeVDeBoucle in
		(*print_expression (BINARY(nop, exp1, exp2)) 0;flush(); new_line();space(); new_line();*)

		let (assign,after)= rechercheAffectVDsListeASAndWhere varCond1 ifvar cas false in

		let (croissant,borneInf,borneSup,operateur,multiple,nnvar,nexp)= rechercheConditionBinary (VARIABLE(varCond1)) varCond1 nop exp1 exp2 (union l listeVDeBoucle) avant dans cte t comp lv (union l listeVDeBoucle)  inst in
		(*Printf.printf " getBooleanAssignementInc apres rechercheConditionBinary nouvelle variable %s if false + indirect %s if\n" nnvar ifvar;*)

		
 
		let  (inc, before, isplus,iscomp,varDep)=
			analyseIncFor varCond1 (BINARY(ASSIGN,VARIABLE(varCond1),assign)) inst cas true inst [] in	

(*Printf.printf " getBooleanAssignementInc apres rechercheConditionBinary nouvelle variable %s if false + indirect %s if varDep %s \n" nnvar ifvar varDep;*)
		let (inc, before) =
		if varDep = varCond1 then 
			if inc = NOTHING then (NOTHING, after=false) else ( inc,after=false ) 
		else (NOTHING, true) in
		expressionDinitFor := assign;
		if croissant = CROISSANT then
				begin
					borne:=borneSup; initialisation:=borneInf; 
				end
				else begin  borne:=borneInf; initialisation:=borneSup; end;

		(*if (croissant = NONMONOTONE) then Printf.printf "condition depend de deux variables ??? \n" 
		else
		begin
			print_expression borneInf 0;flush(); new_line();space(); new_line();
			print_expression borneSup 0;flush(); new_line();space(); new_line();
			print_expression inc 0;flush(); new_line();space(); new_line();
			if before then Printf.printf "before\n" else Printf.printf "after\n";
				print_expression assign 0;flush(); new_line();space(); new_line();
		end;*)
		 (croissant,borneInf,borneSup,op,multiple,varDep,nexp, inc,before)
	|_->  (*Printf.printf "NO LOOP BOUND EXPRESSION avec if false\n"; *)(NONMONOTONE , NOTHING, NOTHING, o, true, var, BINARY ( o, e1, e2), NOTHING, true)
	
	end
	else
	begin
		let ass = rechercheAffectVDsListeAS ifvar cas in
		 
		(match (*List.hd ltrue*)ass with
			EXP(BINARY(op, exp1, exp2))-> (*Printf.printf "getBooleanAssignementInc : binary a etudier\n"; *)(* forme x= i>10*)
(*print_expression (BINARY(op, exp1, exp2)) 0;flush(); new_line();space(); new_line();*)
			let listeVCond =  listeDesVarsDeExpSeules  (List.hd ltrue) in  
			let listeVDeBoucle =  	rechercheListeDesVarDeBoucle  listeVCond 	dans in
			let varCond1 = if listeVDeBoucle = [] then var else List.hd listeVDeBoucle in
			let nop = if isBoolEq then changeCompOp op else op in
			let comp = BINARY (AND, BINARY ( o, e1, e2) ,BINARY (nop, exp1, exp2))  in
			let (assign,after)= rechercheAffectVDsListeASAndWhere varCond1 ifvar cas false in
			let (croissant,borneInf,borneSup,operateur,multiple,nnvar,nexp)= 
				rechercheConditionBinary (VARIABLE(varCond1)) varCond1 nop exp1 exp2 (union l listeVDeBoucle) avant dans cte t comp lv (union l listeVDeBoucle)  inst in
			(*Printf.printf " getBooleanAssignementInc apres rechercheConditionBinary nouvelle variable %s if true + indirect%sif\n" nnvar ifvar;*)


			 

			let (inc, before, isplus,iscomp,varDep)=
				analyseIncFor varCond1 (BINARY(ASSIGN,VARIABLE(varCond1),assign)) inst cas true inst [] in	
			(*Printf.printf " getBooleanAssignementInc apres rechercheConditionBinary nouvelle variable %s if false + indirect %s if varCond1 %s \n" nnvar ifvar varCond1;*)
			let (inc, before) =
			if varDep = varCond1 then 
				if inc = NOTHING then (NOTHING, after=false) else ( inc,after=false ) 
			else (NOTHING, true) in
			expressionDinitFor := assign;
			if croissant = CROISSANT then
				begin
					borne:=borneSup; initialisation:=borneInf; 
				end
				else begin  borne:=borneInf; initialisation:=borneSup; end;

			(*if (croissant = NONMONOTONE) then Printf.printf "condition depend de deux variables ??? \n" 
			else
			begin
				Printf.printf "borneinf\n" ;print_expression borneInf 0;flush(); new_line();space(); new_line();
				Printf.printf "bornesup\n"  ;print_expression borneSup 0;flush(); new_line();space(); new_line();
				Printf.printf "increment\n" ;print_expression inc 0;flush(); new_line();space(); new_line();
				if before then Printf.printf "before\n" else Printf.printf "after\n";
	print_expression assign 0;flush(); new_line();space(); new_line();
			end;*)
			(croissant,borneInf,borneSup,op,multiple,varDep,nexp, inc,before)
		|_->  
			 (*Printf.printf "NO LOOP BOUND EXPRESSION avec if true\n"; *)
			(NONMONOTONE , NOTHING, NOTHING, o, true, var, BINARY ( o, e1, e2), NOTHING, true)
		)
	end

(* on a if isConditionnal then 
			if ltrue = [] then  if List.hd lfalse = true then var = assign else rien (1)
			else lfalse = [] then if List.hd ltrue = true then var = assign else rien (2)
		else var = assign (3)
donc 
cas 1 : l'expression de la condition est-elle de la forme i<N ...
cas 2 : l'expression de la condition  est-elle de la forme i<N ...
cas 3 : l'expression assign  est-elle de la forme i<N ...
la condition initiale doit être de type EQ ou NE ou une des precédente AND...
*)

end



and containBoolxAssignementIntoConditionnal x  iList completList  =
	if iList = [] then (false, false,NOTHING,[],[],"") (* isAssigned, onlyIntoIf ? assignement, conditionTrueList, conditionFalseList *)
	else
	begin 
		let (firstInst, nextInst) =  (List.hd iList, List.tl iList) in
		match firstInst with
			VAR (id, _) | TAB (id, _, _)  | MEMASSIGN (id, _, _) ->
					 if id = x then (true, false, NOTHING ,[],[], "")  
					 else containBoolxAssignementIntoConditionnal x  nextInst completList 
		 			 (* to be extended *)

			| BEGIN liste ->
				 let (isAssigned1, onlyIntoIf1, exp1, listTrue1, listFalse1, ifvar) = containBoolxAssignementIntoConditionnal x  liste completList  in
				 if isAssigned1 = false then containBoolxAssignementIntoConditionnal x  nextInst completList  
				 else if onlyIntoIf1 = true then
					  begin
							let  (isAssigned2, _, _, _, _,_) = containBoolxAssignementIntoConditionnal x  nextInst completList  in
							if  isAssigned2 = false then 
								(isAssigned1, onlyIntoIf1, exp1, listTrue1, listFalse1,ifvar) (* changed only into the 1th instruction *)
							else (* change into the two cases *) (true, false, NOTHING ,[],[],"")
					  end
					  else (true, false, NOTHING ,[],[],"")

			| IFVF (cond, i1, i2) ->
				let las1 = evalStore i1 [] [] in
				let las2 = evalStore i2 [] [] in
				let (existe1, existe2) = (existAffectVDsListeAS x las1, existAffectVDsListeAS x las2) in
			
				if (existe1 && existe2 = false ) then
				begin
					let extinc =  rechercheAffectVDsListeAS x las1  in
					match extinc with 
						MULTIPLE ->   (true, false, NOTHING ,[],[],"") 
						| EXP (e) -> 
							if e = NOTHING then  (true, false, NOTHING,[],[],"")  
							else 
							begin
								let (isAssigned1, _, _, _, _,_) = containBoolxAssignementIntoConditionnal x  nextInst completList  in
								if isAssigned1 = false then
								(			let idif = match  cond with EXP(VARIABLE(varIfN)) ->varIfN|_->"" in
											let(_,cond2) =  getCondIntoList idif completList in 
											(true, true, e ,[expVaToExp cond2],[],idif)
								) 
								else (true, false, NOTHING ,[],[],"") 
							end
 				end
				else 	if  existe2 &&  (existe1 = false ) then
					 	begin
							let extinc =  rechercheAffectVDsListeAS x las2  in
						   (	match extinc with
								MULTIPLE ->  (true, false, NOTHING ,[],[],"") 
								| EXP (e) -> 
									if e = NOTHING then  (true, false, NOTHING,[],[],"")  
									else 
									begin
										let (isAssigned1, _, _, _, _,_) = containBoolxAssignementIntoConditionnal x  nextInst completList  in
										if isAssigned1 = false then 
										(	
											let idif = match  cond with EXP(VARIABLE(varIfN)) ->varIfN|_->"" in
											let (_,cond2) = getCondIntoList idif completList in
											(true, true, e ,[],[expVaToExp cond2],idif) 
										) 
										else (true, false, NOTHING ,[],[],"") 
									end
							)
		 				end
						else (*if  (existe2 = false) &&  (existe1 = false ) then 
								containBoolxAssignementIntoConditionnal x  nextInst completList ifid
							 else*) (true, false,NOTHING ,[],[],"") (* on testera si dans les deux et égaux plus tard *)

			| IFV ( cond, i1) ->
				let las1 = evalStore i1 [] [] in
				if existAffectVDsListeAS x las1  then
				begin
					let extinc =  rechercheAffectVDsListeAS x las1  in
					match extinc with
						MULTIPLE -> (* modifié dans les plusieurs cas ou en fonction de plusieurs conditions on abandonne *)  
							(true, false, NOTHING ,[],[],"") 
						| EXP (e) -> 
							if e = NOTHING then  (true, false, NOTHING,[],[],"")  
							else 
							begin (*Printf.printf "containBoolxAssignementIntoConditionnal\n";*)
							(*	print_expVA cond; flush(); new_line();space(); Printf.printf "containBoolxAssignementIntoConditionnal fin\n";*)
								let (isAssigned1, _, _, _, _,_) = containBoolxAssignementIntoConditionnal x  nextInst completList  in
								if isAssigned1 = false then 
								(	let idif = match  cond with EXP(VARIABLE(varIfN)) ->varIfN|_->"" in
									let  (_,cond2) = getCondIntoList idif completList in (*print_expVA cond2; flush(); new_line();space(); new_line();*)
									(*Printf.printf "containBoolxAssignementIntoConditionnal fin2 pour variable %s\n" idif; *)						
									(true, true, e ,[expVaToExp cond2],[],idif)
								) 
								else (true, false, NOTHING ,[],[],"") 
							end
 				end
				else  containBoolxAssignementIntoConditionnal x  nextInst completList  (* on testera si dans les deux et égaux plus tard *)

			| FORV (_,_, _, _, _, _, body)-> 
				let las1 = evalStore body [] [] in
				if existAffectVDsListeAS x las1  then  (true, false, NOTHING,[],[],"")   
				else containBoolxAssignementIntoConditionnal x  nextInst completList   (* to be extended *) 

			| APPEL (_,_,_,_,_,_,_)-> (true, false, NOTHING,[],[],"")  
				(* to be extended REVOIR la variable peut être modifiée dans le corps ou pas dans un premier temps pessimiste est modifiée*)
	end



and traiterAffineForm  e var l=
if List.mem var (listeDesVarsDeExpSeules  e) = false then   (CONSTANTE, CONSTANT(CONST_INT "1"), CONSTANT(CONST_INT "0"), false ,true)
else
begin
let exp1 = calculer (EXP e) !infoaffichNull  [] 1 in
		if (estAffine var exp1)   then 
		begin 
			let (a,b) = calculaetbAffineForne var exp1 in		
			let (var1, var2) = (evalexpression a , evalexpression b) in
			let expVar2 = expressionEvalueeToExpression var2 in
			let expVar1 = expressionEvalueeToExpression var1 in
			if estNoComp var2 then (NONMONOTONE , NOTHING, NOTHING, false, false)
			else 	if intersection (listeDesVarsDeExpSeules expVar2)  l = [] then
					begin
						let nulCte = (estNul var2) in 
						if  (estStricPositif var1) then   (CROISSANT,expVar1, expVar2, estUn var1 , nulCte)
						else if estStricNegatif var1  then  (DECROISSANT,expVar1, expVar2, estMUn var1 , nulCte)
							 else   if (estNul var1) then  (CONSTANTE,expVar1, expVar2, false, false)
									else (NONMONOTONE , NOTHING, NOTHING, false, false)
					end
					else (NONMONOTONE , NOTHING, NOTHING, false, false)
		end
		else (NONMONOTONE , NOTHING, NOTHING, false, false)
end

and print_affine sens a b var=
	Printf.printf "var = %s\n" var; printSens sens; new_line(); print_expression a 0; new_line(); print_expression b 0; new_line();

and traiterArray  exp1 exp2 liste avant dans cte t c lv l inst =
	let  (res1, _)  = isTabDependCond exp1  liste avant dans cte t c lv l inst in
	let (res2, _)  = isTabDependCond exp2  liste avant dans cte t c lv l inst in
	(*Printf.printf " dans traiter array \n"; print_expression res1 0; new_line(); print_expression res2 0; new_line();*)
	if res1 = NOTHING then res2  else if res2 = NOTHING then res1  else	BINARY(AND, res1, res2)

and isTabDependCond exp1 liste avant dans cte t c lv l inst =
(* the condition depend on a element of an array but the element is not alway the same*)
(*Printf.printf "isTabDependCond\n"; print_expression exp1 0; new_line();*)
	 match exp1 with
		NOTHING 			-> (NOTHING, NOTHING)
		| UNARY (op, exp)	->let (res1, e1) = isTabDependCond exp liste avant dans cte t c lv l inst in
			(res1, UNARY (op,e1))
		| BINARY (op, exp1, exp2) ->
			let (res1, e1) =  isTabDependCond exp1 liste avant dans cte t c lv l inst in
			let (res2, e2) =  isTabDependCond exp2 liste avant dans cte t c lv l inst in
			if res1 = NOTHING then (res2 , BINARY(op, e1, e2))
			else if res2 = NOTHING then (res1, BINARY(op, e1, e2))  else	(BINARY(AND, res1, res2), BINARY(op, e1, e2))
		| QUESTION (exp1, exp2, exp3) ->
			let (res1, e1) =  isTabDependCond exp1 liste avant dans cte t c lv l inst in
			let (res2, e2) =  isTabDependCond exp2 liste avant dans cte t c lv l inst in
			let( res3 , e3) =  isTabDependCond exp3 liste avant dans cte t c lv l inst in
			let n = QUESTION (e1, e2, e3) in
			if res1 = NOTHING then 
				if res2 = NOTHING then (res3,n)  else if res3 = NOTHING then (res2,n) else	(BINARY(AND, res2, res3), n)
			else
				if res2 = NOTHING then  if res3 = NOTHING then (res1, n) else	(BINARY(AND, res1, res3),n)
				else if res3 = NOTHING then (BINARY(AND, res1, res2), n) else (BINARY(AND, res1, BINARY(AND,res2,res3)), n)
		| CAST (ty, exp) -> let (res1, e1) = isTabDependCond exp liste avant dans cte t c lv l inst  in
					(res1, CAST (ty, e1))
		| CALL (f, a)-> 
			let (res1, e1) =  isTabDependCond (COMMA(a)) liste avant dans cte t c lv l inst in 
			let n = match(e1) with COMMA l -> CALL (f,List.append [e1] l) |_-> exp1 in (res1, n)  
		| COMMA a -> 
			if a = [] then  (NOTHING, exp1)  
			else 
			begin
				let (res1, e1) =  isTabDependCond (List.hd a) liste avant dans cte t c lv l inst in
				let (res2, e2) =  isTabDependCond (COMMA(List.tl a)) liste avant dans cte t c lv l inst in
				let n = match(e2) with COMMA l -> (COMMA(List.append [e1] l)) |_-> exp1 in
				if res1 = NOTHING then (res2, n) 
				else if res2 = NOTHING then (res1, n)  else	(BINARY(AND, res1, res2), n) 
			end
		| EXPR_SIZEOF exp  -> let (res1, e1) = isTabDependCond exp liste avant dans cte t c lv l inst in
					(res1, EXPR_SIZEOF (e1))
		| EXPR_LINE (exp, a, b)	-> let (res1, e1) = isTabDependCond exp liste avant dans cte t c lv l inst in
					(res1, EXPR_LINE (e1, a ,b))
		| INDEX (exp, idx) ->
			let (tab,lidx) = analyseArray exp1 []  in
		
			if tab = "" then (NOTHING, exp1)
			else
			begin
				let size = getAssosArrayIDsize tab in
				match size with 
					NOSIZE -> (NOTHING, exp1)
					| SARRAY (v) ->
								(*Printf.printf "simgle size array\n"; 		*)	
							let inter2 =  intersection (listeDesVarsDeExpSeules idx)  l in		
							
							let  isOnlyVar =  if inter2 = [] then false else if List.tl inter2 = [] then true else false in
							if isOnlyVar then 
							begin
								let var = List.hd inter2 in	
								let ((*isindirect,inc,var, before*)isindirect,_,_,_,isMultiInc) =  getLoopVarInc var inst in

								if isMultiInc then isExactForm := false;
								if isindirect then expressionIncFor := NOTHING;
								let valinc = calculer (applyStoreVA   (EXP(!expressionIncFor)) [])  !infoaffichNull  [](*appel*) 1 in	
								let sensinc = 
									if estNoComp valinc then NDEF 
									else 
										if !opEstPlus (*op +or -*) then 
											if estNul valinc then INCVIDE else if estStricPositif valinc then POS  else NEG
										else NOVALID	 
									 in
								
								 if sensinc = POS then 
										( BINARY(LE, idx,BINARY(SUB,CONSTANT(CONST_INT (Printf.sprintf "%d" v)), CONSTANT(CONST_INT "1"))	), exp1)
								 else if sensinc = NEG then (BINARY(GE,idx, CONSTANT(CONST_INT "0")), exp1)
									  else if sensinc != NOVALID then (BINARY(AND, BINARY(GE,idx, CONSTANT(CONST_INT "0"))(*idx>=0*) , 
												 BINARY(LE, idx,BINARY(SUB,CONSTANT(CONST_INT (Printf.sprintf "%d" v)), CONSTANT(CONST_INT "1"))) )
											, exp1)
											else  (NOTHING, exp1) 
							end
							else  (NOTHING, exp1) 
					| MSARRAY (lsize) ->    (setIndexWithSize lidx lsize liste avant dans cte t c lv l inst, exp1)
			end
				
		| VARIABLE name ->  let b=  existAssosPtrNameType  name   in (* AMAJ*)

					if b = true then 
					begin 
					(*	Printf.printf"mane %s is tabptr\n" name;*)
						opEstPlus:= true;	
						 
						(*Printf.printf"expression : \n"; print_expression affect 0; new_line();*)
						let ((*isindirect,inc,var, before*)isindirect,_,_,_,isMultiInc) =  getLoopVarInc name inst in
(*BOOL pas pour le moment ???*)
						if isindirect then  expressionIncFor := NOTHING;
						if isMultiInc then isExactForm := false;

						
						let valinc = calculer (applyStoreVA   (EXP(!expressionIncFor)) [])  !infoaffichNull  [](*appel*) 1 in	
						let sensinc = 
									if !opEstPlus (*op +or -*) then 
										if estNoComp valinc then NDEF 
										else  if estNul valinc then INCVIDE else if estStricPositif valinc then POS  else NEG
									else NOVALID		 
									 in
						let varName =  Printf.sprintf "%s_%s" "getvarTailleTabMax" name in
						let appel =  VARIABLE(varName) in 
					
						let expCroi = BINARY(LE, exp1,BINARY(SUB,appel, CONSTANT(CONST_INT "1"))) in
						let expDec =  BINARY(GE,exp1, CONSTANT(CONST_INT "0")) in
					(*	print_expression appel 0; new_line();	
						print_expression expCroi 0; new_line();	
						print_expression expDec 0; new_line();	*)
						match sensinc with	
						 POS ->(*Printf.printf"inc pos\n"; *) (expCroi, exp1)
						| NEG ->(*Printf.printf"inc neg\n";*) (expDec, exp1)
						| NDEF ->(*Printf.printf"inc nocomp\n"; *)(BINARY(AND,expDec , expCroi ), exp1)
						|_-> (*Printf.printf"inc autre :NOVALID ou const\n";*) (NOTHING, exp1)
					end 
					else begin (*Printf.printf"mane %s is not tabptr\n"name;*) (NOTHING, exp1) end							
					
		| MEMBEROF (exp, fld) ->(*Printf.printf "MEMBEROF\n";print_expression exp1 0; new_line();*)(* actuellement  non traitée *) (NOTHING, exp1) 
		| MEMBEROFPTR (exp, fld) ->(*Printf.printf "MEMBEROFPTR\n";print_expression exp1 0; new_line();*)(* actuellement  non traitée *) (NOTHING, exp1) 
		|_ ->(* actuellement  non traitée *) (NOTHING, exp1) 

and isArrayPtr v avant  =
	if existAssosArrayIDsize v then (v, true) else 
	begin
		let (nv,_) = analyseArray(expVaToExp(rechercheAffectVDsListeAS v avant))  [] in
		if nv <> "" then isArrayPtr nv avant  else ("",false)
	end

	
and setIndexWithSize lidx lsize liste avant dans cte t c lv l inst= 
	if lidx = [] || lsize = [] then NOTHING
	else 
	begin
		let testNext = setIndexWithSize (List.tl lidx) (List.tl lsize) liste avant dans cte t c lv l inst in
		let idx = List.hd lidx in
		let inter2 =  intersection (listeDesVarsDeExpSeules idx)  l in		
					
		let  isOnlyVar =  if inter2 = [] then false else if List.tl inter2 = [] then true else false in
		if isOnlyVar then 
		begin
			let var = List.hd inter2 in	
			let ((*isindirect,inc,var, before*)isindirect,_,_,_,isMultiInc) =  getLoopVarInc var inst in
(*BOOL*)
			if isMultiInc then isExactForm := false;
			expressionIncFor := if isindirect then  NOTHING else !expressionIncFor ;
				
			let valinc = calculer (applyStoreVA   (EXP(!expressionIncFor)) [])  !infoaffichNull  [](*appel*) 1 in	
			let sensinc = if estNoComp valinc then NDEF 
				  else if !opEstPlus (*op +or -*) then 
							if estNul valinc then INCVIDE else if estStricPositif valinc then POS  else NEG
							else (*op *or /*)
							begin
								let varMoinsUn = (evalexpression (Diff( valinc,  ConstInt("1")))) in
								if estStricPositif valinc then
								begin
									if estNul varMoinsUn then	  INCVIDE else   if estStricPositif varMoinsUn then POS else  NEG
								end
								else NOVALID
							end in
 			let nt =
				if sensinc = POS then BINARY(LE, idx,BINARY(SUB,CONSTANT(CONST_INT (Printf.sprintf "%d" (List.hd lsize))), CONSTANT(CONST_INT "1"))	)
				else if sensinc = NEG then BINARY(GE,idx, CONSTANT(CONST_INT "0"))
					 else BINARY(AND, BINARY(GE,idx, CONSTANT(CONST_INT "0"))(*idx>=0*) , 
								BINARY(LE, idx,BINARY(SUB,CONSTANT(CONST_INT (Printf.sprintf "%d" (List.hd lsize))), CONSTANT(CONST_INT "1"))	) ) in

			if testNext = NOTHING then nt else BINARY(AND, testNext,nt)
		end	
		else testNext
	end


and recherchePow init var op exp1 exp2 liste avant dans cte t c lv l isLoopCtee1 isLoopCtee2 inst=


	let (ninit,nv, nop,ne1,ne2,nl , fin)=
	if isLoopCtee1 then (* exp1 is loop constant *)  
	begin
		let (ispow, k,a,b) = isPowCte var exp2 in 
		if ispow then 
		begin
			(*printResPow var k a b ;*)
			let val1 = calculer (EXP a) !infoaffichNull  []  1 in
			let v_1 =(evalexpression (Diff (val1, ConstInt("1")))) in
			if estDefExp val1 then
				if estStricPositif   v_1 then
					( init, var, op,CALL (VARIABLE("pow"), List.append [BINARY(DIV, BINARY(SUB,exp1,b),a)] [BINARY(DIV,CONSTANT(CONST_FLOAT "1.0"),k)]), 
										  VARIABLE(var) ,liste, true ) (* we replace exp1 op a*pow(var, k)+b by pow((EXP1 -B)/A, 1/K) OP VAR *)
				else 
					if estNul  v_1 then ( init, var, op,exp1, exp2,liste, false ) 
					 else (  init, var, changeCompOp op ,
							 CALL (VARIABLE("pow"),List.append [BINARY(DIV, BINARY(SUB,exp1,b) ,a)] 
									[BINARY(DIV, CONSTANT (CONST_FLOAT "1.0"),k)]), VARIABLE(var) ,liste ,true)
													(* we replace exp1 op a*pow(var, k)+b by pow((EXP1 -B)/A, 1/K) OP VAR *)
			else if liste = [] then ( init, var, op,exp1, exp2,liste, false ) 
				 else  (VARIABLE(List.hd liste), (List.hd liste), op, exp1, exp2,  (List.tl liste), true)
		end 
		else  if liste = [] then ( init, var, op,exp1, exp2,liste, false ) 
				 else  (VARIABLE(List.hd liste), (List.hd liste), op, exp1, exp2,  (List.tl liste), true)
	end 
	else 	
		if isLoopCtee2  then (* exp2 is loop constant *)  
		begin
(*Printf.printf "traitement de exp2 cte exp1  pow ???\n";	*)
			(*Printf.printf "traitement de exp2 cte exp1  pow ???\n";	*)
			let (ispow, k,a,b) = isPowCte var exp1 in 
			if ispow then 
			begin
				(*printResPow var k a b ;*)
				let val1 = calculer (EXP a) !infoaffichNull  [] 1 in
				let v_1 =(evalexpression (Diff (val1, ConstInt("1")))) in
				if estDefExp val1 then
					if estStricPositif v_1 then
						(init, var, op, VARIABLE(var), CALL (VARIABLE("pow"),List.append [BINARY(DIV, BINARY(SUB,exp2,b) ,a)] 
							[BINARY(DIV, CONSTANT (CONST_FLOAT "1.0"),k)]) ,liste ,true)
											(* we replace exp1 op a*pow(var, k)+b by pow((EXP1 -B)/A, 1/K) OP VAR *)
					else if estNul v_1 then ( init, var, op,exp1, exp2,liste, false ) 
						 else  (init ,var, (changeCompOp op), VARIABLE(var),
							CALL (VARIABLE("pow"),List.append [BINARY(DIV, BINARY(SUB,exp2,b) ,a)] 
								[BINARY(DIV, CONSTANT (CONST_FLOAT "1.0"),k)]) ,liste, true)
						(* we replace exp1 op a*pow(var, k)+b by pow((EXP1 -B)/A, 1/K) OP VAR *)

				else  if liste = [] then ( init, var, op,exp1, exp2,liste, false ) 
				 else  (VARIABLE(List.hd liste), (List.hd liste), op, exp1, exp2,  (List.tl liste), true)
			end 
			else  if liste = [] then ( init, var, op,exp1, exp2,liste, false ) 
				 else  (VARIABLE(List.hd liste), (List.hd liste), op, exp1, exp2,  (List.tl liste), true)
		end 
		else if liste = [] then ( init, var, op,exp1, exp2,liste, false ) 
				 else  (VARIABLE(List.hd liste), (List.hd liste), op, exp1, exp2,  (List.tl liste), true)
		in
		if fin = false then 
			(
				if (List.length l) = 2 then
				begin
					(*Printf.printf "deux variables ou plus non const %d \n" (List.length l) ;*)
					let ( isindirect1,inc1,vari1, before1,isMultiInc1) =  getLoopVarInc (List.hd l) inst in
					let ( isindirect2,inc2,vari2, before2,isMultiInc2) =  getLoopVarInc (List.hd (List.tl l)) inst in


					let (typeinc1, typeinc2)= (getIncType inc1,getIncType inc2) in
				(*	Printf.printf "deux variables ou plus non const %s %s\n" vari1 vari2 ;
	 				print_expression exp1 0; new_line();
 					print_expression exp2 0; new_line();
					print_intType (getIncType inc1); print_expression (getIncValue inc1) 0; new_line();
					print_intType (getIncType inc2); print_expression (getIncValue inc2) 0; new_line();*)
					let isLeft1 = List.mem (List.hd l) (listeDesVarsDeExpSeules exp1) in
					let isLeft2 = List.mem (List.hd (List.tl l)) (listeDesVarsDeExpSeules exp1) in
					let oppose =  (isLeft1 &&  isLeft2 = false) || (isLeft2 &&  isLeft1 = false) in
				
					let isOK = control inc1 inc2 oppose isMultiInc1 isMultiInc2 (BINARY(SUB,exp2, exp1)) (List.hd l) (List.hd (List.tl l)) in
					
					
					let value =
						if oppose then 
							if typeinc1 =POSITIV||typeinc1 =NEGATIV then
							( calculer (EXP(BINARY(SUB,getIncValue inc1,getIncValue inc2)))  !infoaffichNull [] 1)
							else calculer (EXP(BINARY(DIV,getIncValue inc1,getIncValue inc2)))  !infoaffichNull [] 1
						else
	  						if typeinc1 =POSITIV||typeinc1 =NEGATIV then
								if isLeft1 then
								begin
									let newexp = ((remplacerValPar  (List.hd (List.tl l)) (getIncValue inc2) (remplacerValPar  (List.hd l) (getIncValue inc1) exp1))) in
									calculer (EXP(newexp))  !infoaffichNull [] 1

								end
								else
								begin
									let newexp = UNARY(MINUS,(remplacerValPar  (List.hd (List.tl l)) (getIncValue inc2) (remplacerValPar  (List.hd l) (getIncValue inc1) exp2))) in
									calculer  (EXP(newexp))   !infoaffichNull [] 1
								end

							else calculer (EXP(BINARY(DIV,getIncValue inc1,getIncValue inc2)))  !infoaffichNull [] 1 in
		 			(*Printf.printf " result inc : > %f\n"( getDefValue value);*)
					if isOK &&(typeinc1 =POSITIV||typeinc1 =NEGATIV) &&  (typeinc2 =POSITIV||typeinc2 =NEGATIV) && isindirect1 = false && isindirect2 == false then
					begin
						let vardeux =  Printf.sprintf "%s-%s" (List.hd l) (List.hd (List.tl l))  in	 
						let (stringinc,estNul,estPos, constval)=
							match value with
							 ConstInt (i)-> (i ,(int_of_string  i = 0),(int_of_string  i > 0),CONSTANT  (CONST_INT i))
							| ConstFloat (i) ->(i, (float_of_string  i = 0.0),(float_of_string  i > 0.0),CONSTANT(CONST_FLOAT (i)) ) 
							| RConstFloat (i) ->(Printf.sprintf "%g" i, (  i = 0.0),(  i > 0.0),CONSTANT(RCONST_FLOAT (i)) ) 
							| _->("",true,false,CONSTANT  (CONST_INT "0")) in

							if estPos then
							begin
								(*Printf.printf "deux variables ou plus non const %s %s %s  %s ++\n" vari1 vari2 vardeux stringinc ;*)
									let newinst =  List.append inst [new_instVar  vardeux  (EXP(BINARY (ADD,VARIABLE(vardeux), constval))) ] in
									let newdans =  List.append dans 
														[ASSIGN_SIMPLE(vardeux,  EXP(BINARY (ADD,VARIABLE(vardeux), constval)))]
	
														 in	
									listADD := List.append [VAR(vardeux, EXP(BINARY(SUB,exp1, exp2)))] !listADD ;
									listADDInc := List.append [VAR(vardeux, EXP(BINARY(ADD,VARIABLE(vardeux), constval)))] !listADDInc ;
									let newavant =  List.append avant
														[ASSIGN_SIMPLE(vardeux, EXP(BINARY(SUB,exp1, exp2)))]
	
														 in	
	
									rechercheConditionBinary (VARIABLE(vardeux))  vardeux op  (VARIABLE(vardeux)) (CONSTANT  (CONST_INT "0"))  [vardeux] newavant newdans estNul  t 
											(BINARY(op,VARIABLE(vardeux),   CONSTANT(CONST_INT "0") )) lv (List.append [vardeux] l) newinst
							end
							else
							begin
								(*Printf.printf "deux variables ou plus non const %s %s %s  %s --\n" vari1 vari2 vardeux stringinc ;*)
								let newinst =  List.append inst [new_instVar  vardeux  (EXP(BINARY (SUB,VARIABLE(vardeux), constval))) ] in
									let newdans =  List.append dans 
														[ASSIGN_SIMPLE(vardeux,  EXP(BINARY (SUB,VARIABLE(vardeux), constval)))]
	
														 in	
									listADD := List.append [VAR(vardeux, EXP(BINARY(SUB,exp2, exp1)))] !listADD ;
									listADDInc := List.append [VAR(vardeux, EXP(BINARY(SUB,VARIABLE(vardeux), constval)))] !listADDInc ;
									let newavant =  List.append avant
														[ASSIGN_SIMPLE(vardeux, EXP(BINARY(SUB,exp2, exp1)))]
	
														 in	
	
									rechercheConditionBinary (VARIABLE(vardeux))  vardeux op  (CONSTANT  (CONST_INT "0")) (VARIABLE(vardeux)) [vardeux] newavant newdans estNul  t 
											(BINARY(op, CONSTANT(CONST_INT "0"),  VARIABLE(vardeux))) lv (List.append [vardeux] l) newinst
							end

					end 
					else	if oppose && isOK &&(typeinc1 =MULTI) &&  (typeinc2 =DIVI) && isindirect1 = false && isindirect2 == false then
						begin
							let vardeux =  Printf.sprintf "%s-%s" (List.hd l) (List.hd (List.tl l))  in	 
							let (stringinc,estNul,constval)=
							match value with
							 ConstInt (i)-> (i ,(int_of_string  i = 1),CONSTANT  (CONST_INT i))
							| ConstFloat (i) ->(i, (float_of_string  i = 1.0),CONSTANT(CONST_FLOAT (i)) ) 
							| RConstFloat (i) ->(Printf.sprintf "%g" i, (  i = 1.0),CONSTANT(RCONST_FLOAT (i)) ) 
							| _->("",true,CONSTANT  (CONST_INT "1")) in


						(*Printf.printf "deux variables ou plus non const %s %s %s  \n" vari1 vari2 vardeux  ;*)
							let newinst =  List.append inst [new_instVar  vardeux  (EXP(BINARY (DIV,VARIABLE(vardeux), constval))) ] in
							let newdans =  List.append dans 
												[ASSIGN_SIMPLE(vardeux,  EXP(BINARY (DIV,VARIABLE(vardeux), constval)))]
	
												 in	
							listADD := List.append [VAR(vardeux, EXP(BINARY(DIV,exp2, exp1)))] !listADD ;
							listADDInc := List.append [VAR(vardeux, EXP(BINARY(DIV,VARIABLE(vardeux), constval)))] !listADDInc ;
							let newavant =  List.append avant
												[ASSIGN_SIMPLE(vardeux, EXP(BINARY(DIV,exp2, exp1)))]
	
												 in	
	
							rechercheConditionBinary (BINARY(DIV,exp2, exp1)) vardeux op  (CONSTANT  (CONST_INT "1")) (VARIABLE(vardeux)) [vardeux] newavant newdans estNul t 
									(BINARY(op, CONSTANT(CONST_INT "1"),  VARIABLE(vardeux))) lv (List.append [vardeux] l) newinst

						end 

						else	if oppose && isOK && (typeinc1 =DIVI) &&  (typeinc2 =MULTI) && isindirect1 = false && isindirect2 == false then
						begin
							let vardeux =  Printf.sprintf "%s-%s" (List.hd l) (List.hd (List.tl l))  in	 
							let (stringinc,estNul,constval)=
							match value with
							 ConstInt (i)-> (i ,(int_of_string  i = 1),CONSTANT  (CONST_INT i))
							| ConstFloat (i) ->(i, (float_of_string  i = 1.0),CONSTANT(CONST_FLOAT (i)) ) 
							| RConstFloat (i) ->( Printf.sprintf "%g" i, ( i = 1.0),CONSTANT(RCONST_FLOAT (i)) ) 
							| _->("",true,CONSTANT  (CONST_INT "1")) in

						(*Printf.printf "deux variables ou plus non const inc1 dive%s %s %s  \n" vari1 vari2 vardeux  ;*)
							let newinst =  List.append inst [new_instVar  vardeux  (EXP(BINARY (MUL,VARIABLE(vardeux), constval))) ] in
							let newdans =  List.append dans 
												[ASSIGN_SIMPLE(vardeux,  EXP(BINARY (MUL,VARIABLE(vardeux), constval)))]
	
												 in	
							listADD := List.append [VAR(vardeux, EXP(BINARY(DIV,exp1, exp2)))] !listADD ;
							listADDInc := List.append [VAR(vardeux, EXP(BINARY(MUL,VARIABLE(vardeux), constval)))] !listADDInc ;
							let newavant =  List.append avant
												[ASSIGN_SIMPLE(vardeux, EXP(BINARY(DIV,exp1, exp2)))]
	
												 in	
	
							rechercheConditionBinary (VARIABLE(vardeux))  vardeux op  (VARIABLE(vardeux)) (CONSTANT  (CONST_INT "1"))  [vardeux] newavant newdans estNul t 
									(BINARY(op,   VARIABLE(vardeux),CONSTANT(CONST_INT "1"))) lv (List.append [vardeux] l) newinst



						end 

					else (NONMONOTONE , NOTHING, NOTHING, XOR, true, var, BINARY(op,exp1, exp2))(* if exp1 != 0 we can do the same thing with MULTI...*)
				end else (NONMONOTONE , NOTHING, NOTHING, XOR, true, var, BINARY(op,exp1, exp2)))			 
		(*NONMONOTONE , NOTHING, NOTHING, XOR, true, var, BINARY(op,exp1, exp2))*)
		else rechercheConditionBinary ninit nv nop ne1 ne2 nl avant dans cte t c lv l inst
 
and control inc1 inc2 oppose isMultiInc1 isMultiInc2 exp v1 v2 =
if isMultiInc1 =false && isMultiInc2 =false  then((*Printf.printf "No multidef inc\n"  ;*) true)
else
begin
 
	let newexp2 =  calculer (EXP(remplacerValPar  v1 (CONSTANT(CONST_INT("0"))) exp))  !infoaffichNull [] 1 in
	let newexp1 =  calculer (EXP(remplacerValPar  v2 (CONSTANT(CONST_INT("0"))) exp))  !infoaffichNull [] 1 in
	let (sens1,vsens1) =
		if (estAffine v1 newexp1)   then 
			begin 
				let (a,b) = calculaetbAffineForne  v1 newexp1 in		
				let (var1, var2) = (evalexpression a , evalexpression b) in
				if  (estStricPositif var1) then (CROISSANT,1)
				else begin if (estNul var1) then  (CROISSANT,1)  else (DECROISSANT,-1) end
			end
		else (NONMONOTONE,0) in

	let (sens2,vsens2) =
		if (estAffine v2 newexp2)   then 
			begin 
				let (a,b) = calculaetbAffineForne  v2 newexp2 in		
				let (var1, var2) = (evalexpression a , evalexpression b) in
				if  (estStricPositif var1) then (CROISSANT,1)
				else begin if (estNul var1) then  (CROISSANT,1)  else (DECROISSANT,-1)  end
			end
		else (NONMONOTONE,0) in
	(*Printf.printf "same sens inc1\n"  ;
(isCroissant inc1 ); if vsens1 = 1 then Printf.printf "croissant\n"  else Printf.printf "decroissant\n" ;


	Printf.printf "same sens inc2\n"  ;
(isCroissant inc2 ); if vsens2 = 1 then Printf.printf "croissant\n"  else Printf.printf "decroissant\n" ;*)

	
	let realSens1 = if oppose = false then (isCroissant inc1 ) * vsens1 else (isCroissant inc1 ) * vsens1  in
	let realSens2 =   (isCroissant inc2 ) * vsens2   in

	if realSens1 * realSens2 =1 then ((*Printf.printf "same sens\n"  ;*)true )
	else 
		if isMultiInc1  && isMultiInc2   then false
		else
		begin
			let (val1, val2) =(abs_float (getDefValue( calculer (EXP(getIncValue inc1))  !infoaffichNull [] 1)), abs_float (getDefValue(calculer (EXP(getIncValue inc2))  !infoaffichNull [] 1))) in  
			if val1 = val2 then false else  if val1 > val2 then  isMultiInc2  = false else  isMultiInc1  = false 
			 (*only the biggest absolute value  may be minimised*)

		end
end

and traiterUn croissant  borneInf borneSup operateur multiple var  cond avant dans cte t inst=
	let ninst =(* List.append inst !listADDInc *) (*inst*)  List.append inst !listADDInc in
	let (operateur, typevar, multiple,v) = 
		if multiple = false then
		begin
				if croissant = CROISSANT then begin borne:=borneSup; initialisation:=borneInf end 
				else begin  borne:=borneInf; initialisation:=borneSup   end;
				(operateur,croissant, false, var) 
		end		
		else 	( ADD, NONMONOTONE, true, var)   in

	let (isindirect,inc,vari,before,isMultiInc) =  getLoopVarInc v ninst in
	(*BOOL*)
	
	expressionIncFor := getIncValue inc;
	opEstPlus := getIsAddInc inc;
	let (sup, inf, incr) = 
	 	if !opEstPlus = false && (isDivInc !expressionIncFor)  && typevar = DECROISSANT then 
			(!initialisation,!borne, BINARY (DIV, CONSTANT  (CONST_INT "1"), !expressionIncFor)) 
		 else
				if !opEstPlus && typevar = DECROISSANT then  (!initialisation,!borne, !expressionIncFor)  
		 		else  (!borne,!initialisation,!expressionIncFor) in

	
	if isMultiInc then isExactForm := false;
		if isindirect then 
		begin			
			expressionIncFor := NOTHING; (* 1+*)
			(NOTHING,NOTHING, true,NOTHING)
		end
		else 
			(match  inc  with 
				NODEFINC ->   (* 1+*)
				(NOTHING,NOTHING, false,NOTHING)
			|_->	(*print_expression borneInf 0; space() ;flush() ;new_line(); flush();new_line(); *)
(*Printf.printf"traiterUn v = %s vari = %s\n" v vari;
print_expression inf 0; space() ;flush() ;new_line(); flush();new_line(); 
	print_expression sup 0; space() ;flush() ;new_line(); flush();new_line(); 
print_expression incr 0; space() ;flush() ;new_line(); flush();new_line();
			*)

	let infoVar =   new_variation borneInf borneSup  incr typevar  operateur false in

	let nb = expVaToExp (getNombreIt sup (typevar=CONSTANTE||cte) t cond multiple [] (getIsAddInc inc)  infoVar v []) in
	let borne = (getBorneBoucleFor t nb inf incr (getIsAddInc inc) isindirect) in
(*Printf.printf"traiterUn v = %s vari = %s\n" v vari;
print_expression nb 0; space() ;flush() ;new_line(); flush();new_line(); 
	print_expression borne 0; space() ;flush() ;new_line(); flush();new_line(); *)

	(nb, incr, false,borne))



and construireCondition crois1 bInf1  bSup1  oper1 mult1 v1 cd1 crois2  bInf2  bSup2  oper2 mult2 v2 cd2 lv avant dans cte t inst=

(*Printf.printf"construireCondition \n";	*)
	let (nb1, inc1, indirect1,b1) = traiterUn  crois1 bInf1 bSup1  oper1 mult1 v1 cd1 avant dans cte t  inst in
	let (nb2, inc2, indirect2,b2) = traiterUn  crois2 bInf2  bSup2 oper2 mult2 v2 cd2 avant dans cte t inst in

	if inc1 = NOTHING  then begin (* Printf.printf"construireCondition inc1 not def\n";*) isExactForm := false; (crois2, bInf2, bSup2, oper2,mult2, v2, BINARY(AND, cd1,cd2)) end
	else
		if  inc2 = NOTHING then begin  (*  Printf.printf"construireCondition inc 2 not def\n";*) isExactForm := false;(crois1, bInf1, bSup1, oper1,mult1, v1, BINARY(AND, cd1,cd2 )) end
		else 
			if v1 = v2 then
			begin (*Printf.printf"construireCondition egal %s\n" v1;*)
				match crois1 with
					CROISSANT | DECROISSANT-> (*Printf.printf"construireCondition egal crois 1 ok %s\n" v1;	*)
						if crois2 = CROISSANT || crois2 = DECROISSANT then
						begin
							let bInf =  if bInf1 != NOTHING && bInf2 != NOTHING then
										begin 
											if bInf1 = bInf2 then begin 
												isExactForm := false; bInf1 
											end
											else CALL (VARIABLE("MAXIMUM") , (List.append [bInf1] [bInf2])) 
										end
										else if bInf1 = NOTHING then bInf2 else bInf1 in
(*Printf.printf"construireCondition binfs\n"  ;
							print_expression bInf1 0; space() ;flush() ;new_line(); flush();new_line(); 
	print_expression bInf2 0; space() ;flush() ;new_line(); flush();new_line(); 

print_expression bInf 0; space() ;flush() ;new_line(); flush();new_line(); *)
							let bSup =  if bSup2 != NOTHING  && bSup1 != NOTHING then
										begin if bSup2 = bSup1 then bSup1 else (CALL (VARIABLE("MINIMUM") , (List.append [bSup1] [bSup2] ))) end
										else if bSup1 = NOTHING then begin isExactForm := false; bSup2 end else begin isExactForm := false; bSup1 end in

(*Printf.printf"construireCondition bsups\n"  ;
							print_expression bSup1 0; space() ;flush() ;new_line(); flush();new_line(); 
	print_expression bSup2 0; space() ;flush() ;new_line(); flush();new_line(); 

print_expression bSup 0; space() ;flush() ;new_line(); flush();new_line(); *)

							if bSup != NOTHING && bInf!= NOTHING then (crois1, bInf, bSup, oper1,false,v1, BINARY(AND, cd1,cd2))
							else	begin isExactForm := false; (NONMONOTONE , NOTHING, NOTHING, XOR,true,v1,BINARY (AND, cd1,cd2)) end
						end 
						else 
							(* if crois2 = NONMONOTONE || (crois2 = CONSTANTE && bSup2 = NOTHING) (*revoir*)	
							 then *) 
						begin
								(*Printf.printf"construireCondition egal crois1 croissant ou decroissant, crois2 non monoto%s\n" v1;*)	 
								isExactForm := false; 
								(crois1, bInf1, bSup1, oper1,mult1, v1, BINARY(AND, cd1,cd2)) 
						end(*
							 else begin isExactForm := false; (CONSTANTE, NOTHING, bSup2, oper1,false,v2 , BINARY(AND, cd1,cd2) ) end*)
					| NONMONOTONE ->isExactForm := false; (crois2, bInf2, bSup2, oper2,mult2, v2, BINARY(AND, cd1,cd2))
					| CONSTANTE -> isExactForm := false;
								  (* if bSup2 = NOTHING then  (CONSTANTE, NOTHING, bSup1, oper2,false, v1, BINARY(AND, cd1,cd2) )
								   else *)(crois2, bInf2, bSup2, oper2,mult2, v2, BINARY(AND, cd1,cd2))
				end
			else
			begin (*Printf.printf"construireCondition diff\n";*)
				if  nb1 = NOTHING then begin isExactForm := false; (crois2, bInf2, bSup2, oper2,mult2, v2, BINARY(AND, cd1,cd2)) end
				else
				begin
					if  nb2 = NOTHING then begin expressionIncFor := inc1;  isExactForm := false;(crois1, bInf1, bSup1, oper1,mult1, v1, BINARY(AND, cd1,cd2 )) end
					else((*Printf.printf"construireCondition diff\n";*) (	CROISSANT, CONSTANT (CONST_INT "0"), (*CONSTANT (CONST_INT "1")*)
							BINARY (SUB, CALL (VARIABLE("MINIMUM") , List.append [ b1] [b2] ), CONSTANT (CONST_INT "1")),
							  LT,mult2, lv, BINARY(AND, cd1,cd2)))
				end
			end

and traiterARRAYANDCOND init var testA op exp1 exp2  liste avant dans cte t c lv l isLoopCtee1 isLoopCtee2 inst =					
	 let (crois1,bInf1, bSup1, oper1,mult1,v1, cd1)=
			recherchePow init var op exp1 exp2 liste avant dans cte t c lv l isLoopCtee1 isLoopCtee2 inst in
	 let (crois2, bInf2, bSup2, oper2,mult2,v2, cd2) =
			match testA with 
				BINARY (op2, exp21, exp22) ->  
					rechercheConditionBinary init var AND testA (BINARY (op, exp1, exp2)) liste avant dans  cte t 
						(BINARY (AND, testA,(BINARY (op, exp1, exp2)) ))  lv l inst
				|_-> 	(NONMONOTONE , NOTHING, NOTHING, XOR, true, var, c) in

	(*listADD := List.append  avant !listADD ;
							listADDInc := List.append [VAR(vardeux, EXP(BINARY(MUL,VARIABLE(vardeux), constval)))] !listADDInc ;

					let newinst =  List.append inst [new_instVar  vardeux  (EXP(BINARY (DIV,VARIABLE(vardeux), constval))) ] in
							let newdans =  List.append dans 
												[ASSIGN_SIMPLE(vardeux,  EXP(BINARY (DIV,VARIABLE(vardeux), constval)))]
	
												 in	
							listADD := List.append [VAR(vardeux, EXP(BINARY(DIV,exp1, exp2)))] !listADD ;
							listADDInc := List.append dans !listADDInc ;
							let newavant =  List.append avant
												[ASSIGN_SIMPLE(vardeux, EXP(BINARY(DIV,exp1, exp2)))]
	
												 in	*)

		if crois1 = NONMONOTONE then  
		begin isExactForm := false; (*Printf.printf "only tab %s\n" v2;*)(crois2, bInf2, bSup2, oper2,mult2,v2, cd2)end
		else construireCondition crois1 bInf1  bSup1  oper1 mult1 v1 cd1 crois2  bInf2  bSup2  oper2 mult2 v2 cd2 lv  avant    dans cte t  inst 


and traiterANDCOND init var exp1 exp2 liste avant dans cte t c lv l inst =
			 
(*
Printf.printf" traiterANDCOND %s\n" var;
print_expression exp1 0; space() ;flush() ;new_line(); flush();new_line(); 
print_expression exp2 0; space() ;flush() ;new_line(); flush();new_line(); *)
	if liste = [] then 
	begin (*Printf.printf"cas 1 traiterANDCOND exp1  \n";*)	
		 let (crois1,bInf1, bSup1, oper1,mult1,v1,cd1)=
			match exp1 with
				BINARY (op1, exp11, exp12) -> rechercheConditionBinary init var op1 exp11 exp12 [] avant dans cte t exp1 lv l inst
				| VARIABLE name -> 
					rechercheConditionBinary (VARIABLE name)  name NE (VARIABLE name) (CONSTANT (CONST_INT "0")) [] avant dans cte t exp1 lv l inst
				| UNARY (op, exp) -> 
							(match op with 
								NOT ->  
									rechercheConditionBinary init var EQ exp (CONSTANT (CONST_INT "0")) [] avant dans cte t c lv l inst
							 	|_-> 	(  NONMONOTONE , NOTHING, NOTHING, XOR, true, var , c) (*pas multiple voir pour les booleens*))
				|_-> (*Printf.printf"cas 1 traiterANDCOND exp1 is not Binary boolean ???\n";	*)(NONMONOTONE , NOTHING, NOTHING, XOR, true, var, c) in




		let (crois2, bInf2, bSup2, oper2,mult2,v2, cd2) =
			match exp2 with 
				BINARY (op2, exp21, exp22) ->  rechercheConditionBinary init var op2 exp21 exp22 [] avant dans  cte t exp2  lv l inst
				| VARIABLE name ->   
					rechercheConditionBinary (VARIABLE(name))  name NE (VARIABLE (name)) (CONSTANT (CONST_INT "0")) [] avant dans cte t exp2 lv l inst
				| UNARY (op, exp) -> 
							(match op with 
								NOT ->  
									rechercheConditionBinary init var EQ exp (CONSTANT (CONST_INT "0")) [] avant dans cte t c lv l inst
							 	|_-> 	(  NONMONOTONE , NOTHING, NOTHING, XOR, true, var , c) (*pas multiple voir pour les booleens*))
				|_-> (*Printf.printf"cas 1 traiterANDCOND exp2 is not Binary boolean ???\n";	*)(NONMONOTONE , NOTHING, NOTHING, XOR, true, var, c) in

		if crois2 = NONMONOTONE ||crois1 = NONMONOTONE then isExactForm := false;


		construireCondition crois1 bInf1  bSup1  oper1 mult1 v1 cd1 crois2  bInf2  bSup2  oper2 mult2 v2 cd2 lv avant dans cte t inst
	end
	else 
	begin (* Printf.printf"cas 2 traiterANDCOND exp1 is not Binary boolean ???\n";*)
		 	
		let lv1 =  (listeDesVarsDeExpSeules exp1) in
		let lv2 =  (listeDesVarsDeExpSeules exp2) in
		let (var1, suite1,var2, suite2 ) = if List.mem var  lv1  && List.mem var  lv2 then (var,liste,var,liste) else 
										   if (List.hd lv1) = var &&  (List.tl lv1) = [] then   (var,liste,List.hd liste, List.tl liste) else (List.hd liste, List.tl liste,List.hd liste, List.tl liste) in

		
		(*Printf.printf"cas 2 traiterANDCOND exp1 is not Binary boolean ??? %s %s\n" var1 var2;*)
		let (crois1,bInf1, bSup1, oper1,mult1,v1, c1)=
					match exp1 with
						BINARY (op, e1, e2) ->  
							rechercheConditionBinary (VARIABLE(var1))  var1 op e1 e2 suite1 avant dans cte t c lv l inst
						| VARIABLE name -> 
						rechercheConditionBinary (VARIABLE name) name NE (VARIABLE name) (CONSTANT (CONST_INT "0")) liste avant dans cte t c lv l inst
						| UNARY (op, exp) -> 
							(match op with 
								NOT ->  
									rechercheConditionBinary init var EQ exp (CONSTANT (CONST_INT "0"))  liste avant dans cte t c lv l inst
							 	|_-> 	(  NONMONOTONE , NOTHING, NOTHING, XOR, true, var , c) (*pas multiple voir pour les booleens*))
						|_-> 	(* Printf.printf"cas 2 traiterANDCOND exp1 is not Binary boolean ???\n";	*) 
								(  NONMONOTONE , NOTHING, NOTHING, XOR, true, var , c) in
		(*Printf.printf"cas 2 traiterANDCOND exp1 is not Binary boolean ??? v1 %s\n" v1;*)

		let (crois2, bInf2, bSup2, oper2,mult2,v2, c2) =
					match exp2 with
						BINARY (op, e1, e2) ->  rechercheConditionBinary (VARIABLE(var2))  var2 op e1 e2 suite2 avant dans cte t c lv l inst
						| VARIABLE name ->   
						rechercheConditionBinary (VARIABLE name) name NE (VARIABLE name) (CONSTANT (CONST_INT "0")) liste avant dans cte t c lv l inst
						| UNARY (op, exp) -> 
							(match op with 
								NOT ->  
									rechercheConditionBinary init var EQ exp (CONSTANT (CONST_INT "0")) liste avant dans cte t c lv l inst
							 	|_-> 	(  NONMONOTONE , NOTHING, NOTHING, XOR, true, var , c) (*pas multiple voir pour les booleens*))
						|_->  (* Printf.printf"cas 2 traiterANDCOND exp2 is not Binary boolean ???\n";	*)	
							(  NONMONOTONE , NOTHING, NOTHING, XOR, true, var, c) in
		(*Printf.printf"cas 2 traiterANDCOND exp1 is not Binary boolean ??? v2 %s\n" v2;*)


		if crois2 = NONMONOTONE ||crois1 = NONMONOTONE then isExactForm := false;
		if ( intersection (listeDesVarsDeExpSeules exp1)  l) = [] then
		begin
			isExactForm := false;
			(* cond ne dépend que de exp2*) (crois2, bInf2, bSup2, oper2,mult2,v2, c2)
		end
		else 
			if ( intersection (listeDesVarsDeExpSeules exp2)  l) = [] then 
			begin
				isExactForm := false;
				(* cond ne dépend que de exp1*)  (crois1,bInf1, bSup1, oper1,mult1,v1, c1)
			end
			else  construireCondition crois1 bInf1  bSup1  oper1 mult1 v1 c1 crois2  bInf2  bSup2  oper2 mult2 v2 c2 lv avant dans cte t inst
	end

(* dans un premier temps comparaison = operateur binaire *)	
and analyseCompFor  var init comp l avant dans cte t lv lvb inst=
	borne := NOTHING;
	match comp with
		NOTHING -> 	( ADD, NONMONOTONE,false, var)
		| UNARY (op, exp) -> 
				(match op with 
					NOT ->  analyseCompFor  var init (BINARY(EQ, exp,  CONSTANT (CONST_INT "0")))  l avant dans cte t lv lvb inst
				 	|_-> 	(ADD, NONMONOTONE,false, var) (*pas multiple voir pour les booleens*))

		| BINARY (op, exp1, exp2) ->
		   arrayShown := false;	 
		   let  (croissant,borneInf,borneSup,operateur,multiple,var,_)= 
				rechercheConditionBinary init var op exp1 exp2 l avant dans cte t comp lv lvb  inst in

			if multiple = false then
			begin
				if croissant = CROISSANT then
				begin
					borne:=borneSup; initialisation:=borneInf;  (operateur,	CROISSANT, false, var)  
				end
				else begin  borne:=borneInf; initialisation:=borneSup; (operateur,croissant, false, var)   end
			end		
			else 	( op, NONMONOTONE, true, var)  
		| VARIABLE name -> 
						analyseCompFor  var init (BINARY(NE, VARIABLE (name),  CONSTANT (CONST_INT "0")))  l avant dans cte t lv lvb inst;
		| _-> 	 ( ADD, NONMONOTONE,false, var) (*pas multiple meme chose que pour unary si booleen*)

and changeExpInto0 expToChange exp  =
	if exp = expToChange then CONSTANT (CONST_INT "0")
	else
	begin
		match exp with
			NOTHING -> exp
			| UNARY (op, e) ->UNARY (op,changeExpInto0 expToChange e)
			| BINARY (op, exp1, exp2) -> BINARY (op, changeExpInto0 expToChange exp1, changeExpInto0 expToChange exp2)
			| CAST (typ, exp) ->  CAST (typ, changeExpInto0 expToChange exp)
			| COMMA exps ->COMMA(List.map(fun e-> changeExpInto0 expToChange  e)exps)
			| CALL (exp, args) ->	CALL(changeExpInto0 expToChange exp, List.map(fun e-> changeExpInto0 expToChange  e) args)
			| _ ->exp
	end


and getNombreIt une conditionConstante typeBoucle  conditionI conditionMultiple appel typeopPlusouMUL infoVar var globales=
	(*Printf.printf "getnombre d'it valeur de la condition : %s\n" var;*)
	let varCond = match conditionI with VARIABLE(v)->v |_-> "NODEF" in
	(*print_expVA (EXP(conditionI)); new_line ();*)
	let affect = if (  conditionConstante) then  (  (*Printf.printf"cons cte";*) EXP(conditionI) )
			else 
				if (existeAffectationVarListe varCond appel) then ( (* Printf.printf"cons non cte 1";*) 
					applyStoreVA(rechercheAffectVDsListeAS  varCond appel)[] )
				else ( (* Printf.printf"cons non cte 2"; *) EXP(NOTHING)) in
 
	let const = calculer   affect !infoaffichNull  [](*appel*) 1 in
	(*Printf.printf "getnombre d'it valeur de la condition : %s\n" var; print_expTerm const; new_line ();*)

	let isExecutedV = (match const with Boolean(b)	->  if b = false then false  else true 
										|_->if estDefExp const then if estNul const then false else true else true) in	
	(*Printf.printf "getnombre d'it valeur de la condition : %s\n" var;*) (*print_expTerm const; new_line ();*)
	(*if isExecutedV  then Printf.printf "isexecuted \n" else Printf.printf "is not executed \n" ;Printf.printf "FIN...\n";*)
	(*let isConstructVar = if (String.length var > 4) then begin if (String.sub var  0 4) = "bIt-" then  true else   false end else false in*)
 
	if isExecutedV then
	begin

		if (conditionMultiple) then   EXP(NOTHING)
		else
		begin	
			let (valinc, op, sensinc) = analyseInc infoVar appel typeopPlusouMUL globales in
			(*Printf.printf "NON MULTIPLE\n";*)
			match sensinc with
			 NOVALID ->	Printf.printf "NON NOVALID\n"; EXP(NOTHING)
			| INCVIDE ->
				(match typeBoucle with
					"for" |"while"->
						(match const with (*estExecutee*)
							ConstInt(i) 	-> if (int_of_string  i) = 0  then EXP(CONSTANT (CONST_INT "0")) else	 EXP(NOTHING) 		 	
							|ConstFloat (f) -> 	if (float_of_string  f) = 0.0  then EXP(CONSTANT (CONST_INT "0")) else   EXP(NOTHING)
							|RConstFloat (f) -> 	if (  f) = 0.0  then EXP(CONSTANT (CONST_INT "0")) else   EXP(NOTHING)
							| _->		(*Printf.printf (" boucle for infinie\n");*)EXP(NOTHING))
					|"dowhile"->
						(match const with
							ConstInt(i) -> 	if (int_of_string  i) = 0  then EXP(CONSTANT (CONST_INT "1"))  else   EXP(NOTHING)
							|ConstFloat (f) -> 	if (float_of_string  f) = 0.0  then EXP(CONSTANT (CONST_INT "1"))   else EXP(NOTHING)
							|RConstFloat (f) -> 	if ( f) = 0.0  then EXP(CONSTANT (CONST_INT "1"))   else EXP(NOTHING)
							| _->				EXP(NOTHING))
					|_-> EXP(NOTHING))
			|_->			
				if conditionConstante || op = EQ then
				begin
					match typeBoucle with
					"for" |"while"->
						(match const with (*estExecutee*)
						ConstInt(i) 	-> if (int_of_string  i) = 0  then EXP(CONSTANT (CONST_INT "0"))
										   else	 if   op = EQ then   EXP(CONSTANT (CONST_INT "1"))  else EXP(NOTHING)   
						|ConstFloat (f) -> 	if (float_of_string  f) = 0.0  then EXP(CONSTANT (CONST_INT "0"))
											else  if  op = EQ then   EXP(CONSTANT (CONST_INT "1"))  else EXP(NOTHING)
						|RConstFloat (f) -> 	if (  f) = 0.0  then EXP(CONSTANT (CONST_INT "0"))
											else  if  op = EQ then   EXP(CONSTANT (CONST_INT "1"))  else EXP(NOTHING)
						| _->		(*Printf.printf (" boucle for infinie\n");*)EXP(NOTHING))
					|"dowhile"->
					(match const with
						ConstInt(i) -> 	if (int_of_string  i) = 0  then EXP(CONSTANT (CONST_INT "1"))
										  else if  op = EQ  then  EXP(CONSTANT (CONST_INT "2"))   else EXP(NOTHING)
						|ConstFloat (f) -> 	if (float_of_string  f) = 0.0  then EXP(CONSTANT (CONST_INT "1"))
											else if  op = EQ then   EXP(CONSTANT (CONST_INT "2"))   else EXP(NOTHING)
						|RConstFloat (f) -> 	if ( f) = 0.0  then EXP(CONSTANT (CONST_INT "1"))
											else if  op = EQ then   EXP(CONSTANT (CONST_INT "2"))   else EXP(NOTHING)
						| _->				EXP(NOTHING))
					|_-> EXP(NOTHING)
				end
				else 
				begin 
					let typeInc =  expressionType valinc  in
					let bie = expVaToExp (applyStoreVA (applyStoreVA
										(EXP ( remplacerValPar  "EPSILON" (CONSTANT (CONST_INT "1")) (infoVar.borneInf))) appel)globales)  in
					
					let borneinf =  if listeDesVarsDeExpSeules bie = [] 
									then calculer  (EXP ( bie)) !infoaffichNull  [] 1 else NOCOMP in
					let typeInf =  expressionType borneinf  in
					let bse = expVaToExp (applyStoreVA (applyStoreVA
										(EXP ( remplacerValPar  "EPSILON" (CONSTANT (CONST_INT "1")) (infoVar.borneSup))) appel)globales)   in
					let bornesup = if listeDesVarsDeExpSeules bse = [] then calculer  (EXP ( bse)) !infoaffichNull  [] 1 else NOCOMP in
					let typeSup = expressionType bornesup in 

				
					(*afficherListeAS appel; new_line();*)
 					let bs = applyStoreVA(applyStoreVA   (EXP ( infoVar.borneSup)) appel)globales in
					(*let bi = applyStoreVA(applyStoreVA   (EXP ( infoVar.borneInf)) appel)globales in*)
					let bu = applyStoreVA(applyStoreVA   (EXP ( une )) appel)globales in
					(*print_expVA bs; new_line();*)

					(*Printf.printf "getNombreIt recherche de affect : \n";
					print_expression infoVar.borneSup 0; space() ;flush() ;new_line(); flush();new_line(); 
					print_expression infoVar.borneInf 0; space() ;flush() ;new_line(); flush();new_line(); 
					 
					print_expression infoVar.increment 0; space() ;flush() ;new_line(); flush();new_line(); 
					print_expression  une 0; space() ;flush() ;new_line(); flush();new_line(); 
					Printf.printf "getNombreIt recherche de affect : \n";*)
					
					let expune= evalArrayTravel  bs  appel globales une bu in
					let isInt = if  ( typeInf = INTEGERV && typeSup  = INTEGERV && typeInc  = INTEGERV)   then true else false in

					if isInt then 	 (applyStoreVA(applyStoreVA   (EXP(  remplacerValPar  "EPSILON" !vEPSILONINT expune)) appel)globales)  	 
					(*if sensinc = NDEF || (op != NE) then  *)
					else	(applyStoreVA(applyStoreVA   (EXP( (*remplacerValPar  "EPSILON" valEPSILON*) expune)) appel)globales)

					
				end
		end
	end 
	else 
	begin
		match typeBoucle with
			"for" |"while"->  EXP(CONSTANT (CONST_INT "0") )
			|"dowhile"-> 	  EXP(CONSTANT (CONST_INT "1"))
			|_-> 	 EXP(NOTHING)
	end

and evalArrayTravel bs appel globales une bu =
let (rep, var, isvar,expression) = hasPtrArrayBoundCondition bs in
if rep = true then 
								begin
								
									if isvar then
									begin	
										let av = if (existeAffectationVarListe var appel) then 
													applyStoreVA(rechercheAffectVDsListeAS  var appel)globales 
												else rechercheAffectVDsListeAS  var globales in
				
										
										let newe = expVaToExp( av )  in
										let (tab1,lidx1, e1) =getArrayNameOfexp newe in
										if tab1 != "" then
										begin
											let nune = changeExpInto0 e1 (expVaToExp bu) in
											let size = getAssosArrayIDsize tab1 in
											let varName =  Printf.sprintf "%s_%s" "getvarTailleTabMax" var in
											(match size with 
												NOSIZE -> ((*nsup, ninf,*) nune)
												| SARRAY (v) ->
													let arraySize = (CONSTANT (CONST_INT (Printf.sprintf "%d" v) )) in
													remplacerValPar  varName arraySize  nune
												| MSARRAY (lsize) -> 
													let tsize = expressionEvalueeToExpression (prodListSize lsize) in
													remplacerValPar  varName tsize  nune)
										end
										else  une
									end
									else
									begin
										let newe = expVaToExp( applyStoreVA(applyStoreVA  (EXP(expression)) appel)globales)  in
										let (tab1,lidx1, e1) =getArrayNameOfexp newe in
										if tab1 != "" then
										begin
											let nune = changeExpInto0 e1 (expVaToExp bu) in
											let size = getAssosArrayIDsize tab1 in
											 
											(match size with 
												NOSIZE -> ((*nsup, ninf,*) nune)
												| SARRAY (v) ->
													let arraySize = (CONSTANT (CONST_INT (Printf.sprintf "%d" v) )) in
													((*remplacerValPar  varName arraySize  nsup, ninf,*)remplacergetvarTailleTabMaxFctPar  nune arraySize  )
												| MSARRAY (lsize) -> 
													let tsize = expressionEvalueeToExpression (prodListSize lsize) in
													remplacergetvarTailleTabMaxFctPar  nune tsize  )
										end
										
										else  ((*infoVar.borneSup, infoVar.borneInf,*) une)


									end
								end
								else ((*infoVar.borneSup, infoVar.borneInf,*) une)



let rec typeDefList typ name result =
if name != [] then 
begin
	
	let ((id, _, _, _), others) = (List.hd name, List.tl name) in (* Printf.printf "mane %s typeDefList\n " id;*)
	if  (List.mem_assoc id !listAssosIdTypeTypeDec)= false then 
		listAssosIdTypeTypeDec := List.append !listAssosIdTypeTypeDec [(id, newDecTypeTYPEDEFTYPE typ)]; 
	typeDefList typ others (List.append result [(id, typ)])
end; ()

let rec varDefList typ name isPtr=
(*Printf.printf "varDefList "; *)
if name=[] then ()
else
begin
	let ((id, pt, _, _), others) = (List.hd name, List.tl name) in
	if id != "" then 
	begin	
			let (isPtrIn, isProto) = if estProto pt =false then
			begin
				(*Printf.printf "is not proto\n";*)
				(isPtrType pt , false)
			end
			else begin (*Printf.printf "is proto\n";*) (false, true) end in
			(*if isPtr || isPtrIn then Printf.printf "varDefList %s is ptr \n" id else Printf.printf "varDefList %s is not ptr \n" id;*)

		if isProto = false then
		begin
			setAssosIDBasetype id typ;
			(*Printf.printf "varDefList id %s type :\n"id; printfBaseType (getBaseType (List.assoc id !listAssocIdType) );new_line();*)
		end;
		if isPtr || isPtrIn then  
			if existAssosPtrNameType  id = false then  setAssosPtrNameType  id typ
	end;
	varDefList typ others isPtr
end


(* analyse fichier pour boucle *)
let rec analyse_defsPB defs = List.iter	(fun def ->		analyse_defPB def)		defs; 

and analyse_defPB def =
	match def with
		FUNDEF (proto, body) ->		ajouteFonctionDansDocument proto body ;()
		| OLDFUNDEF (proto, (*decs*)_, body) ->	ajouteFonctionDansDocument proto body ;()
		| DECDEF n -> 		
			let (baseType, _, namelist) = n in
			if estProto baseType then  
				List.iter (fun (n, _ , _,_)-> ajouteNomDansListeNomFonction n baseType) namelist;
		()	
		| TYPEDEF (n, _)  -> 
				let (typ, _, names) =n in (*let base = get_base_type typi*)
				nonamedForTypeDef:=
					if names =[] then ""
					else
					begin
						let (id, _, _, _) = (List.hd names) in
						id
					end
				;
				(*Printf.printf "id name typedef %s\n " !nonamedForTypeDef;*)
				let baseT = (get_base_typeEPS typ) in
				typeDefList baseT names []  ;()	
		| ONLYTYPEDEF n -> 	(* Definition of lonely "struct", "union" or "enum". *)   (*get_name_group n ;*)()	

and  consRefstatement   stat =
	match stat with
	 COMPUTATION exp ->		consRefexpression  exp ;()
	| BLOCK (defs, stat) ->	 analyse_defsPB  defs ; if stat <> NOP then consRefstatement  stat ;()
	| SEQUENCE (s1, s2) ->			
		consRefstatement   s1; consRefstatement   s2;()											
	| IF (exp, s1, s2) -> consRefexpression   exp ;	  consRefstatement  s1; consRefstatement  s2;()			
	| WHILE (exp, stat) ->  	(*analyse_expression  exp ;rien condition sans effet de bord*)	
		idBoucle := !idBoucle +1;
		let (num, fic, numl) = (!idBoucle,!fileCour , !numLine) in
		consRefexpression   exp ;
		(*Printf.printf"Boucle %d fichier %s ligne %d \n" num, fic, numl;*)
		setAssosIdLoopRef num (fic , numl );																
		consRefstatement  stat;
		consRefexpression   exp ;()
	| DOWHILE (exp, stat) ->			
		idBoucle := !idBoucle +1;
		let (num, fic, numl) = (!idBoucle,!fileCour , !numLine) in
		(*Printf.printf"Boucle %d fichier %s ligne %d \n" num, fic, numl;*)
		setAssosIdLoopRef num (fic , numl );				
		consRefstatement  stat;
		consRefexpression   exp ;
		()
	| FOR (exp1, exp2, exp3, stat) ->
		idBoucle := !idBoucle +1;
		let (num, fic, numl) = (!idBoucle,!fileCour , !numLine) in
		consRefexpression  exp1;
		consRefexpression  exp2;	
		(*Printf.printf"Boucle %d fichier %s ligne %d \n" num, fic, numl;*)
		setAssosIdLoopRef num (fic , numl );															
		consRefstatement  stat;
		consRefexpression   exp3 ;
		consRefexpression  exp2;()		
	| RETURN (exp) ->	consRefexpression  exp ;()
	| SWITCH (exp, stat) ->			consRefexpression   exp ; consRefstatement    stat ;()
	| CASE (exp, stat) ->			consRefexpression   exp ;
									consRefstatement    stat ;()					
	| DEFAULT stat ->				consRefstatement    stat;()
	| LABEL ((*name*)_, stat) ->	consRefstatement    stat;()
	| STAT_LINE (stat, file, line) ->  fileCour := file; numLine := line; consRefstatement stat;()
	| _ ->			(*Printf.printf "DEFAUT STATEMENT\n";*)	()
	 

and  consRefexpression exp =
	 match exp with
	UNARY (_, e) ->   consRefexpression e;()
	| BINARY (_, exp1, exp2) ->  consRefexpression exp1 ; consRefexpression exp2;	()
	| QUESTION (exp1, exp2, exp3) -> consRefexpression exp1 ; consRefexpression exp2; consRefexpression exp3;()
	| CAST (_, e) 		 ->  consRefexpression e ; ()
	| CALL (e , args) 				->		List.iter (fun ep -> consRefexpression ep) args; idAppel := !idAppel+1;
				setAssosIdCallFunctionRef !idAppel (!fileCour , !numLine );
				(* Printf.printf "setAssosIdCallFunctionRef functiuon %s numAppel %d \n" (nomFonctionDeExp e) !idAppel;*) ()
	| COMMA e 				->    List.iter (fun ep -> consRefexpression ep) e; ()
	| MEMBEROF (e , _) 		
	| MEMBEROFPTR (e , _) 	->		consRefexpression e ; ()
	| GNU_BODY (decs, stat) ->  consRefstatement   (BLOCK (decs, stat));()
	| EXPR_SIZEOF e ->consRefexpression e;()
	| INDEX (e, _) ->consRefexpression e;()
	| EXPR_LINE (exp, file, line)-> fileCour := file; numLine := line; consRefexpression exp;()		
	| _->()


and ajouteFonctionDansDocument proto body =					
	let (_ , _ , fct )=proto in
	let (nom,_,_,_) =fct in
	let (_,_,name) = proto in	(*(typ, sto, name)*)		
	let (_, parametres, _, _) = name in		(*(id nom fonction, typ, attr, exp) *)
	let base = get_base_type parametres  in
	ajouteNomDansListeNomFonction nom base;
	let (num, _,_) = tupleNumNomFonctionDansListe nom in
	 
	let (decs, stat) = body in
	consRefstatement (BLOCK (decs, stat));
	let nouCorpsFonction = new_CorpsFonction    (BLOCK (decs, stat)) [] (*!laListeDesAppelsDsFctCourante *)in
	listeRes := []; 

	(*Printf.printf"ajouteFonctionDansDocument %s\n"nom;*)
	creerListeES proto ; 
	(*Printf.printf "liste des variables et leur type\n";
			List.iter (fun (id,typ) -> Printf.printf "VARIABLE %s " id ; Printf.printf "de type "; printfBaseType typ; new_line()) !listAssocIdType;
			Printf.printf "fin liste des variables et leur type\n";*)
 
	let nouInfoFonc = new_Infofonction  nom proto nouCorpsFonction [] !listeRes in	
	let nouListe = add_fonction ( num,  nouInfoFonc ) !doc.laListeDesFonctions in		
	doc := new_document !doc.laListeDesBoucles nouListe  !doc.laListeDesAssosBoucleBorne  !doc.laListeDesNids

let isEQoperator op=
match op with EQ|NE->true|_->false



 let traiterConditionBoucleFor t nom nbIt cond eng (*exp*) (*init*) inc var cte var2 listLoopVar avant dans lvb vcond inst =
(*Printf.printf "traiterConditionBoucleFor\n" ;*)
(*afficherLesAffectations inst;*)
	let listeV = listeDesVarsDeExpSeules cond in
	(*let listeV = listeDesVarsDeExpSeules init in*)
	listADD := [];listADDInc := [];
	
	expressionIncFor:= NOTHING;
	expressionDinitFor := VARIABLE(var);
	let (op,typev,multi,v) = analyseCompFor var (VARIABLE(var)) cond listLoopVar avant dans cte t var2 lvb inst in	

(* je pense que c'est ici si op est NE ou EQ qu'on va chercher*)
	let ( indirect,nv,nt, indirectafter,typevar,multiple,operateur)=

		if v != var2 then
		begin	
			expressionDinitFor :=  
				( let initialvar =expVaToExp(rechercheAffectVDsListeAS v avant) in 
				  if  initialvar  = NOTHING then   VARIABLE(v)   else initialvar );

			opEstPlus:= true;	
			let ((*isindirect,inc,var, before*)isindirect,inc,vari, before,isMultiInc) =  getLoopVarInc v (List.append inst !listADDInc) in
			(match  inc  with 
				NODEFINC -> 
					if isEQoperator op then
					begin
					  	(*Printf.printf "cas 3 EQ peut être booleen var %s\n" var;*)
						let (isAssignedOK, assign, isConditionnal, ltrue, lfalse, ifvar) = containBoolxAssignementBody var  inst inst in
						if isAssignedOK then 
							(	
								 
								(*expressionDinitFor := (VARIABLE(var));*)
								let (exp1, exp2) = match cond with   BINARY (op, exp1, exp2) -> (exp1, exp2)|_->(NOTHING, NOTHING) in
								let (croissant,borneInf,borneSup,o,m,varDep,nexp, inc,b) =
								getBooleanAssignementInc 
									assign isConditionnal ltrue lfalse  
									(VARIABLE(var)) var op exp1 exp2 listLoopVar avant dans cte t cond var2 lvb  inst ifvar in
							
								(* 	let initialvar =expVaToExp(rechercheAffectVDsListeAS varDep avant) in 
									if  initialvar  = NOTHING then   VARIABLE(varDep)   else initialvar );*)

								expressionIncFor := inc;
								
								(*Printf.printf "cas 3 EQ peut être booleen vari %s\n" vari;
								print_expression borneInf 0;flush(); new_line();space(); new_line();
								print_expression borneSup 0;flush(); new_line();space(); new_line();
								Printf.printf "cas 3 EQ peut être booleen ifvar %s\n" ifvar;*)
								(*Printf.printf "cas 3 EQ peut être booleen var2 %s\n" var2;*)

								print_expression inc 0;flush(); new_line();space(); new_line();
								(*if before then Printf.printf "before\n" else Printf.printf "after\n";*)
								(true,		varDep	,"dowhile", b = false, croissant, m, op)
							)
						else  (false, v, t, false,typev,multi,op)
					end
					else (false, v, t, false,typev,multi,op)
				|_-> expressionIncFor := getIncValue inc ;
					if isMultiInc then isExactForm := false;
					if isindirect then 
					begin 
						(*if before then Printf.printf "before\n" else Printf.printf "after\n";*)

						expressionDinitFor :=  
							( 	let initialvar =expVaToExp(rechercheAffectVDsListeAS vari avant) in 
								if  initialvar  = NOTHING then   VARIABLE(vari)   else initialvar );
						initialisation := !expressionDinitFor;
						(true, vari, "dowhile", before = false,typev,multi,op) 
					end
					else (false, v, t, false,typev,multi,op))
		end
		else
		begin
			expressionDinitFor :=  (CONSTANT (CONST_INT "0"));
			opEstPlus:= true;	
			expressionIncFor:=CONSTANT (CONST_INT "1");
			(false, v, t, false,typev,multi,op)
		end in

	let (sup, inf, inc) = 
	if indirect && !opEstPlus = false && (isDivInc !expressionIncFor) then 
		(!initialisation, !borne,  BINARY (DIV, CONSTANT  (CONST_INT "1"), !expressionIncFor)) 
	else	if !opEstPlus = false && (isDivInc !expressionIncFor)  && typevar = DECROISSANT then 
	(!initialisation,!borne, BINARY (DIV, CONSTANT  (CONST_INT "1"), !expressionIncFor)) 
		 	else
				if !opEstPlus && typevar = DECROISSANT then  (!borne,!initialisation, !expressionIncFor)  
		 		else  (!borne,!initialisation,!expressionIncFor) in

	expressionIncFor := inc;
	
	let isConstructVar = if (String.length nv > 4) then begin if (String.sub nv  0 4) = "bIt-" then  true else   false end else false in
	let isIntVar = 	if isConstructVar = false &&  List.mem_assoc nv !listAssocIdType then   
		( match getBaseType (List.assoc nv !listAssocIdType) with INT_TYPE-> true|_-> false) else  false in


	let ( ninf ,nsup) =
	if  isIntVar then
	begin
		expressionDinitFor := remplacerValPar  "EPSILON" !vEPSILONINT !expressionDinitFor;
		( remplacerValPar  "EPSILON" !vEPSILONINT  inf,   remplacerValPar  "EPSILON" !vEPSILONINT  sup)
    end
	else ( inf, sup) in


	borne := nsup; 
	initialisation := ninf;


	(*Printf.printf "\n\ntraiterConditionBoucleFor  2\n" ;*)
	let typeopPlusouMUL =  !opEstPlus	in
	(*if !expressionDinitFor = NOTHING then expressionDinitFor := VARIABLE(nv);*)
	let infoVar =   new_variation ninf nsup inc typevar  operateur indirectafter in
	let nc = if (typevar=CONSTANTE||cte) then cond else vcond in
	let nb = expVaToExp (getNombreIt nsup (typevar=CONSTANTE||cte) t nc multiple [] typeopPlusouMUL  infoVar nv []) in
	listeBoucleOuAppelCourante := reecrireCAll var2 !listeBoucleOuAppelCourante;
	 

	let info = (new_boucleInfo t nom listeV nbIt eng (typevar=CONSTANTE||cte) nc multiple !listeBoucleOuAppelCourante 
				( new_variation !expressionDinitFor nb inc typevar operateur indirectafter) typeopPlusouMUL) in
	
	let boucleFor = new_boucleFor  info  listeV  var2  ninf  nb inc  in
	let nouvBoucle = new_bouclef boucleFor in
    let borne = (getBorneBoucleFor t boucleFor.n boucleFor.valInit.valeur boucleFor.c typeopPlusouMUL indirectafter) in
	if !isExactForm && ((getIsMultipleIncrement !expressionIncFor) =false) then setAssosExactLoopInit  nom borne;
	doc := 	new_document 
				(new_ListeDesBoucles !doc.laListeDesBoucles  [nouvBoucle]) 
				!doc.laListeDesFonctions
				(new_ListeDesBoucles !doc.laListeDesAssosBoucleBorne [new_infoBorneDeBoucle nouvBoucle  borne [] 
				(!isExactForm  && ((getIsMultipleIncrement !expressionIncFor) =false))])
				!doc.laListeDesNids;(*isExactForm*)
	(borne, indirect)

and traiterConditionBoucle t nom nbIt cond eng  var cte (*inc typeopPlusouMUL*) var2 listLoopVar avant dans lvb vcond inst =
	(*Printf.printf "\n\ntraiterConditionBoucleFor  analyseCompFor\n" ;*)

	listADD := [];listADDInc := [];
 	let (op, typev,multi,v) = analyseCompFor    var  (VARIABLE(var)) cond listLoopVar  avant dans cte t var2 lvb inst in
	let liste = listeDesVarsDeExpSeules  cond in
	expressionIncFor:= NOTHING;
	(*Printf.printf "\n\ntraiterConditionBoucleFor  analyseCompFor\n" ;*)
	let ( indirect,nv,nt, indirectafter,typevar,multiple,operateur)=

		if v != var2 then
		begin	
			expressionDinitFor :=  
				( let initialvar =expVaToExp(rechercheAffectVDsListeAS v avant) in 
				  if  initialvar  = NOTHING then   VARIABLE(v)   else initialvar );

			opEstPlus:= true;	
			let (isindirect,inc,var, before,isMultiInc) =  getLoopVarInc v (List.append inst !listADDInc) in
			(match  inc  with 
				NODEFINC -> (*Printf.printf "NODEFINC\n";*)
					if isEQoperator op then
					begin
						(*Printf.printf "cas 3 EQ peut être booleen\n";*)
						let (isAssignedOK, assign, isConditionnal, ltrue, lfalse, ifvar) = containBoolxAssignementBody var  inst inst in
						if isAssignedOK then 
							(    
								let (exp1, exp2) = match cond with   BINARY (op, exp1, exp2) -> (exp1, exp2)|_->(NOTHING, NOTHING) in
								let (croissant,borneInf,borneSup,o,multiple,varDep,nexp, inc,b) =
								getBooleanAssignementInc 
									assign isConditionnal ltrue lfalse  
									(VARIABLE(var)) var op exp1 exp2 listLoopVar avant dans cte t cond var2 lvb  inst ifvar in
							    (*expressionDinitFor :=  
								( 	let initialvar =expVaToExp(rechercheAffectVDsListeAS varDep avant) in 
									if  initialvar  = NOTHING then   VARIABLE(varDep)   else initialvar );*)
								
								(*Printf.printf "while... être booleen\n";
								print_expression borneInf 0;flush(); new_line();space(); new_line();
								print_expression borneSup 0;flush(); new_line();space(); new_line();
								print_expression inc 0;flush(); new_line();space(); new_line();*)
								(*Printf.printf "while... être booleen\n";*)
								expressionIncFor := inc;
								(*if before then Printf.printf "before\n" else Printf.printf "after\n";*)
								(true,		varDep	,"dowhile", b = false, croissant, multiple, op)
							)
						else  (false, v, t, false,typev,multi,op)
					end
					else (false, v, t, false,typev,multi,op)
				|_->
					(*Printf.printf "OTHER NODEF\n";*)
					expressionIncFor := getIncValue inc ;
					if isMultiInc then isExactForm := false;
					if isindirect then 
					begin 
						expressionDinitFor :=  
							( 	let initialvar =expVaToExp(rechercheAffectVDsListeAS var avant) in 
								if  initialvar  = NOTHING then   VARIABLE(var)   else initialvar );
						initialisation := !expressionDinitFor;
						(true, var, "dowhile", before = false,typev,multi,op) 
					end
					else (false, v, t, false,typev,multi,op))
		end
		else
		begin
			expressionDinitFor :=  (CONSTANT (CONST_INT "0"));
			opEstPlus:= true;	
			expressionIncFor:=CONSTANT (CONST_INT "1");
			(false, v, t, false,typev,multi,op)
		end in

	
	let (sup, inf, inc) = 
	if indirect && !opEstPlus = false && (isDivInc !expressionIncFor) then 
		(!initialisation, !borne,  BINARY (DIV, CONSTANT  (CONST_INT "1"), !expressionIncFor)) 
	else	if !opEstPlus = false && (isDivInc !expressionIncFor)  && typevar = DECROISSANT then 
		(!initialisation,!borne, BINARY (DIV, CONSTANT  (CONST_INT "1"), !expressionIncFor)) 
		 	else
				if !opEstPlus && typevar = DECROISSANT then  (!borne,!initialisation, !expressionIncFor)  
		 		else  (!borne,!initialisation,!expressionIncFor) in
	 
	 
	expressionIncFor := inc;
(*Printf.printf "cas 4 EQ peut être booleen vari \n" ;

								print_expression inc 0;flush(); new_line();space(); new_line();
								print_expression sup 0;flush(); new_line();space(); new_line();*)

	let isConstructVar = if (String.length nv > 4) then begin if (String.sub nv  0 4) = "bIt-" then  true else   false end else false in
	let isIntVar = 	if isConstructVar = false &&  List.mem_assoc nv !listAssocIdType then   ( match getBaseType (List.assoc nv !listAssocIdType) with INT_TYPE-> true|_-> false) else  false in


	let ( ninf ,nsup) =
	if  isIntVar then
	begin
		
		( remplacerValPar  "EPSILON" !vEPSILONINT  inf,  remplacerValPar  "EPSILON" !vEPSILONINT sup)
    end
	else ( inf, sup) in


	borne := nsup; 
	initialisation := ninf;

	(*Printf.printf "\n\ntraiterConditionBoucleFor  2\n" ;*)
 	let infoVar =   new_variation ninf nsup inc typevar  operateur indirectafter in
	let nc = if (typevar=CONSTANTE||cte) then cond else vcond in
	let nb = expVaToExp (getNombreIt nsup (typevar=CONSTANTE||cte) t nc multiple [] !opEstPlus   infoVar v []) in
	listeBoucleOuAppelCourante := reecrireCAll var2 !listeBoucleOuAppelCourante;
   
	let b = new_boucleWhileOuDoWhile 
				(new_boucleInfo t nom liste nbIt eng (typevar=CONSTANTE||cte)  nc  multiple !listeBoucleOuAppelCourante
				(new_variation (VARIABLE(nv)) nb inc typevar operateur indirectafter) !opEstPlus ) [] []  in
	let ba = (new_boucleA b )  in	
	let borne = (getBorneBoucleFor t nb ninf inc !opEstPlus indirectafter) in
	if (!isExactForm && ((getIsMultipleIncrement !expressionIncFor) =false)) then setAssosExactLoopInit  nom borne;
	doc := new_document 	(new_ListeDesBoucles !doc.laListeDesBoucles  [ba])  !doc.laListeDesFonctions
							(new_ListeDesBoucles !doc.laListeDesAssosBoucleBorne
								[ new_infoBorneDeBoucle ba borne [] (!isExactForm &&( (getIsMultipleIncrement !expressionIncFor) =false))] )		
							!doc.laListeDesNids;
(borne, indirect)
													
																			
let rec majABB traitee listeATraiter id listeI =
	if listeATraiter = []	then 	(traitee)
	else		
		let elt = (List.hd listeATraiter) in
		 if (id = (getBoucleIdB elt.laBoucle)) then 
		(* on a trouve l'élément à modifier la nouvelle liste est composée du début déja traite
		du nouvel element de la fin de la liste*)
			List.append 
				(List.append  traitee [new_infoBorneDeBoucle  elt.laBoucle elt.expressionBorne listeI elt.isExactExp]) 
					(List.tl listeATraiter)
		else
			majABB 	(List.append traitee [new_infoBorneDeBoucle  elt.laBoucle elt.expressionBorne elt.lesAffectationsB elt.isExactExp] )
						(List.tl listeATraiter)  id listeI			
								
let rec extraireListeSousBoucle  listeTriplet =
if listeTriplet = [] then []	
else
begin
	let (tete,_,_) = List.hd listeTriplet in
	let queue = List.tl listeTriplet in
	if (queue = [])	then tete 		
	else  List.append tete (extraireListeSousBoucle 	queue	)
end
	
let eval listeInst saufId idEng=
	let listeInter = 
		List.filter 
		(fun e -> 
			match e with
			VAR ( _, _)|TAB ( _, _, _)|MEMASSIGN(_,_,_)|IFVF ( _, _, _)| IFV ( _, _) | BEGIN (_)-> true			
			| FORV ( num, _, _, _, _, _, _) -> 	num != saufId						
			| APPEL (_,_, _, _,_,_,_) ->true
		) listeInst in	 
	evalStore   (new_instBEGIN (listeInter)) [] []
	
			
let rec relierAux num 	varDeBoucle listeTraitee listeAtraiter listeDesFils=	
	if (listeAtraiter = []) then 	
	begin 
		if !vDEBUG then Printf.printf "relierAux :aucun suivant à traiter dans nid %d \n" num ;
	end
	else
	begin
		let n = List.hd listeAtraiter in
		let suite = List.tl listeAtraiter in	
		if !vDEBUG 
			then Printf.printf "relierAux :des suivants à traiter dans nid %d \n" num		;	
		(* recherche des boucles sous moi*)
		
		let idTeteSousNid = (getBoucleInfoB(n.infoNid.laBoucle)).identifiant	in
		(* se sont tous ceux de la liste qui sont dans la pile *)
		if !vDEBUG then 
		begin
			Printf.printf "relierAux :du suivant %d à traiter dans nid %d\n" idTeteSousNid num;	
			Printf.printf "num eng %d num courant%d\n"
				(getBoucleInfoB(n.infoNid.laBoucle)).nomEnglobante	 num
		end;
		(*if (List.mem idTeteSousNid listeDesFils) then*)
		if (getBoucleInfoB(n.infoNid.laBoucle)).nomEnglobante	= num then
		begin (* n est imbriqué sous num*)
			if !vDEBUG then Printf.printf "n imbrique sous num relierAux :à %d  fils  %d\n" idTeteSousNid num;	
			let listeAux = (extraireListeSousBoucle n.listeTripletNid) in
			let _ =eval !listeDesInstCourantes 	idTeteSousNid num in
			
			let listeDesAffectationsSansNoeudCourant = !listeASCourant	in
																										
			listeTripletNidCourant :=
				List.append [(List.append [idTeteSousNid] listeAux), listeDesAffectationsSansNoeudCourant, n] 
							!listeTripletNidCourant	;									
			relierAux num 	varDeBoucle listeTraitee suite listeDesFils				
		end								
		else (* se sont des noeuds de même niveau d'imbrication *)
		begin
			if !vDEBUG then  Printf.printf "relierAux:pas fils nid %d %d\n" num		idTeteSousNid;	
				(*listeTraitee = ( List.append [n] listeTraitee)	;ERREUR A290*)
				relierAux num varDeBoucle (List.append [n] listeTraitee) suite listeDesFils		;
				listeNoeudCourant	:=	( List.append  [n] !listeNoeudCourant )
		end;
	end
										
let 	relierLesNoeudsEnglobesAuNoeudCourant num varDeBoucle listeNC listeBouclesImbriquees cond =
		let listeRes = [] in 
		listeTripletNidCourantPred := !listeTripletNidCourant;
		listeTripletNidCourant := [];	
		if !vDEBUG then Printf.printf "DANS RELIER APPEL A RELIER AUX\n";
		listeNoeudCourant := [];
		relierAux num 	varDeBoucle listeRes listeNC listeBouclesImbriquees ;
		noeudCourant := new_NidDeBoucle  cond	(rechercheAssosBoucleBorne num)  varDeBoucle !listeDesInstCourantes !listeTripletNidCourant ;
		listeTripletNidCourant := !listeTripletNidCourantPred
		
let estGlobale = ref true	
let nouvExp = ref NOTHING
let listeNextExp = ref []

let rec hasMultiOuputInst stat =
	match stat with
	NOP ->false
	| COMPUTATION exp ->hasMultiOuputExp  exp
	| BLOCK (_, stat) | SWITCH (_, stat) | CASE (_, stat) | DEFAULT stat | LABEL (_, stat)| STAT_LINE (stat, _, _) ->hasMultiOuputInst stat
	| SEQUENCE (s1, s2) ->hasMultiOuputInst s1 || hasMultiOuputInst s2
	| IF (exp, s1, s2) ->hasMultiOuputExp  exp ||hasMultiOuputInst s1 || hasMultiOuputInst s2
	| WHILE (e, stat) | DOWHILE (e, stat)->hasMultiOuputExp  e ||hasMultiOuputInst stat
	| FOR (exp1, exp2, exp3, stat) -> hasMultiOuputExp  exp1 || hasMultiOuputExp  exp2 ||hasMultiOuputExp  exp3 ||hasMultiOuputInst stat
	| BREAK | CONTINUE | RETURN _| GOTO _  | ASM _ | GNU_ASM (_, _, _, _)->true

and hasMultiOuputExp exp =
	match exp with
		NOTHING -> false
		| UNARY (_, e) | CAST (_, e) | EXPR_SIZEOF e | MEMBEROF (e, _) 	| MEMBEROFPTR (e, _) | EXPR_LINE (e, _, _) ->hasMultiOuputExp e
		| BINARY (_, exp1, exp2) | INDEX (exp1, exp2)-> hasMultiOuputExp exp1 || hasMultiOuputExp exp2
		| QUESTION (exp1, exp2, exp3) ->hasMultiOuputExp exp1 || hasMultiOuputExp exp2 || hasMultiOuputExp exp3
		| CALL (_, _) ->false
		| COMMA exps -> if exps = [] then false else  (hasMultiOuputExp (List.hd exps)) ||( hasMultiOuputExp (COMMA ( List.tl exps)))
		| CONSTANT _ | VARIABLE _ | TYPE_SIZEOF _ -> false		
		| GNU_BODY (_, stat) ->hasMultiOuputInst stat

let isFindCase =ref false
let listOfCase = ref []
let listOfDefault = ref NOP

let rec analyseCase stat listeCond vtest  =
	match stat with
		CASE (exp, s) ->			
			let new_cond = analyseCase s [] vtest  in
			if new_cond = [] then
				  [BINARY(EQ, VARIABLE(vtest), exp)]
			else 	[BINARY(OR, BINARY(EQ, VARIABLE(vtest), exp), List.hd new_cond)]					
	| _ ->	listeCond


(*let isFindCase = ref false
let isFindCaseEnd = ref false
let rec listeCasestatbreak  stat prev=
	match stat with
	| BREAK  -> 			isFindCaseEnd := true; prev		
	| SEQUENCE (s1, s2) ->	let res = listeCasestatbreak  s1 prev in
							if !isFindCaseEnd then res else listeCasestatbreak  s2 res			
	| _ -> 	List.append prev [stat]


let rec listeCasestatbegin   case stat =
	match stat with
	| SEQUENCE (s1, s2) ->	let res = listeCasestatbegin   case s1 in
							if !isFindCase then List.append	res [s2] else   listeCasestatbegin   case s2 			
	| CASE (exp, stat) ->	if exp = case then 	
							begin isFindCase := true 	; [stat] end 
							else []
	| _ -> 	[]*)


let listeCasestatbegin  case statL boolean=
List.filter 
(fun stat ->  
	match stat with
		  CASE (exp, _) ->	if boolean then false else begin if exp = case then begin isFindCase := true 	;	true end else false end
		| DEFAULT st		->	if boolean then true else   !isFindCase 
		| BREAK  -> 			isFindCase := false; false		
		| _ ->					!isFindCase		
)statL


let rec listeSwitchStatement  stat =
	match stat with
	| SEQUENCE (s1, s2) ->	 List.append	(listeSwitchStatement s1) (listeSwitchStatement s2)
	| _ -> 	[stat]

let rec listeSwitchStatementToSeq  stat =
if stat = [] then NOP
else  SEQUENCE (List.hd stat, listeSwitchStatementToSeq (List.tl stat)) 

let rec analyseSwitchStatement stat vtest listestat=
(*print_statement stat;*)
	match stat with
	 BLOCK (defs, stat) ->				analyseSwitchStatement stat vtest listestat;()
	| SEQUENCE (s1, s2) ->	
		analyseSwitchStatement   s1 vtest listestat;
		analyseSwitchStatement    s2 vtest listestat;Printf.printf "sequence\n"; (*print_statement s1;print_statement s2;*)()
	| CASE (e, cs) ->													
									isFindCase := false;
									let nl = listeCasestatbegin  e listestat false in
									let new_cond = analyseCase stat [] vtest  in
									if new_cond != [] then listOfCase:= List.append  !listOfCase [(List.hd new_cond,   nl )];()
	| DEFAULT stat ->				isFindCase := false;
									let listedefault = listeCasestatbegin  NOTHING listestat true in
									
									listOfDefault :=  if listedefault = [] then NOP else List.hd listedefault; ()		
	|_ ->	()


let rec buildSwitchStatement listCase listDefault =
if listCase <> [] then
begin
	let ((test,stat), suite) = (List.hd listCase, List.tl listCase) in
	 
	if suite = [] then IF (test, (listeSwitchStatementToSeq stat), listDefault) 
	else IF (test, (listeSwitchStatementToSeq stat), (buildSwitchStatement suite listDefault ))
end
else listDefault


let numArg = ref 0
let rec analyse_statement   stat =
	match stat with
	NOP -> 						()
	| COMPUTATION exp ->		analyse_expression  exp 
	| BLOCK (defs, stat) ->			
		let listePred = !listeDesInstCourantes in	
		listeDesInstCourantes := [];
		analyse_defs  defs ;
		if stat <> NOP then analyse_statement  stat ;
		listeDesInstCourantes :=  List.append listePred  !listeDesInstCourantes 

	| SEQUENCE (s1, s2) ->			
		let listePred = !listeDesInstCourantes in	
		listeDesInstCourantes := [];
		analyse_statement   s1;
		let listePred2 = List.append listePred  !listeDesInstCourantes in		
		listeDesInstCourantes := [];
		analyse_statement   s2;
		listeDesInstCourantes :=List.append listePred2  !listeDesInstCourantes 
											
	| IF (exp, s1, s2) ->			
		(*ICI IDIF (var,instthen, treethen,insteles, treeelse,lt,lf)*)
		let trueListPred = !trueList in
		let falseListPred = !falseList in
		idIf := !idIf + 1;
		analyse_expression   exp ;
		let ne = !nouvExp in   
		let varIfN =  Printf.sprintf "%s-%d" "IF" !idIf  in	 
		let newaffect =new_instVar  varIfN  (EXP(ne)) in 

		listeDesInstCourantes := List.append !listeDesInstCourantes  [newaffect]; 
		let listePred = !listeDesInstCourantes in	


		let maListeDesBoucleOuAppelPred = 	!listeBoucleOuAppelCourante		in
		listeBoucleOuAppelCourante := [];

		listeDesInstCourantes := [];
		trueList := List.append !trueList [varIfN];
		analyse_statement  s1;

		let listeThen = !listeDesInstCourantes in
(*Printf.printf"analyse statement if\n";
afficherLesAffectations !listeDesInstCourantes;*)
		let bouavrai = !listeBoucleOuAppelCourante in
		trueList := trueListPred ;
  		let (instthen,treethen, instelse,treeelse) =
				if (s2 = NOP)	then 
				begin
					listeDesInstCourantes :=  List.append listePred  [ new_instIFV (EXP(VARIABLE(varIfN))) (new_instBEGIN (listeThen)) ];
					(listeThen,bouavrai,[],[])
				end
				else 	
				begin					 
					listeBoucleOuAppelCourante := [];
					listeDesInstCourantes := [];
					falseList := List.append !falseList [varIfN];
					analyse_statement  s2;			
					let listeElse = !listeDesInstCourantes in

(*Printf.printf"analyse statement else\n";
afficherLesAffectations !listeDesInstCourantes;
print_statement  s2 ;*)
										
					listeDesInstCourantes := 
						List.append  listePred  [new_instIFVF (EXP(VARIABLE(varIfN))) (new_instBEGIN (listeThen))  (new_instBEGIN (listeElse)) ];
					falseList := falseListPred;
					(listeThen,bouavrai,listeElse,!listeBoucleOuAppelCourante)
				end in	

		listeBoucleOuAppelCourante	:= 
			List.append  maListeDesBoucleOuAppelPred   [IDIF(varIfN , instthen,treethen, instelse,treeelse,trueListPred,falseListPred)]
												
	| WHILE (exp, stat) ->  	(*analyse_expression  exp ;rien condition sans effet de bord*)	

	    let degPred = !nbImbrications in 
		nbImbrications := !nbImbrications + 1;
		let deg = !nbImbrications in 
		if !nbImbrications >= !nbImbricationsMaxAppli then nbImbricationsMaxAppli := !nbImbrications;

		listeNextExp := [];
		aUneFctNotDEf := false;
		(*analyse_expressionaux exp ;*)
		analyse_expressionaux   exp ;
		let ne = !nouvExp in   
		idBoucle := !idBoucle +1;
		let numBoucle = !idBoucle in	

		let idBoucleEngPred = !idBoucleEng in	
		idBoucleEng := numBoucle;

		let varIfN =  Printf.sprintf "%s-%d" "TWH" numBoucle  in	 
		let newaffect =new_instVar  varIfN  (EXP(ne)) in 
		listeDesInstCourantes := List.append !listeDesInstCourantes  [newaffect]; 


		let varBoucleIfN =  Printf.sprintf "%s-%d" "bIt" !idBoucle in	
		listAssocIdType := List.append !listAssocIdType [(varBoucleIfN, INT_TYPE)] ;
		let listePred = !listeDesInstCourantes in
		listeDesInstCourantes := !listeNextExp;		
		let (fic,lig)=getAssosIdLoopRef numBoucle in															
		listeBoucleOuAppelCourante	:= List.append  !listeBoucleOuAppelCourante   [IDBOUCLE(numBoucle, !trueList,!falseList ,fic ,lig)];	
		let maListeDesBoucleOuAppelPred = 	!listeBoucleOuAppelCourante		in

		listeBoucleOuAppelCourante := [];
								
		let listeBouclesInbriqueesPred = !listeDesBouclesDuNidCourant in
		listeDesBouclesDuNidCourant := List.append  !listeDesBouclesDuNidCourant [numBoucle];			
		listeBouclesImbriquees := [];
					
		analyse_statement  stat;
		listeNextExp := [];
		(*analyse_expressionaux exp ;*)
		analyse_expressionaux   exp ;

		idBoucleEng := idBoucleEngPred;
		let lesInstDeLaBoucle = !listeDesInstCourantes in
		idBoucleEng := idBoucleEngPred;

			let li = if !aUneFctNotDEf = true then 
			begin 
				(*Printf.printf "traitement particulier boucle\n";*)
				let (ida,nbi,idb,id_if) = (!idAppel,!nbImbrications , !idBoucle,!idIf) in	
				let maListeDesBoucleOuAppelPredP = !listeBoucleOuAppelCourante in
				listeDesInstCourantes := []; onlyAexpression   exp ; onlyAstatement stat;onlyAexpression   exp ;
				idAppel := ida; nbImbrications :=nbi;idBoucle:=idb;idIf:=id_if;
				(*Printf.printf "traitement particulier boucle FIN\n";  *)
				listeBoucleOuAppelCourante := 	maListeDesBoucleOuAppelPredP;				
				!listeDesInstCourantes
			end 
			else !listeDesInstCourantes in

		listeDesInstCourantes := lesInstDeLaBoucle;
		let listeVCond =  listeDesVarsDeExpSeules  exp in  
		let na = extractVarCONDAffect  li listeVCond in
		let asna = evalStore (new_instBEGIN (na)) [] [] in

		let listeVDeBoucle =  	rechercheListeDesVarDeBoucle  listeVCond 	asna in
		let (varDeB, constante, lVB) =
			(if listeVDeBoucle = [] then (varBoucleIfN, true, [])
			else
				if (List.tl listeVDeBoucle) = [] then  (List.hd listeVDeBoucle, false, []) (*la boucle ne depend que d'1 variable on peut traiter*)	
				else (varBoucleIfN, false, listeVDeBoucle))in
		(*afficherLesAffectations na;*)

		let listeASC = evalStore (new_instBEGIN (listePred)) [] [] in
		isExactForm := (hasMultiOuputInst stat = false) && (!trueList = []) && (!falseList = []);
		(*Printf.printf "\n\nAnalyse statement : la boucle %d   \n" numBoucle;

afficherLesAffectations (  lesInstDeLaBoucle) ;new_line () ;*)
(*Printf.printf "\n\nAnalyse statement : la boucle %d   \n" numBoucle;
if !isExactForm then Printf.printf "exact\n" else Printf.printf "non exact\n" ;*)
		let (nb, addtest) = traiterConditionBoucle "while" numBoucle deg ne(*exp*) idBoucleEngPred  varDeB constante varBoucleIfN lVB listeASC  asna (*aS*) listeVDeBoucle (VARIABLE(varIfN)) na in
(*Printf.printf "\n\nAnalyse statement : la boucle %d   ap\n" numBoucle;*)

		listeDesInstCourantes := 
				[	new_instFOR numBoucle varBoucleIfN	(EXP(NOTHING)) (EXP(ne(*exp*))) (EXP(NOTHING))
								 (EXP( nb)) (new_instBEGIN (lesInstDeLaBoucle ))];
																										
		let res = majABB []	!doc.laListeDesAssosBoucleBorne 	numBoucle !listeDesInstCourantes in
		if !vDEBUG then  Printf.printf "\n\nAnalyse statement : noeud traité : %d varDEBOUCLE %s \n\n "  numBoucle varBoucleIfN;
		if (!listeBouclesImbriquees = []) then 	(*  test ne contient pas de boucle *)
		begin
			if !vDEBUG then  	Printf.printf "\n\nAnalyse statement : la boucle %d ne contient pas de boucle \n" numBoucle;
			noeudCourant :=(new_NidDeBoucle ne(*exp*)  (rechercheAssosBoucleBorne numBoucle) varBoucleIfN  (*lesInst*)!listeDesInstCourantes []) 	
		end
		else 
		begin
			if !vDEBUG then Printf.printf "\nAnalyse statement : la boucle %d contient boucles appel relierLesNoeudsEnglobesAuNoeudCourant\n" numBoucle;
			(* attention on peut avoir X sous noeuds et donc 1 liste de noeuds et pas un seul*)
			relierLesNoeudsEnglobesAuNoeudCourant 	numBoucle varBoucleIfN !listeNoeudCourant !listeBouclesImbriquees exp
		end;									
		(* si la boucle est au départ d'un noeud*)
		 
		if (idBoucleEngPred = 0) then
		begin
			doc := 	new_document !doc.laListeDesBoucles !doc.laListeDesFonctions 	res	 (List.append [!noeudCourant] !doc.laListeDesNids);
			listeTripletNidCourantPred := [];
			listeDesBouclesDuNidCourant := [];
			listeNoeudCourant := []
		end 
		else
		begin
			listeNoeudCourant := List.append 	[!noeudCourant] !listeNoeudCourant ;
			doc := 	new_document !doc.laListeDesBoucles !doc.laListeDesFonctions 	res	   (List.append [!noeudCourant] !doc.laListeDesNids)
		end;
		listeBouclesImbriquees :=  List.append [numBoucle] !listeBouclesImbriquees;
		listeBouclesImbriquees :=  List.append listeBouclesInbriqueesPred !listeBouclesImbriquees ;
		listeDesInstCourantes :=  List.append( List.append listePred (List.append !listADD !listeDesInstCourantes)) !listeNextExp;
		nbImbrications := degPred; 		
		listeBoucleOuAppelCourante :=  maListeDesBoucleOuAppelPred 
									
	| DOWHILE (exp, stat) ->		
   		let degPred = !nbImbrications in 
		 
		nbImbrications := !nbImbrications + 1;
		let deg = !nbImbrications in  
		if !nbImbrications >= !nbImbricationsMaxAppli then nbImbricationsMaxAppli := !nbImbrications;
	(*	analyse_expression   exp ;*)
		idBoucle := !idBoucle +1;
		let numBoucle = !idBoucle in
		let varBoucleIfN =  Printf.sprintf "%s-%d" "bIt" !idBoucle in	
		let listePred = !listeDesInstCourantes in
		listeDesInstCourantes := [];
		listAssocIdType := List.append !listAssocIdType [(varBoucleIfN, INT_TYPE)] ;
		let (fic,lig)=getAssosIdLoopRef numBoucle in												
		listeBoucleOuAppelCourante	:= List.append !listeBoucleOuAppelCourante  [IDBOUCLE(numBoucle, !trueList,!falseList, fic,lig)];
		let listeBouclesInbriqueesPred  = !listeDesBouclesDuNidCourant in					
		listeDesBouclesDuNidCourant := List.append  !listeDesBouclesDuNidCourant [numBoucle];			
		listeBouclesImbriquees := [];

		let maListeDesBoucleOuAppelPred = 	!listeBoucleOuAppelCourante		in
		listeBoucleOuAppelCourante := [];

		let idBoucleEngPred = !idBoucleEng in 										
		idBoucleEng := numBoucle;	
		
		aUneFctNotDEf := false;
		analyse_statement  stat;
		idBoucleEng := idBoucleEngPred;


		listeNextExp := [];
		(*analyse_expressionaux exp ;*)
		analyse_expressionaux   exp ;
		let ne = !nouvExp in   
		let varIfN =  Printf.sprintf "%s-%d" "TWH" numBoucle  in	 
		let newaffect =new_instVar  varIfN  (EXP(ne)) in 
		listeDesInstCourantes := List.append !listeDesInstCourantes  [newaffect]; 
		listeDesInstCourantes := List.append !listeDesInstCourantes  !listeNextExp; 

 		let lesInstDeLaBoucle = !listeDesInstCourantes in
	
		let li = if !aUneFctNotDEf = true then 
		begin 
			(*Printf.printf "traitement particuloier boucle\n";*)
			let maListeDesBoucleOuAppelPredP = !listeBoucleOuAppelCourante in
			let (ida,nbi,idb,id_if) = (!idAppel,!nbImbrications , !idBoucle,!idIf) in	
			listeDesInstCourantes := []; onlyAstatement stat;onlyAexpression   exp ; idAppel := ida; nbImbrications :=nbi;idBoucle:=idb;idIf:=id_if; (*Printf.printf "traitement particulier boucle FIN\n";  *)
			listeBoucleOuAppelCourante := 	maListeDesBoucleOuAppelPredP;			
			!listeDesInstCourantes
		end 
		else !listeDesInstCourantes in

		listeDesInstCourantes := lesInstDeLaBoucle;
 
		let listeVCond =  listeDesVarsDeExpSeules  exp in  
		let na = extractVarCONDAffect  li listeVCond in

		let asna = evalStore (new_instBEGIN (na)) [] [] in
		let listeVDeBoucle =  	rechercheListeDesVarDeBoucle  listeVCond 	asna in
	
		let (varDeB, constante, lVB) =
			(if listeVDeBoucle = [] then (varBoucleIfN, true, [])
			else
				if (List.tl listeVDeBoucle) = [] then 
					(List.hd listeVDeBoucle, false, []) (*la boucle ne depend que d'une seule variable on peut traiter*)	
				else (varBoucleIfN, false, listeVDeBoucle))in
		
		let las = evalStore (new_instBEGIN (listePred)) [] [] in
		isExactForm := (hasMultiOuputInst stat = false) && (!trueList = []) && (!falseList = []);
		(*Printf.printf "\n\nAnalyse statement : la boucle %d   \n" numBoucle;

afficherLesAffectations (  lesInstDeLaBoucle) ;new_line () ;*)


		(*if !isExactForm then Printf.printf "exact\n" else Printf.printf "non exact\n" ;*)
		let (nb,_) =  traiterConditionBoucle "do" numBoucle deg ne(*exp*) idBoucleEngPred  varDeB constante  varBoucleIfN lVB las asna listeVDeBoucle  (VARIABLE(varIfN)) na in 
	(*Printf.printf "\n\nAnalyse statement : la boucle %d   ap\n" numBoucle;*)
		listeDesInstCourantes :=  [new_instFOR numBoucle varBoucleIfN (EXP(NOTHING)) (EXP(ne(*exp*))) (EXP(NOTHING)) (EXP( nb)) 
									(new_instBEGIN (lesInstDeLaBoucle ))];				
		
		let res = majABB []	!doc.laListeDesAssosBoucleBorne 	numBoucle (*lesInst*)!listeDesInstCourantes in
		if !vDEBUG then Printf.printf "\n\nAnalyse statement : noeud traité : %d varDEBOUCLE %s \n\n " numBoucle varBoucleIfN;
		if (!listeBouclesImbriquees = []) then 	(*  test ne contient pas de boucle *)
		begin
			if !vDEBUG then Printf.printf "\n\nAnalyse statement : la boucle %d ne contient pas de boucle \n" numBoucle;
			noeudCourant :=(new_NidDeBoucle ne(*exp*) (rechercheAssosBoucleBorne numBoucle)  varBoucleIfN !listeDesInstCourantes []) 
		end
		else 
		begin
			if !vDEBUG then Printf.printf "\nAnalyse statement : la boucle %d contient boucles appel relierLesNoeudsEnglobesAuNoeudCourant\n" numBoucle;
			(* attention on peut avoir X sous noeuds et donc 1 liste de noeuds et pas un seul*)
			relierLesNoeudsEnglobesAuNoeudCourant numBoucle varBoucleIfN !listeNoeudCourant !listeBouclesImbriquees
			exp
		end;									
		(* si la boucle est au départ d'un noeud*)
		if (idBoucleEngPred = 0) then
		begin
			doc := 	new_document !doc.laListeDesBoucles !doc.laListeDesFonctions 	res	 (List.append [!noeudCourant] !doc.laListeDesNids);
			listeTripletNidCourantPred := [];
			listeDesBouclesDuNidCourant := [];
			listeNoeudCourant := []
		end 
		else
		begin
			listeNoeudCourant := List.append 	[!noeudCourant] !listeNoeudCourant ;
			doc := 	new_document !doc.laListeDesBoucles !doc.laListeDesFonctions 	res (List.append [!noeudCourant] !doc.laListeDesNids)
		end;
		listeBouclesImbriquees :=  List.append [numBoucle] !listeBouclesImbriquees;
		listeBouclesImbriquees :=  List.append listeBouclesInbriqueesPred !listeBouclesImbriquees ;
		listeDesInstCourantes :=   List.append listePred (List.append !listADD !listeDesInstCourantes);	
		nbImbrications := degPred; 										
		listeBoucleOuAppelCourante :=  maListeDesBoucleOuAppelPred 

	| FOR (exp1, exp2, exp3, stat) ->
		let degPred = !nbImbrications in 
		 
		nbImbrications := !nbImbrications + 1;
		let deg = !nbImbrications in  

		if !nbImbrications >= !nbImbricationsMaxAppli then  nbImbricationsMaxAppli := !nbImbrications;

		listeNextExp := [];
		analyse_expression  exp1 ;
		idBoucle := !idBoucle +1;
		let num = !idBoucle in		

		let idBoucleEngPred = !idBoucleEng in 	
		aUneFctNotDEf := false;	
		idBoucleEng := num;
	
		(*analyse_expressionaux  exp2;*)
		analyse_expressionaux   exp2 ;
		let ne = !nouvExp in   
		let varIfN =  Printf.sprintf "%s-%d" "TWH" num  in	 
		let newaffect =new_instVar  varIfN  (EXP(ne)) in 
		listeDesInstCourantes := List.append !listeDesInstCourantes  [newaffect]; 


		let varBoucleIfN =  Printf.sprintf "%s-%d" "bIt" !idBoucle in	
		let listePred = !listeDesInstCourantes in
		listAssocIdType := List.append !listAssocIdType [(varBoucleIfN, INT_TYPE)] ;
		listeDesInstCourantes := !listeNextExp;	
		let (fic,lig)=getAssosIdLoopRef num in										
		listeBoucleOuAppelCourante	:= List.append  !listeBoucleOuAppelCourante [IDBOUCLE(num, !trueList,!falseList, fic, lig )];	
		let listeBouclesInbriqueesPred  = !listeDesBouclesDuNidCourant in
		let maListeDesBoucleOuAppelPred = 	!listeBoucleOuAppelCourante		in
		listeBoucleOuAppelCourante := [];
					
		listeDesBouclesDuNidCourant := List.append  !listeDesBouclesDuNidCourant [num];
		listeBouclesImbriquees := [];
	
		analyse_statement   stat;
		idBoucleEng := idBoucleEngPred;

		(* recherche des variables de la condition qui sont dans le aS cad modifiées par la boucle*)
		analyse_expression  exp3;
		listeNextExp := [];
		(*analyse_expressionaux  exp2;*)
		analyse_expressionaux   exp2 ;
		let lesInstDeLaBoucle = !listeDesInstCourantes in
		listeASCourant := [];
		let li = if !aUneFctNotDEf = true then  
		begin 
			let (ida,nbi,idb,id_if) = (!idAppel,!nbImbrications , !idBoucle,!idIf) in	
			let maListeDesBoucleOuAppelPredP = 	!listeBoucleOuAppelCourante		in
			(*Printf.printf "traitement particulier boucle \n";*)
			listeDesInstCourantes := []; onlyAstatement stat;onlyAexpression   exp3 ;onlyAexpression   exp2; idAppel := ida; nbImbrications :=nbi;idBoucle:=idb;idIf:=id_if; (*Printf.printf "traitement particulier boucle FIN\n"; *) 
			listeBoucleOuAppelCourante := 	maListeDesBoucleOuAppelPredP;		
			!listeDesInstCourantes
		end  
		else !listeDesInstCourantes in
		listeDesInstCourantes := lesInstDeLaBoucle;
		let listeVCond =  listeDesVarsDeExpSeules  exp2 in  
		let na = extractVarCONDAffect  li listeVCond in
 
		let asna = evalStore (new_instBEGIN (na)) [] [] in		 
		let listeVDeBoucle =  	rechercheListeDesVarDeBoucle  listeVCond 	asna in
		(*remarque ajouter les initialisations au bloc englobant et exp3 à la boucle *)
		

		let (varDeBoucle, constante, 	listeVB) =
		(if listeVDeBoucle = [] then (varBoucleIfN, true, [])
		else
			if (List.tl listeVDeBoucle) = [] then (List.hd listeVDeBoucle, false, [])(*la boucle ne depend que d'une seule variable on peut traiter*)
			else (varBoucleIfN, false, listeVDeBoucle))in	
 
		let las=  evalStore (new_instBEGIN (listePred)) [] [] in
				isExactForm := (hasMultiOuputInst stat = false) && (!trueList = []) && (!falseList = []);
(*Printf.printf "\n\nAnalyse statement : la boucle %d   \n" num;
afficherLesAffectations (  lesInstDeLaBoucle) ;new_line () ;*)
(*
if !isExactForm then Printf.printf "exact\n" else Printf.printf "non exact\n" ;*)
		let (nb,addtest) = traiterConditionBoucleFor 	"for" num deg ne(*exp2*)
					idBoucleEngPred (*exp1*) exp3  varDeBoucle constante varBoucleIfN listeVB las asna listeVDeBoucle (VARIABLE(varIfN)) na in	
		(*Printf.printf "\n\nAnalyse statement : la boucle %d  ap \n" num;*)
		listeDesInstCourantes := 
				[	new_instFOR num varBoucleIfN	(EXP(exp1)) (EXP(ne(*exp2*))) (EXP(exp3))  (EXP( nb)) (new_instBEGIN lesInstDeLaBoucle )  ];
					
																		
		let res = majABB []	!doc.laListeDesAssosBoucleBorne 	num  !listeDesInstCourantes in
		if !vDEBUG then Printf.printf "\n\nAnalyse statement : noeud traité : %d varDEBOUCLE %s \n\n " num varBoucleIfN;
		if (!listeBouclesImbriquees = []) then 	(*  test ne contient pas de boucle *)
		begin
			if !vDEBUG then  Printf.printf "\n\nAnalyse statement : la boucle %d ne contient pas de boucle \n" num;
			noeudCourant :=(new_NidDeBoucle exp2 (rechercheAssosBoucleBorne num)  varBoucleIfN  !listeDesInstCourantes []) 								
		end
		else 
		begin
			if !vDEBUG then Printf.printf "\n\nAnalyse statement : la boucle %d contient des boucles appel relierLesNoeudsEnglobesAuNoeudCourant\n" num;
			(* attention on peut avoir X sous noeuds et donc 1 liste de noeuds et pas un seul*)
			relierLesNoeudsEnglobesAuNoeudCourant num varBoucleIfN !listeNoeudCourant !listeBouclesImbriquees exp2
		end;									
		(* si la boucle est au départ d'un noeud*)
		if (idBoucleEngPred = 0) then
		begin
			doc := 	new_document !doc.laListeDesBoucles !doc.laListeDesFonctions 	res	
					(List.append [!noeudCourant] !doc.laListeDesNids);
			listeTripletNidCourantPred := [];
			listeDesBouclesDuNidCourant := [];
			listeNoeudCourant := []
		end 
		else
		begin
			listeNoeudCourant := List.append 	[!noeudCourant] !listeNoeudCourant ;
			doc := 	new_document !doc.laListeDesBoucles !doc.laListeDesFonctions 	res	 
				 (List.append [!noeudCourant] !doc.laListeDesNids)
		end;
		listeBouclesImbriquees :=  List.append [num] !listeBouclesImbriquees;
		listeBouclesImbriquees :=  List.append listeBouclesInbriqueesPred !listeBouclesImbriquees ;
		listeDesInstCourantes :=  List.append( List.append listePred (List.append !listADD !listeDesInstCourantes)) !listeNextExp;
		nbImbrications := degPred; 		

 											
		listeBoucleOuAppelCourante :=  maListeDesBoucleOuAppelPred 
	
	| BREAK | CONTINUE -> 			()
	| RETURN (exp) ->		if exp = NOTHING	then ()	else 
							begin
								(*analyse_expression  exp ;*)
								listeNextExp := [];
								analyse_expressionaux  exp ;
								let ne = !nouvExp in
								let nouvarres = Printf.sprintf "res-%s" !nomFctCour  in
								let newaffect = new_instVar  (nouvarres)  (EXP(ne))in
								listeDesInstCourantes :=List.append ( List.append !listeDesInstCourantes  [newaffect]) !listeNextExp
							end
	| SWITCH (exp, stat) ->			analyse_expression   exp ;
									let ne = !nouvExp in   
									idSwitch := !idSwitch + 1;
									let varIfNaux =  Printf.sprintf "%s-%d" "SW" !idSwitch  in	 
									let newaffect =new_instVar  varIfNaux  (EXP(ne)) in 
									listeDesInstCourantes := List.append !listeDesInstCourantes  [newaffect]; 
									listOfCase := [];
(*Printf.printf "odl statement\n";
print_substatement stat;*)
									let listOfStat = listeSwitchStatement  stat in
									analyseSwitchStatement stat varIfNaux listOfStat;

									let newStatement = buildSwitchStatement !listOfCase !listOfDefault in

(*Printf.printf "new statement\n";
print_substatement newStatement;*)
									
									(*let isPred = !isIntoSwithch in*)
									(*isIntoSwithch := true;*)
									analyse_statement    newStatement (* à traiter *);
									
								(*	isIntoSwithch := isPred*)

	| CASE (exp, stat) ->			analyse_expression   exp ;
									analyse_statement    stat (* a traiter *);
	| DEFAULT stat ->				analyse_statement    stat
	| LABEL ((*name*)_, stat) ->	analyse_statement    stat
	| GOTO (*name*)_ ->				()
	| ASM (*desc*)_ ->				()
	| GNU_ASM ((*desc, output, input, mods*)_,_,_,_) -> 	()
	| _ -> ()

and  construireListesES listeDesES arg   =
	if (listeDesES = [] || arg = []) then begin (*Printf.printf "construireListesES vide";*) ()end
	else
	begin		
		let valeurParam = List.hd arg in
		(*analyse_expression  valeurParam; (*VOIR*) *)
		let premier = List.hd listeDesES in
			match premier with			
			ENTREE (nom) ->	(* le type de nom n'est pas pointeur *) 
					entrees := List.append !entrees [new_instVar nom  (EXP(valeurParam))];
					construireListesES (List.tl listeDesES) (List.tl arg)  
				| SORTIE (nom) ->
					(* nom est de type pointeur soit fonction : f (void * k,...) et appel de f
					on peut avoir : f(&exp, ...), f(ptr, ...) on doit dans le premier car construire 
					l'affectation en fin d'appel de la fonction : exp = *k et dans l'autre *ptr=*k *)
						sorties := List.append !sorties (instPourVarDeExpEnSortie valeurParam (VARIABLE(nom))("*"^(nom)));
						construireListesES (List.tl listeDesES) (List.tl arg)  
				| ENTREESORTIE (nom) -> 
					entrees := List.append !entrees [new_instVar nom  (EXP(valeurParam))];
					sorties := List.append !sorties (instPourVarDeExpEnSortie valeurParam (VARIABLE(nom)) ("*"^(nom)));
					construireListesES (List.tl listeDesES) (List.tl arg)  
		end

	(* nom est de type pointeur soit fonction : f (void * k,...) et appel de f
	on peut avoir : f(&exp, ...), f(ptr, ...), f(ptr+i, ...) on doit dans le premier car construire 
	l'affectation en fin d'appel de la fonction : exp = *k et dans l'autre *ptr=*k *)
	and instPourVarDeExpEnSortie valeurParam expressionAffectation nom =
		match valeurParam with
		VARIABLE n -> (*Printf.printf "construireListesES tableau ou pointeur \n";*)
					  [new_instMem ("*"^n) (EXP(VARIABLE(n))) (EXP (UNARY(MEMOF, expressionAffectation)))]
					(* on peut avoir p = ptr pointeur ou tableau*)
			(*  cas ou on passe ptr car hypothèse code OK *)
		| UNARY (op , e)->
			(	match op with 
				ADDROF	-> 
				(	match e with
					(*on a &exp mais exp peut être une variable, un tableau ou un champ de struct*)
					VARIABLE v ->(* Printf.printf "construireListesES &v \n";*) let nas = [new_instVar v  (EXP (VARIABLE(nom)))] in (*afficherLesAffectations  nas;*)nas
							
					| INDEX (t, i) -> 
						( 	match t with 
							VARIABLE v -> 
								[new_instTab v (EXP(i)) (EXP (VARIABLE(nom)))]
							| _-> if !vDEBUG then Printf.printf "exp pour tab avec nom tab pas variable non traité\n";
							[])														
					| MEMBEROF (_, _) ->
						[new_instVar (expressionToString "" e 0)(EXP (VARIABLE(nom)))]
					| MEMBEROFPTR (_, _) ->	
						[new_instVar (expressionToString "" e 0) (EXP (VARIABLE(nom)))]
					| _->if !vDEBUG then  Printf.printf "erreur lvalue attendue pour ce param (impossible car code OK)"; []
				)
				| _->if !vDEBUG then  Printf.printf "erreur lvalue attendue pour ce param (impossible car code OK)"; []
			)
		| BINARY (_,_,_)-> (* on peut avoir en paramètre ptr +i*)
			[new_instVar 	(expressionToString  "" valeurParam 0) (EXP (VARIABLE(nom)))]
		|_-> if !vDEBUG then 
				Printf.printf "erreur lvalue attendue pour ce param (impossible car code OK)";[]
		
											
and creerAFFECT op e1 e2 =
	 match e1 with
		VARIABLE n -> 
			listeDesInstCourantes :=  List.append !listeDesInstCourantes [ new_instVar n  (EXP(BINARY(op, VARIABLE(n), e2)))]
		|INDEX (t,i)-> 
			( match t with 
				VARIABLE v -> 
					listeDesInstCourantes :=  List.append !listeDesInstCourantes  [new_instTab v (EXP(i)) (EXP(BINARY(op, INDEX (t,i), e2)))]
				| UNARY (opr,e) ->
				(
					match e with
						VARIABLE v ->
						(
						 match opr with
						 MEMOF		->(** "*" *)(* revoir e n'est pas forcement une variable *)
							listeDesInstCourantes := List.append !listeDesInstCourantes [new_instTab ("*"^v) (EXP(i)) (EXP(BINARY(op,INDEX (t,i), e2)))]
						 | ADDROF	->(** "&" . *)
							listeDesInstCourantes := List.append !listeDesInstCourantes [new_instTab ("&"^v) (EXP(i))(EXP(BINARY(op, INDEX (t,i), e2)))]
						 |  _->	if !vDEBUG then  Printf.printf "expression pour tableau avec nom tab pas variable non encore traité\n" 
						)
					| _-> if !vDEBUG then  Printf.printf "expression pour tableau avec nom tab pas variable non encore traité\n" 
				)
				| _-> if !vDEBUG then Printf.printf "expression  pour  tableau avec nom tab pas variable non traité	actuellement\n"
			)
		| UNARY (opr,e) ->
			(
				match e with
					VARIABLE v ->
					(
					 match opr with
					 MEMOF		->(** "*" . *)(* revoir e n'est pas forcement une variable *)
						let newaff =new_instMem  ("*"^v) (EXP(VARIABLE(v))) (EXP(BINARY(op, VARIABLE("*"^v), e2))) in
						
						listeDesInstCourantes := List.append !listeDesInstCourantes [newaff]
					 | ADDROF	->(** "&" . *)
						let newaff =new_instVar ("&"^v) (EXP(BINARY(op, VARIABLE("&"^v), e2))) in
						
					   	listeDesInstCourantes := List.append !listeDesInstCourantes  [newaff]
					 |  _->  if !vDEBUG then Printf.printf "expression pour tableau avec nom tab pas variable non encore traité\n" 
					)
					| _->  (*if !vDEBUG then *) Printf.printf "expression pour tableau ou struct avec nom tab pas variable non encore traité\n" 
			)
		| MEMBEROF (e , t) 			 
		| MEMBEROFPTR (e , t) 	->	 
					let lid =	getInitVarFromStruct e1  in

				
						let id = if lid != [] then List.hd lid else (Printf.printf "not id 3876\n"; "noid") in
						let (btype, isdeftype) = 
								if List.mem_assoc id !listAssocIdType then (getBaseType (List.assoc id !listAssocIdType), true) 
								else 
									if List.mem_assoc id !listeAssosPtrNameType then (getBaseType (List.assoc id !listeAssosPtrNameType), true) 
									else (INT_TYPE, false) in
						
						
					if lid != [] then 
					begin
						
						 
						(*Printf.printf "varDefList id %s type :\n"id; printfBaseType btype;new_line();*)
						let ne = consCommaExp (VARIABLE(id)) btype [id] lid (BINARY(op, e1, e2))  in
						let newaff = new_instVar id (EXP(ne) ) in
							(*Printf.printf"Dans creerAFFECT  struct (*ptr*) assign\n";
						Printf.printf "affect du & \n"; afficherUneAffect newaff;new_line();*)
						listeDesInstCourantes := List.append !listeDesInstCourantes   [newaff];
					end;
				

(*( creerStructAffect e1 (*VARIABLE(id)*) id (List.tl lid) btype (EXP(BINARY(op, VARIABLE(n), e2))))]*)

		| _->	 if !vDEBUG then  Printf.printf "expression  pour  tableau avec nom tab pas variable non traité	actuellement\n"
(*	|_-> print "expression  pour non variable et non tableau non traité	actuellement\n"*)
		
											 											
and affectationUnaire op e = creerAFFECT op e  (CONSTANT(CONST_INT("1")))
and affectationBinaire op e1 e2 = creerAFFECT op e1 e2
and contruireAux par args	=
	if par = [] || args = [] then ()
	else
	begin
		analyse_expression (BINARY(ASSIGN, VARIABLE(List.hd(par)), List.hd(args)));
		contruireAux (List.tl par) (List.tl args)
	end			
																
and  construireAsAppel dec	appel =
 	let (t, _, name) = dec in 
 	let (_, typep, _, _) = name in
 	let base = get_base_type typep in
 	let liste =
		(match base with
			PROTO (t, pars, _) -> List.map( fun pc -> let (_, _, n) = pc in let (id, _, _, _) = n in id)  pars 
			| OLD_PROTO (_, pars, _) ->	pars 
			| _ -> []) in	
 	match appel with
	 	CALL (_, args) ->	contruireAux liste args | _-> ()

and externFct base appel =
let liste =
		(match base with
			PROTO (t, pars, _) -> List.map( fun pc -> let (_, _, n) = pc in let (id, _, _, _) = n in id)  pars 
			| OLD_PROTO (_, pars, _) ->	pars 
			| _ -> []) in	
 	match appel with
	 	CALL (_, args) ->	contruireAux liste args | _-> ()


and  analyse_expression exp =
listeNextExp := [];
analyse_expressionaux exp ;
listeDesInstCourantes := List.append !listeDesInstCourantes !listeNextExp

and  analyse_expressionaux exp =

	 match exp with
		NOTHING -> 				nouvExp := exp	
	| 	UNARY (op, e) -> 	
			 
			(match op with		(*je ne distingue pas pre et post operation linearise attention aux conditions *)
				PREINCR  -> 	analyse_expressionaux e;	 let ne = !nouvExp in affectationUnaire ADD ne
				| POSINCR -> 	
					let p = !listeDesInstCourantes in
								listeDesInstCourantes := [];
								analyse_expressionaux e;	 let ne = !nouvExp in  affectationUnaire ADD ne ;
								listeNextExp :=  List.append !listeNextExp !listeDesInstCourantes;
								listeDesInstCourantes := p;
								
				| PREDECR  ->   analyse_expressionaux e;	 let ne = !nouvExp in  affectationUnaire SUB ne
				| POSDECR ->  
					let p = !listeDesInstCourantes in
								listeDesInstCourantes := [];
								analyse_expressionaux e;	 let ne = !nouvExp in  affectationUnaire SUB ne ;
								listeNextExp :=  List.append !listeNextExp !listeDesInstCourantes;
								listeDesInstCourantes := p;
				| ADDROF	->(** "&" . nouvExp :=VARIABLE("&"^v)*)
					(match e with
						INDEX (t,i) ->
							(*Printf.printf "adresse de...\n";print_expression e 0; new_line(); print_expression t 16;print_expression i 0;*)
			
							let (tab,lidx) = analyseArray e []  in
							if tab = "" then nouvExp := exp
							else 
							begin
								let sygmaIndex = (*(CONSTANT(CONST_INT("0"))) in*)
										if lidx = [] then (CONSTANT(CONST_INT("0"))) else if (List.tl lidx) = [] then i else NOTHING in
								nouvExp := BINARY (ADD, (VARIABLE(tab)), sygmaIndex) ;

							end
						| _->
								nouvExp := exp)
				|_ -> 		if !vDEBUG then Printf.printf "non traite\n";analyse_expressionaux e;	 let ne = !nouvExp in  nouvExp := UNARY (op, ne) 
			);
	| BINARY (op, exp1, exp2) -> 
	(*	analyse_expressionaux exp1 ; let ne1 = !nouvExp in 	
		analyse_expressionaux exp2;	 let ne = !nouvExp in   *)
		(	match op with		
			ASSIGN		->
			(	match exp1 with
				VARIABLE n ->  analyse_expressionaux exp2;	 let ne = !nouvExp in   
					let newaffect =new_instVar  n  (EXP(ne)) in
						(* afficherUneAffect newaffect; flush(); new_line(); *)
					listeDesInstCourantes := List.append !listeDesInstCourantes  [newaffect]
				|INDEX (t,i)-> 
					( match t with 
						VARIABLE v -> 
								analyse_expressionaux exp2;	 let ne = !nouvExp in   
								listeDesInstCourantes := List.append !listeDesInstCourantes [new_instTab v (EXP(i))	(EXP(ne))]
						| UNARY (opr,e) ->
							(
								match e with
								VARIABLE v ->
								(
									match opr with
									MEMOF		->analyse_expressionaux exp2;	 let ne = !nouvExp in   
					(** "*" operator. *)(* revoir e n'est pas forcement une variable *)
										listeDesInstCourantes := 
											List.append !listeDesInstCourantes 
														[new_instTab ("*"^v) (EXP(i))	(EXP(ne))]
									| ADDROF	->(** "&" operator. *)analyse_expressionaux exp2;	 let ne = !nouvExp in   
											listeDesInstCourantes := 
												List.append !listeDesInstCourantes 
															[new_instTab ("&"^v) (EXP(i))	(EXP(ne))]
									|  _->	 if !vDEBUG then  Printf.printf "expr pour tableau  non traitée\n" ;
								)
								| _->  if !vDEBUG then  Printf.printf "expr pour tableau  non traitée\n" 
							)
						| _->	 if !vDEBUG then  Printf.printf "expr pour tableau  non traitée\n" 	
					)
				| UNARY (opr,e) -> 
					(*let p = !listeNextExp in*)
					(*
					analyse_expressionaux e ;
					listeNextExp := p;
					let neunary = !nouvExp in 	*)
					(
						match opr with
							MEMOF		->
								analyse_expressionaux e ;(*listeNextExp := p;*)

								(match !nouvExp with
								  VARIABLE v -> analyse_expressionaux exp2;	 let ne = !nouvExp in   
									(** "*" operator. *)(*Printf.printf "expr pour tableau  MEMOF\n" ;
									     afficherUneAffect( new_instMem ("*"^v) (EXP(VARIABLE(v))) (EXP(ne))); flush(); new_line(); *)
									listeDesInstCourantes := List.append !listeDesInstCourantes  [new_instMem ("*"^v) (EXP(VARIABLE(v))) (EXP(ne))]
								  | UNARY(ADDROF,expaux)	->(** "&" operator. *)
									(match expaux with
									 VARIABLE v -> analyse_expressionaux exp2;	 let ne = !nouvExp in   
										listeDesInstCourantes := List.append !listeDesInstCourantes  [new_instVar v 	(EXP(ne))]
								     |_->if !vDEBUG then Printf.printf "expr pour tableau  non traitée\n" )
								|_->if !vDEBUG then Printf.printf "expr pour tableau  non traitée\n" )
					
							
							| ADDROF	->(** "&" operator. *)analyse_expressionaux e ;(*listeNextExp := p;*)
								(match  !nouvExp with
								  VARIABLE v ->analyse_expressionaux exp2;	 let ne = !nouvExp in   
									  listeDesInstCourantes := List.append !listeDesInstCourantes 
																			[new_instVar ("&"^v) 	(EXP(ne))]
									| UNARY(MEMOF,expaux)	->(** "&" operator. *)
										(match expaux with
										VARIABLE v ->analyse_expressionaux exp2;	 let ne = !nouvExp in   
											listeDesInstCourantes := List.append !listeDesInstCourantes  [new_instVar v 	(EXP(ne))]
										|_->if !vDEBUG then Printf.printf "expr pour tableau  non traitée\n" )
									|_->if !vDEBUG then Printf.printf "expr pour tableau  non traitée\n" )

							|  _->	 if !vDEBUG then Printf.printf "expr pour tableau  non traitée\n" 	 )
						
				 (*  *)
				 | MEMBEROF (e , t) 			
				 | MEMBEROFPTR (e , t) 	->		
						let lid =	getInitVarFromStruct exp1  in
						let id = if lid != [] then List.hd lid else (Printf.printf "not id 3876\n"; "noid") in
						let (btype, isdeftype) = 
								if List.mem_assoc id !listAssocIdType then (getBaseType (List.assoc id !listAssocIdType), true) 
								else 
									if List.mem_assoc id !listeAssosPtrNameType then (getBaseType (List.assoc id !listeAssosPtrNameType), true) 
									else (INT_TYPE, false) in
						
						if lid != [] then 
						begin
							analyse_expressionaux exp2;	 let ne = !nouvExp in  
							(*Printf.printf "varDefList id %s type :\n"id;  new_line();*)
							let nee = consCommaExp (VARIABLE(id)) btype [id] lid ne  in
							(*Printf.printf "varDefList id %s type :\n"id;  new_line();print_expression ne 0 ; flush();space() ;
							Printf.printf "varDefList id %s type :\n"id;  new_line();print_expression nee 0 ; flush();space() ;new_line(); *)
							let newaffect = new_instVar id (EXP(nee) ) in
							
							listeDesInstCourantes := List.append !listeDesInstCourantes  [newaffect];
						end;
					
	
				 |_-> if !vDEBUG then Printf.printf "expr pour tableau  non traitée\n" 		 
			); 
			
			| ADD_ASSIGN	->analyse_expressionaux exp2;	 let ne = !nouvExp in    affectationBinaire ADD exp1 ne;  nouvExp:=BINARY (op, exp1, ne) 
			| SUB_ASSIGN	-> analyse_expressionaux exp2;	 let ne = !nouvExp in   affectationBinaire SUB exp1 ne;  nouvExp:=BINARY (op, exp1, ne) 
			| MUL_ASSIGN	-> analyse_expressionaux exp2;	 let ne = !nouvExp in   affectationBinaire MUL exp1 ne ; nouvExp:=BINARY (op, exp1, ne) 
			| DIV_ASSIGN	-> analyse_expressionaux exp2;	 let ne = !nouvExp in   affectationBinaire DIV exp1 ne ; nouvExp:=BINARY (op, exp1, ne) 
			| MOD_ASSIGN	-> analyse_expressionaux exp2;	 let ne = !nouvExp in   affectationBinaire MOD exp1 ne ; nouvExp:=BINARY (op, exp1, ne) 
			| BAND_ASSIGN	-> analyse_expressionaux exp2;	 let ne = !nouvExp in   affectationBinaire BAND exp1 ne; nouvExp:=BINARY (op, exp1, ne) 
			| BOR_ASSIGN	-> analyse_expressionaux exp2;	 let ne = !nouvExp in   affectationBinaire BOR exp1 ne ; nouvExp:=BINARY (op, exp1, ne) 
			| XOR_ASSIGN	-> analyse_expressionaux exp2;	 let ne = !nouvExp in   affectationBinaire XOR exp1 ne ; nouvExp:=BINARY (op, exp1, ne) 
			| SHL_ASSIGN	-> analyse_expressionaux exp2;	 let ne = !nouvExp in   affectationBinaire SHL exp1 ne ; nouvExp:=BINARY (op, exp1, ne) 
			| SHR_ASSIGN	-> analyse_expressionaux exp2;	 let ne = !nouvExp in   affectationBinaire SHR exp1 ne ; nouvExp:=BINARY (op, exp1, ne) 
			| _ -> analyse_expressionaux exp1 ; let ne1 = !nouvExp in 	analyse_expressionaux exp2;	 let ne = !nouvExp in   
					nouvExp:=BINARY (op, ne1, ne) 
		)
	| QUESTION (exp1, exp2, exp3) ->
				analyse_expressionaux exp1 ;
				let ne1 = !nouvExp in
				analyse_expressionaux exp2;
				let ne2 = !nouvExp in
				analyse_expressionaux exp3;
				let ne3 = !nouvExp in 
    			nouvExp:=QUESTION (ne1, ne2, ne3)
																					
	| CAST (t, e) 						->  analyse_expressionaux e ; nouvExp:=CAST (t, !nouvExp) 
	| CALL (e , args) 				->		
				let listeInstPred = !listeDesInstCourantes in					
				if existeFonction (nomFonctionDeExp e) && (not (is_in_use_partial (nomFonctionDeExp e))) then 
				begin

					let fonction = rechercheFonction (nomFonctionDeExp e) in
					let (_, f) = fonction in
					listeDesInstCourantes := [];
					construireAsAppel f.declaration	exp ;
					(*let (t, _, _) = f.declaration in 
  
					let isvoid =	if t = VOID then true else false in*)
					(*if isvoid then Printf.printf "la fonction %s is void \n"(nomFonctionDeExp e) 
					else Printf.printf "la fonction %s is NOT void \n"(nomFonctionDeExp e) ;*)
					idAppel := !idAppel + 1;
				    let ida = !idAppel in	

(*Printf.printf "analyse_expressionaux %s num appel %d \n" (nomFonctionDeExp e) ida;	*)

(*Printf.printf "analyse_expressionaux %s EXISTE \n" (nomFonctionDeExp e) ;*)
					 let (fichier , ligne ) = getAssosIdCallFunctionRef ida in
					listeBoucleOuAppelCourante	:= 
						List.append  !listeBoucleOuAppelCourante  [IDAPPEL(ida, exp, !listeDesInstCourantes,"", !trueList,!falseList ,fichier , ligne)];
					let _ = traiterAppelFonction e args !listeDesInstCourantes ida in
					let nouvar = Printf.sprintf "call-%s%d" (nomFonctionDeExp e) ida in
					(*if isvoid = false then *)
					begin 
						
						let nouvarres = Printf.sprintf "res-%s" (nomFonctionDeExp e) in
						let newaffect = new_instVar  (nouvar)  (EXP(VARIABLE(nouvarres))) in
						listeDesInstCourantes :=  List.append !listeDesInstCourantes  [newaffect]
					end;
					listeDesInstCourantes :=  List.append listeInstPred !listeDesInstCourantes ;

(*afficherLesAffectations (  !listeDesInstCourantes) ;new_line () ;*)
(*Printf.printf "FIN analyse_expressionaux %s num appel %d \n" (nomFonctionDeExp e) ida;	*)

					nouvExp:=VARIABLE(nouvar)
				end
				else 
				begin 
					listeDesInstCourantes := [];
					let nom = (nomFonctionDeExp e) in
					if existeNomFonctionDansListe nom  then
					begin 
						let (_, _,base) = tupleNumNomFonctionDansListe nom in
						externFct base exp
					end
					else (* List.iter 
						(fun ep -> analyse_expression (BINARY(ASSIGN, VARIABLE( Printf.sprintf "%s%d" nom !numArg), ep));numArg := !numArg +1 ) args; 
					numArg:=0;*)
					 List.iter (fun ep -> analyse_expression  ep  ) args;
					idAppel := !idAppel + 1;
				    let ida = !idAppel in	
(*Printf.printf "analyse_expressionaux %s num appel %d \n" (nomFonctionDeExp e) ida;		
Printf.printf "analyse_expressionaux %s NON EXISTE \n" (nomFonctionDeExp e) ;*)
					 let (fichier , ligne ) = getAssosIdCallFunctionRef ida in
					listeBoucleOuAppelCourante	
						:= List.append  !listeBoucleOuAppelCourante [IDAPPEL(ida, exp,!listeDesInstCourantes,"" , !trueList,!falseList ,fichier , ligne)];
					let isComponant = traiterAppelFonction e args !listeDesInstCourantes ida in

(*if isComponant then Printf.printf "analyse_expressionaux %s NON EXISTE IS COMPOSANT %d\n" (nomFonctionDeExp e) ida
else   Printf.printf "analyse_expressionaux %s NON EXISTE IS NOT COMPOSANT\n" (nomFonctionDeExp e) ;*)
					let nouvar = Printf.sprintf "call-%s%d" nom ida in
					let nouvarres = Printf.sprintf "res-%s" nom in
					let newaffect = new_instVar  (nouvar)  (EXP(VARIABLE(nouvarres))) in
					listeDesInstCourantes :=  List.append !listeDesInstCourantes  [newaffect];
					listeDesInstCourantes :=  List.append listeInstPred !listeDesInstCourantes ;

(*afficherLesAffectations (  !listeDesInstCourantes) ;new_line () ;*)
(*Printf.printf "FIN analyse_expressionaux %s num appel %d \n" (nomFonctionDeExp e) ida;	*)
					if isComponant then nouvExp:=VARIABLE(nouvar) else nouvExp:=exp
				end		;
	| COMMA e 	-> (*Printf.printf "dans comma\n";print_expression exp 0; new_line();*) List.iter (fun ep -> analyse_expressionaux ep) e;
					nouvExp:=COMMA(e)
	| MEMBEROF (e , t) 			(*->	analyse_expression e ;  nouvExp:=MEMBEROF (!nouvExp , t)*)
	| MEMBEROFPTR (e , t) 	->	(*Printf.printf "dans ptr\n";print_expression exp 0; new_line();	*)
		analyse_expressionaux e ; nouvExp:=MEMBEROFPTR (!nouvExp , t) (*nouvExp:=exp*)
	| GNU_BODY (decs, stat) 		-> 	
			let listePred = !listeDesInstCourantes in
			listeDesInstCourantes := [];
			analyse_statement (BLOCK (decs, stat));
			listeDesInstCourantes := 	[new_instBEGIN  !listeDesInstCourantes];
			listeDesInstCourantes :=    List.append listePred  !listeDesInstCourantes 	;
			nouvExp:=GNU_BODY (decs, stat)
	|	CONSTANT cst ->
			(match cst with 
					CONST_COMPOUND expsc ->  
(*Printf.printf "applystore MEMBEROFPTR lid non vide  assigncomma\n" ;print_expression exp 0; new_line();
Printf.printf "\n";*)
					nouvExp:=CONSTANT(CONST_COMPOUND(convael  expsc));
(*print_expression !nouvExp 0; new_line(); Printf.printf "adresse de...constant\n";*)
					|_->nouvExp:=exp	;(*Printf.printf "...constant\n";*)
			)
	| EXPR_SIZEOF exp ->
		analyse_expressionaux exp;
		( match !nouvExp with
			VARIABLE (v) ->  
							if (List.mem_assoc v !listeAssosPtrNameType) then nouvExp:=VARIABLE( "SIZEOF_PTR")
							else if (List.mem_assoc v !listAssosArrayIDsize) then
								 begin
									let size = getAssosArrayIDsize v in
									let typeElem = if existAssosArrayType v   then (get_baseinittype (getAssosAssosArrayType v ))
									else "SIZEOF_elementsOf"  ^ v ^"ARRAY" in
									(match size with
										NOSIZE -> if (List.mem_assoc v !listeAssosPtrNameType) then nouvExp:=VARIABLE( "SIZEOF_PTR")
												  else nouvExp:= BINARY(MUL,VARIABLE( "SIZEOF_"^v^"ARRAY_ELT_NUMBER"),  
																			VARIABLE( "SIZEOF_" ^ typeElem))
										| SARRAY (taille) -> nouvExp:= BINARY(MUL, CONSTANT(CONST_INT (Printf.sprintf "%d" taille)),  
																			VARIABLE( "SIZEOF_" ^ typeElem))
										| MSARRAY (lsize) -> let tsize = expressionEvalueeToExpression (prodListSize lsize) in
															nouvExp:= BINARY(MUL,  tsize,  
																			VARIABLE( "SIZEOF_" ^ typeElem))
									)
								 end
								 else if List.mem_assoc v !setAssosIDTYPEINIT then 
											nouvExp:=VARIABLE( "SIZEOF_"  ^ (get_baseinittype (List.assoc v !setAssosIDTYPEINIT)))
										else nouvExp:=EXPR_SIZEOF !nouvExp
			| INDEX (e, idx) ->	
				let (tab,lidx) = analyseArray (  !nouvExp) []  in
		
				if tab = "" then nouvExp:=EXPR_SIZEOF !nouvExp
				else 
				begin
					if (List.mem_assoc tab !listAssosArrayIDsize) then
								 begin
									let size = getAssosArrayIDsize tab in
									let typeElem = if existAssosArrayType tab  then (get_baseinittype (getAssosAssosArrayType tab ))
									else "SIZEOF_elementsOf"  ^ tab ^"ARRAY" in
									(match size with
										NOSIZE -> if (List.mem_assoc tab !listeAssosPtrNameType) then nouvExp:=VARIABLE( "SIZEOF_PTR")
												  else nouvExp:= BINARY(MUL,VARIABLE( "SIZEOF_"^tab^"ELT_NUMBER"),  
																			VARIABLE( "SIZEOF_" ^ typeElem))
										| SARRAY (taille) -> nouvExp:= BINARY(MUL, CONSTANT(CONST_INT (Printf.sprintf "%d" taille)),  
																			VARIABLE( "SIZEOF_" ^ typeElem))
										| MSARRAY (lsize) -> let tsize = expressionEvalueeToExpression (prodListSize lsize) in
															nouvExp:= BINARY(MUL, tsize,  
																			VARIABLE( "SIZEOF_" ^ typeElem))
									)
								 end
				end
			|UNARY (MEMOF,VARIABLE (v)) -> 
							if (List.mem_assoc v !listeAssosPtrNameType) then nouvExp:=VARIABLE( "SIZEOF_PTR")
							else if (List.mem_assoc v !listAssosArrayIDsize) then
								 begin
									 
									let typeElem = if existAssosArrayType v   then (get_baseinittype (getAssosAssosArrayType v ))
									else "SIZEOF_elementsOf"  ^ v ^"ARRAY" in
									nouvExp:=  VARIABLE( "SIZEOF_" ^ typeElem)
								 end
								 else   nouvExp:=EXPR_SIZEOF !nouvExp
			
			|_->  nouvExp:=EXPR_SIZEOF !nouvExp
		);				
	| TYPE_SIZEOF typ ->
			nouvExp:=VARIABLE( "SIZEOF_"  ^ (get_baseinittype typ));
(*traiter sizeof*)
	| _->(*Printf.printf "other cases\n";*)nouvExp:=exp
		

and convael l =
if l = [] then []
else
begin
analyse_expression (List.hd l);
let n = !nouvExp in
List.append [n] (convael  (List.tl l)  )
end
									
and ajouterReturn nomF lesAffectations =
	let nouvarres = Printf.sprintf "res-%s" nomF  in
	
	if lesAffectations = [] then begin  ()end
	else
	begin
		 
		withoutTakingCallIntoAccount := true;
		let asl = evalStore (new_instBEGIN(lesAffectations)) [] [] in
	    withoutTakingCallIntoAccount := false;
		if existAffectVDsListeAS nouvarres !listeASCourant then
		begin 
			let resaux = rechercheAffectVDsListeAS nouvarres (*index*) asl in
			listeASCourant := [];
			if resaux <> EXP(NOTHING) then
			begin
				let newaffect = new_instVar  nouvarres resaux in
				sorties := List.append !sorties [newaffect]
			end		
		end;
		 
	end
	
	
and getPartialResult nom = 
    let nom = (Filename.concat !out_dir (nom^".rpo")) in
    let chan = Unix.in_channel_of_descr (Unix.openfile nom [Unix.O_RDONLY] 0) in
    let (partialResult : compInfo) = Marshal.from_channel chan in  
	close_in chan;
    partialResult
     
and getExpBornesFromComp nom =
    (getPartialResult nom).expBornes
    	
and getESFromComp nom =
    (getPartialResult nom).compES

    
and getAbsStoreFromComp nom =
    (getPartialResult nom).absStore
    
and expBornesToListeAffect expBornes =
    let rec aux res = function
      	Doc subtree -> List.fold_left aux res subtree
  	| Function (x, subtree) ->  List.fold_left aux res subtree
  	| Call (x, subtree) -> List.fold_left aux res subtree
  	| Loop ((id, line, source, exact, max, total, expMax, expTotal, expinit, sens,et, ef), subtree) -> 
	  (new_instVar (sprintf "max-%d" id) (EXP expMax))::(new_instVar (sprintf "total-%d" id) (EXP expTotal))::(List.fold_left aux res subtree)
	in
    aux [] expBornes 

and getInstListFromPartial partialResult = 
    List.append (expBornesToListeAffect partialResult.expBornes) (listeAsToListeAffect partialResult.absStore)
    

and traiterAppelFonction exp args init ida =
      let nom = nomFonctionDeExp exp in (* il faut construire la liste d es entrées et la liste des sorties*)
      (*Printf.printf "La fonction: %s existe=%b \n" nom (existeFonction nom);*)

      if ((existeFonction nom) && (not (is_in_use_partial nom))) then 
	  (	
		let (_, f) = rechercheFonction nom in
		if f.lesAffectations = [] then   aUneFctNotDEf := true;
		entrees := [];
		sorties := [];
		(*Printf.printf "construireListesES La fonction: %s existe=%b \n" nom (existeFonction nom);*)
		construireListesES f.listeES args;

		(*Printf.printf "ap construireListesES La fonction: %s existe=%b \n" nom (existeFonction nom);*)
		ajouterReturn nom f.lesAffectations;
		(*Printf.printf "La fonction: %s existe=%b NEW APPEL \n" nom (existeFonction nom);*)
		listeDesInstCourantes :=  
			List.append init [new_instAPPEL ida (new_instBEGIN !entrees) nom (new_instBEGIN !sorties) (new_instBEGIN f.lesAffectations) ""];
			false
	 ) 
	 else 
	 (
		entrees := [];
		sorties := [];
		try 
		(
			let (absStore,listeES) = (getAbsStoreFromComp nom),(getESFromComp nom) in
			(*Printf.printf "Il y a %u variables E/S" (List.length listeES);*)
			construireListesES listeES args;	  
			(*Printf.printf "Ici on construit le noeud d'appel du composant: %s %d\n" nom ida;*)
			listeDesInstCourantes :=   List.append init[ new_instAPPELCOMP ida  (new_instBEGIN !entrees)  nom (new_instBEGIN !sorties)  absStore ""]; 
			true
		) 
		with  Unix.Unix_error(Unix.ENOENT, _, _)-> 
			aUneFctNotDEf := true; 
			(*Printf.printf "La fonction: %s existe pas=%b NEW APPEL NON 2\n" nom (existeFonction nom);*)
          	listeDesInstCourantes :=  List.append init[new_instAPPEL ida (new_instBEGIN !entrees) nom (new_instBEGIN !sorties) (new_instBEGIN []) ""];false
        	| Unix.Unix_error (x,y,z) -> aUneFctNotDEf := true; 
				listeDesInstCourantes :=  List.append init [new_instAPPEL ida (new_instBEGIN !entrees) nom (new_instBEGIN !sorties) (new_instBEGIN []) ""];
           		(* Printf.eprintf "%s: %s %s\n%!" y (Unix.error_message x) z;*)
           		 false
	)


(* for variables *)
and analyse_defs defs =    
 List.iter	(fun def ->		analyse_def def)		defs

and analyse_def def =
	match def with
	FUNDEF (proto, body)                 ->	 	

(*let (_ , _ , fct )=proto in
		let (nom,_,_,_) =fct in 
		(*let fonction = rechercheFonction nom in*)
		Printf.printf "dans analyse_def  %s\n" nom ;*)
		estGlobale := false;
		let listeBoucleOuAppelPred = !listeBoucleOuAppelCourante in
		listeBoucleOuAppelCourante := [];
		majFonctionDansDocument proto body 		;
		estGlobale := true;
		listeBoucleOuAppelCourante := listeBoucleOuAppelPred;(*Printf.printf "fin dans analyse_def  %s\n" nom ;*)	()
	| OLDFUNDEF (proto, (*decs*)_, body) -> 	
(*let (_ , _ , fct )=proto in*)
		(*let (nom,_,_,_) =fct in *)
		(*let fonction = rechercheFonction nom in*)
		(*Printf.printf "dans analyse_def  %s\n" nom ;*)
		estGlobale := false; 
		let listeBoucleOuAppelPred = !listeBoucleOuAppelCourante in
		listeBoucleOuAppelCourante := [];
		majFonctionDansDocument proto body ;
		estGlobale := true;
		listeBoucleOuAppelCourante := listeBoucleOuAppelPred	;(*Printf.printf "fin dans analyse_def  %s\n" nom ;*)	()
	| DECDEF (n) -> (*TRAITERPTR*)
			let listPred = !listeDesInstCourantes in
			listeDesInstCourantes := [];
			let (typ, sto, namelist) = n in 
			(*print_type (fun _ -> ()) typ; new_line();*)
			(*print_base_type typ; new_line();*)
			(*if estProto typ then  Printf.printf "is proto\n" else  Printf.printf "is not proto\n" ;*)

		(*	let bbtype = get_base_type typ in*)
			let isPtr = if estProto typ =false then isPtrType typ  else   false  in
			if estProto typ =false then   (* déclaration de variable*) varDefList  typ namelist isPtr;

				enumCour := NO_TYPE;
			let baseType = match  get_base_typeEPS  typ  with TYPEDEF_NAME(id) -> id |_-> "" in
(*| ENUM (id, items) -> print_enum id items*)
			let (isTypeDefTab, size ) =
				if baseType <> "" && existAssosTypeDefArrayIDsize baseType then
				begin
					 (true,(getAssosTypeDefArrayIDsize baseType)) 
				end
				else (false, NOSIZE) in

			let (estDejaDecl, eststatic,estChar) = 
				(	match sto with 				
					STATIC-> 
							if namelist <> [] then 
							begin
								let (id,_,_,exp) = (List.hd namelist) in
								if List.mem id !alreadyAffectedGlobales then   (true, true, isCharType typ) 
								else (false, true,isCharType typ)  
							end
							else (false , true,isCharType typ)
					|_-> (false, false, isCharType typ) )in
			if namelist <> [] then	
			List.iter  
			(fun name -> 
				let (id,typ, _, exp) = name in
				(*Printf.printf "id : %s \n" id;*)

				let (isArray,dim) = 
					(match typ with
						ARRAY (t, dim) -> majAssosArrayIDsize id typ exp; (* a cause des renommages je pense que cela suffit*)
							(match calculer  (EXP(dim)) !infoaffichNull  [] 1 with ConstInt(s)-> (true,(int_of_string  s)) |_->(true,0))
						
						|_ -> if isTypeDefTab then setAssosArrayIDsize id size; (false,0)) in
						
				if exp <> NOTHING ||( eststatic && estDejaDecl = false) (*|| !estGlobale*)  then 
				begin
					if isArray = false then begin analyse_expression (BINARY(ASSIGN,VARIABLE(id),exp)) end
								(*else  creerInitTab id 0 (dim-1) exp estChar*)
				end	;
			
				if !estGlobale || eststatic then  if List.mem id !alreadyAffectedGlobales = false then 
					alreadyAffectedGlobales:=List.append [id] !alreadyAffectedGlobales
				
			) namelist;
			consEnum !enumCour; 
			if estDejaDecl then begin listeDesInstCourantes := listPred; consEnum !enumCour end
			else if eststatic =false then listeDesInstCourantes := List.append listPred !listeDesInstCourantes 
				 else if !estGlobale = false  && estDejaDecl = false then
					  begin
							listeDesInstGlobales := List.append !listeDesInstGlobales !listeDesInstCourantes;
							listeDesInstCourantes := listPred
					  end ;

			if !estGlobale  then 
		 	begin
					listeDesInstGlobales := List.append !listeDesInstGlobales !listeDesInstCourantes;
					listeDesInstCourantes := listPred
			end ;
(*Printf.printf "fin dans analyse_def  DECDEF\n"  ;	*)
			()
	| TYPEDEF (n, _) -> 	
		let (typi, sto, namelist) = n in 
		List.iter  (fun name ->
					let (id,typ, _, exp) = name in   
					match typ with ARRAY (t, dim) -> majTypeDefAssosArrayIDsize id typ exp; () |ENUM(_,_)->consEnum typ;()
									 |_->let base = get_base_type typi in 
											(match base with ENUM(_,_) ->consEnum  base ;()|_->());()
					) namelist; ;
		
		()
	| ONLYTYPEDEF n -> 
		let (typ, sto, namelist) = n in 
		List.iter  (fun name -> 
					let (id,typ, _, exp) = name in  
					match typ with ARRAY (t, dim) -> majTypeDefAssosArrayIDsize id typ exp; () |ENUM(_,_)->consEnum typ;|_->()
					) namelist;
		
		()	

	
(*	*)		
and isCharType typ =
match typ with  CHAR _ -> true | _->false

and stringOfStringCst cst =  match cst with  CONST_STRING s -> s | _ ->""
and aggreListOfCstCOMPOUND cst = match cst with  CONST_COMPOUND s ->(*Printf.printf"counpound\n";*) s | _ ->[]
and cteOfexp exp = match exp with  CONSTANT cst -> ( cst , true) | _ ->(CONST_STRING "", false)


and creerInitTab id min max exp estChar=
	let index = INDEX (VARIABLE(id), CONSTANT(CONST_INT(Printf.sprintf "%d"  min))) in
	let (cte, iscst) = cteOfexp exp in

	if min <= max then
	begin
		if estChar then
		begin
			let charcst = (stringOfStringCst  cte) in
			let lg = (String.length charcst -1) in
			let (curChar, others) =  	
					if iscst = false then (NOTHING , NOTHING)
					else if charcst = "" then (NOTHING, NOTHING)
						 else if lg = 1 then (CONSTANT(CONST_CHAR(String.sub charcst 0 1)),NOTHING)
							  else	 (CONSTANT(CONST_CHAR(String.sub charcst 0 1)), CONSTANT(CONST_STRING(String.sub charcst 1 lg))) in
			analyse_expression (BINARY(ASSIGN,index, curChar));
			creerInitTab id (min+1) max others estChar
		end
		else
		begin
			let(tete, suite) =
				(if iscst = false then (NOTHING, NOTHING)
				else
				begin
					let cteCOMPOUND =   aggreListOfCstCOMPOUND cte in
					let autres = (List.tl cteCOMPOUND) in
					if autres = [] then (List.hd cteCOMPOUND,  NOTHING ) else (List.hd cteCOMPOUND,  CONSTANT(CONST_COMPOUND autres) )
				
				end )in
				analyse_expression (BINARY(ASSIGN,index,tete));
				creerInitTab id (min+1) max suite estChar
		end
	end
				
and majFonctionDansDocument proto body =
let listeP = !listeDesInstCourantes in
	 listeDesInstCourantes := [];
	let (_ , _ , fct )=proto in
	let (nom,_,_,_) =fct in 
	let nomPred = !nomFctCour in
    nomFctCour := nom;
	 let (decs, stat) = body in analyse_statement (BLOCK (decs, stat));
	 nomFctCour := nomPred;
	 listeDesInstCourantes := [ new_instBEGIN  !listeDesInstCourantes];
		let res = majAuxFct  []  !doc.laListeDesFonctions nom  in
		doc := new_document !doc.laListeDesBoucles   res !doc.laListeDesAssosBoucleBorne !doc.laListeDesNids;
listeDesInstCourantes:= listeP

and  onlyAstatement   stat =
	match stat with
	NOP -> 						()
	| COMPUTATION exp ->		onlyAexpression  exp 
	| BLOCK (defs, stat) ->			
		let listePred = !listeDesInstCourantes in	
		listeDesInstCourantes := [];
		onlyAdefs  defs ;
		if stat <> NOP then onlyAstatement  stat ;
		listeDesInstCourantes :=  List.append listePred  !listeDesInstCourantes 

	| SEQUENCE (s1, s2) ->			
		let listePred = !listeDesInstCourantes in	
		listeDesInstCourantes := [];
		onlyAstatement   s1;
		let listePred2 = List.append listePred  !listeDesInstCourantes in		
		listeDesInstCourantes := [];
		onlyAstatement   s2;
		listeDesInstCourantes :=List.append listePred2  !listeDesInstCourantes 
											
	| IF (exp, s1, s2) ->			
		
		onlyAexpression   exp ;	 
		let listePred = !listeDesInstCourantes in	
		listeDesInstCourantes := [];
		onlyAstatement  s1;
		if (s2 = NOP)	then 
			listeDesInstCourantes :=  List.append listePred  [ new_instIFV (EXP(exp)) (new_instBEGIN (!listeDesInstCourantes)) ]
		else 	
		begin
			let listeVrai = !listeDesInstCourantes in
			listeDesInstCourantes := [];
			onlyAstatement  s2;													
			listeDesInstCourantes := 
				List.append  listePred  [new_instIFVF (EXP(exp)) (new_instBEGIN (listeVrai))  (new_instBEGIN (!listeDesInstCourantes)) ]
		end
												
	| WHILE (exp, stat) ->  	(*analyse_expression  exp ;rien condition sans effet de bord*)	
		listeNextExp := [];
		
		onlyAexpressionaux   exp ;
		let listePred = !listeDesInstCourantes in
		listeDesInstCourantes := !listeNextExp;																	
		onlyAstatement  stat;
		listeNextExp := [];
		
		onlyAexpressionaux   exp ;
		listeDesInstCourantes :=  List.append ( List.append listePred [ (new_instBEGIN (!listeDesInstCourantes ))]) !listeNextExp;
									
	| DOWHILE (exp, stat) ->			
		let listePred = !listeDesInstCourantes in
		listeDesInstCourantes := [];																	
		onlyAstatement  stat;
		onlyAexpression   exp ;
		listeDesInstCourantes :=   List.append listePred [ (new_instBEGIN (!listeDesInstCourantes ))];

	| FOR (exp1, exp2, exp3, stat) ->
		onlyAexpression  exp1;
		listeNextExp := [];
		onlyAexpressionaux  exp2;
		let listePred = !listeDesInstCourantes in
		listeDesInstCourantes := !listeNextExp;																	
		onlyAstatement  stat;
		onlyAexpression   exp3 ;
		listeNextExp := [];
		onlyAexpressionaux  exp2;
		listeDesInstCourantes :=  List.append ( List.append listePred [ (new_instBEGIN (!listeDesInstCourantes ))]) !listeNextExp;
	
	| BREAK | CONTINUE -> 			()
	| RETURN (exp) ->				if exp = NOTHING	then ()	else 
									begin
										listeNextExp := [];
										onlyAexpressionaux  exp ;
										let ne = !nouvExp in
										let nouvarres = Printf.sprintf "res-%s" !nomFctCour  in
										let newaffect = new_instVar  (nouvarres)  (EXP(ne))in
										listeDesInstCourantes :=  List.append ( List.append !listeDesInstCourantes  [newaffect]) !listeNextExp
									end
	| SWITCH (exp, stat) ->			
									onlyAexpression   exp ;


									let ne = !nouvExp in   
									idSwitch := !idSwitch + 1;
									let varIfNaux =  Printf.sprintf "%s-%d" "SW" !idSwitch  in	 
									let newaffect =new_instVar  varIfNaux  (EXP(ne)) in 
									listeDesInstCourantes := List.append !listeDesInstCourantes  [newaffect]; 

									listOfCase := [];

									let listOfStat = listeSwitchStatement  stat in
									analyseSwitchStatement stat varIfNaux listOfStat;

									(*let newStatement = buildSwitchStatement !listOfCase !listOfDefault in*)
									(*let isPred = !isIntoSwithch in*)
									(*isIntoSwithch := true;*)
									onlyAstatement    stat (* à traiter *);
									(*isIntoSwithch := isPred*)


	| CASE (exp, stat) ->			onlyAexpression   exp ;
									onlyAstatement    stat (* a traiter *);
									
	| DEFAULT stat ->				onlyAstatement    stat
	| LABEL ((*name*)_, stat) ->	onlyAstatement    stat
	| _-> 	()

and onlyAexpression exp =
listeNextExp := [];
onlyAexpressionaux exp ;
listeDesInstCourantes := List.append !listeDesInstCourantes !listeNextExp
											

and  onlyAexpressionaux exp =
	 match exp with
		NOTHING -> 				nouvExp := exp	
	| 	UNARY (op, e) -> 	
			
			(match op with		(*je ne distingue pas pre et post operation linearise*)
				PREINCR -> onlyAexpression e;	 affectationUnaire ADD !nouvExp
				| POSDECR ->  onlyAexpression e;	
					let p = !listeDesInstCourantes in
								listeDesInstCourantes := [];
								affectationUnaire SUB e ;
								listeNextExp :=  List.append !listeNextExp !listeDesInstCourantes;
								listeDesInstCourantes := p;
	
				| POSINCR -> onlyAexpression e;	 
								let p = !listeDesInstCourantes in
								listeDesInstCourantes := [];
								affectationUnaire ADD e ;
								listeNextExp :=  List.append !listeNextExp !listeDesInstCourantes;
								listeDesInstCourantes := p;
				| PREDECR -> onlyAexpression e;	  affectationUnaire SUB !nouvExp;
				
				| ADDROF	->(** "&" . nouvExp :=VARIABLE("&"^v)*)
					(match e with
						INDEX (t,i)->
(* Printf.printf "adresse de...\n"; print_expression e 0; new_line();*)
							let (tab,lidx) = analyseArray e []  in
							if tab = "" then nouvExp := exp
							else 
							begin
(*								let sygmaIndex = getSygma lidx in*)
											
								(*let sygmaIndex = (*(CONSTANT(CONST_INT("0"))) in*)
										if lidx = [] then NOTHING else if (List.tl lidx) = [] then (CONSTANT(CONST_INT("0"))) else  i in*)
							    let sygmaIndex = (*(CONSTANT(CONST_INT("0"))) in*)
										if lidx = [] then (*NOTHING else if (List.tl lidx) = [] then *)(CONSTANT(CONST_INT("0"))) else if (List.tl lidx) = [] then i else NOTHING in
								nouvExp := UNARY(ADDROF,BINARY (ADD, (VARIABLE(tab)), sygmaIndex)) ;
(*print_expression !nouvExp 0; new_line(); Printf.printf "adresse de...\n";*)
							end
						| _->

						nouvExp :=exp)
	
				| _->  if !vDEBUG then  Printf.printf "expression pour tableau avec nom tab pas variable non encore traité\n" ;
						onlyAexpression e;	nouvExp := UNARY (op, !nouvExp)
			)

	| BINARY (op, exp1, exp2) -> 
		onlyAexpression exp1 ;
		let ne1 = !nouvExp in 	
		onlyAexpression exp2;	
		let ne = !nouvExp in   
		(	match op with		
			ASSIGN		->
			(	match exp1 with
				VARIABLE n ->   
					listeDesInstCourantes := List.append !listeDesInstCourantes  [new_instVar  n  (EXP(ne))]
				|INDEX (t,i)-> 
					( match t with 
						VARIABLE v -> listeDesInstCourantes := List.append !listeDesInstCourantes  [new_instTab v (EXP(i))	(EXP(ne))]
						| UNARY (opr,e) ->
						(
							match e with
							VARIABLE v ->
							(
								match opr with
								MEMOF		-> 
										listeDesInstCourantes := List.append !listeDesInstCourantes 
																		[new_instMem ("*"^v) (EXP(VARIABLE(v))) (EXP(ne))]

								| ADDROF	->  
									listeDesInstCourantes := List.append !listeDesInstCourantes  [new_instTab ("&"^v) (EXP(i))	(EXP(ne))]
								|  _->	 if !vDEBUG then  Printf.printf "expr pour tableau  non traitée\n" ;
							)
							| _->  if !vDEBUG then  Printf.printf "expr pour tableau  non traitée\n" 
						)
						| _->	 if !vDEBUG then  Printf.printf "expr pour tableau  non traitée\n" 	
					)
				| UNARY (opr,e) -> 
					(
						match e with
						VARIABLE v ->
						(
							match opr with
							MEMOF		->(* * operator *)
										listeDesInstCourantes := List.append !listeDesInstCourantes 
																		[new_instMem ("*"^v) (EXP(VARIABLE(v))) (EXP(ne))]
							| ADDROF	->(* & operator *) listeDesInstCourantes := List.append !listeDesInstCourantes [new_instVar ("&"^v) (EXP(ne))]
							|  _->	 if !vDEBUG then Printf.printf "expr pour tableau  non traitée\n" 	
						)
						| _->	 if !vDEBUG then Printf.printf "expr pour tableau  non traitée\n" 	 	
					) 
				 |_-> if !vDEBUG then Printf.printf "expr pour tableau  non traitée\n" 		 
			); 	
			| ADD_ASSIGN	-> affectationBinaire ADD exp1 ne;  nouvExp:=BINARY (op, exp1, ne) 
			| SUB_ASSIGN	-> affectationBinaire SUB exp1 ne;  nouvExp:=BINARY (op, exp1, ne) 
			| MUL_ASSIGN	-> affectationBinaire MUL exp1 ne ; nouvExp:=BINARY (op, exp1, ne) 
			| DIV_ASSIGN	-> affectationBinaire DIV exp1 ne ; nouvExp:=BINARY (op, exp1, ne) 
			| MOD_ASSIGN	-> affectationBinaire MOD exp1 ne ; nouvExp:=BINARY (op, exp1, ne) 
			| BAND_ASSIGN	-> affectationBinaire BAND exp1 ne; nouvExp:=BINARY (op, exp1, ne) 
			| BOR_ASSIGN	-> affectationBinaire BOR exp1 ne ; nouvExp:=BINARY (op, exp1, ne) 
			| XOR_ASSIGN	-> affectationBinaire XOR exp1 ne ; nouvExp:=BINARY (op, exp1, ne) 
			| SHL_ASSIGN	-> affectationBinaire SHL exp1 ne ; nouvExp:=BINARY (op, exp1, ne) 
			| SHR_ASSIGN	-> affectationBinaire SHR exp1 ne ; nouvExp:=BINARY (op, exp1, ne) 
			| _ -> nouvExp:=BINARY (op, ne1, ne) 
		)
	| QUESTION (exp1, exp2, exp3) ->
				onlyAexpression exp1 ;
				let ne1 = !nouvExp in
				onlyAexpression exp2;
				let ne2 = !nouvExp in
				onlyAexpression exp3;
				let ne3 = !nouvExp in 
    			nouvExp:=QUESTION (ne1, ne2, ne3)
																					
	| CAST (t, e) 		 ->  onlyAexpression e ; nouvExp:=CAST (t, !nouvExp) 
	| CALL (e , args) 				->		
				(* List.iter (fun ep -> onlyAexpression ep) args; *)
				let listeInstPred = !listeDesInstCourantes in 								
				if existeFonction (nomFonctionDeExp e) && (not (is_in_use_partial (nomFonctionDeExp e))) then 
				begin
					let fonction = rechercheFonction (nomFonctionDeExp e) in
					let (_, f) = fonction in
					listeDesInstCourantes := [];
					construireAsAppelAux f.declaration	exp ;(*pb si arg est un appel de fonction revoir*)
					let _ = onlytraiterAF e args !listeDesInstCourantes in
					
					let nouvar = Printf.sprintf "call-%s%d" (nomFonctionDeExp e) 0 in
					let nouvarres = Printf.sprintf "res-%s" (nomFonctionDeExp e) in
					let newaffect = new_instVar  (nouvar)  (EXP(VARIABLE(nouvarres))) in
					listeDesInstCourantes :=  List.append !listeDesInstCourantes  [newaffect];
					listeDesInstCourantes :=  List.append listeInstPred !listeDesInstCourantes ;
					nouvExp:=VARIABLE(nouvar)
				end
				else
				begin 
					listeDesInstCourantes := [];
					List.iter (fun ep -> analyse_expressionaux ep) args;
			
					
					let isComponant =  onlytraiterAF e args !listeDesInstCourantes in
					let nouvar = Printf.sprintf "call-%s%d" (nomFonctionDeExp e) 0 in
					let nouvarres = Printf.sprintf "res-%s" (nomFonctionDeExp e) in
					let newaffect = new_instVar  (nouvar)  (EXP(VARIABLE(nouvarres))) in
					listeDesInstCourantes :=  List.append !listeDesInstCourantes  [newaffect];
					listeDesInstCourantes :=  List.append listeInstPred !listeDesInstCourantes ;
					if isComponant then nouvExp:=VARIABLE(nouvar) else nouvExp:=exp
				end	


		

			 
	| COMMA e 				->    List.iter (fun ep -> onlyAexpression ep) e; nouvExp:=COMMA(e)
	| MEMBEROF (e , t) 		
	| MEMBEROFPTR (e , t) 	->		onlyAexpression e ; nouvExp:=exp
	| EXPR_SIZEOF exp ->
		onlyAexpression exp ;
		( match !nouvExp with
			VARIABLE (v) ->  
							if (List.mem_assoc v !listeAssosPtrNameType) then nouvExp:=VARIABLE( "SIZEOF_PTR")
							else if (List.mem_assoc v !listAssosArrayIDsize) then
								 begin
									let size = getAssosArrayIDsize v in
									let typeElem = if existAssosArrayType v   then (get_baseinittype (getAssosAssosArrayType v ))
									else "SIZEOF_elementsOf"  ^ v ^"ARRAY" in
									(match size with
										NOSIZE -> if (List.mem_assoc v !listeAssosPtrNameType) then nouvExp:=VARIABLE( "SIZEOF_PTR")
												  else nouvExp:= BINARY(MUL,VARIABLE( "SIZEOF_"^v^"ELT_NUMBER"),  
																			VARIABLE( "SIZEOF_" ^ typeElem))
										| SARRAY (taille) -> nouvExp:= BINARY(MUL, CONSTANT(CONST_INT (Printf.sprintf "%d" taille)),  
																			VARIABLE( "SIZEOF_" ^ typeElem))
										| MSARRAY (lsize) -> let tsize = expressionEvalueeToExpression (prodListSize lsize) in
															nouvExp:= BINARY(MUL,  tsize,  
																			VARIABLE( "SIZEOF_" ^ typeElem))
									)
								 end
								 else if List.mem_assoc v !setAssosIDTYPEINIT then 
											nouvExp:=VARIABLE( "SIZEOF_"  ^ (get_baseinittype (List.assoc v !setAssosIDTYPEINIT)))
										else nouvExp:=EXPR_SIZEOF !nouvExp
			| INDEX (e, idx) ->  		
				let (tab,lidx) = analyseArray  ( !nouvExp) []  in
		
				if tab = "" then nouvExp:=EXPR_SIZEOF !nouvExp
				else 
				begin
					if (List.mem_assoc tab !listAssosArrayIDsize) then
								 begin
									let size = getAssosArrayIDsize tab in
									let typeElem = if existAssosArrayType tab  then (get_baseinittype (getAssosAssosArrayType tab ))
									else "SIZEOF_elementsOf"  ^ tab ^"ARRAY" in
									(match size with
										NOSIZE -> if (List.mem_assoc tab !listeAssosPtrNameType) then nouvExp:=VARIABLE( "SIZEOF_PTR")
												  else nouvExp:= BINARY(MUL,VARIABLE( "SIZEOF_"^tab^"ELT_NUMBER"),  
																			VARIABLE( "SIZEOF_" ^ typeElem))
										| SARRAY (taille) -> nouvExp:= BINARY(MUL, CONSTANT(CONST_INT (Printf.sprintf "%d" taille)),  
																			VARIABLE( "SIZEOF_" ^ typeElem))
										| MSARRAY (lsize) -> let tsize = expressionEvalueeToExpression (prodListSize lsize) in
															nouvExp:= BINARY(MUL, tsize,  
																			VARIABLE( "SIZEOF_" ^ typeElem))
									)
								 end
				end
			|UNARY (MEMOF,VARIABLE (v)) ->  
							if (List.mem_assoc v !listeAssosPtrNameType) then nouvExp:=VARIABLE( "SIZEOF_PTR")
							else if (List.mem_assoc v !listAssosArrayIDsize) then
								 begin 
									let typeElem = if existAssosArrayType v   then (get_baseinittype (getAssosAssosArrayType v ))
									else "SIZEOF_elementsOf"  ^ v ^"ARRAY" in
									nouvExp:=  VARIABLE( "SIZEOF_" ^ typeElem)
								 end
								 else   nouvExp:=EXPR_SIZEOF !nouvExp
			|_->  nouvExp:=EXPR_SIZEOF !nouvExp
		);
			 					
			(*print_expression !nouvExp 0;new_line () ;flush(); space();*)
				
	| TYPE_SIZEOF typ ->
			nouvExp:=VARIABLE( "SIZEOF_"  ^ (get_baseinittype typ));
 					
			(*print_expression !nouvExp 0;new_line () ;flush(); space();*)
	| GNU_BODY (decs, stat) -> 	
			let listePred = !listeDesInstCourantes in
			listeDesInstCourantes := [];
			onlyAstatement   (BLOCK (decs, stat));
			listeDesInstCourantes := 	[new_instBEGIN  !listeDesInstCourantes];
			listeDesInstCourantes :=    List.append listePred  !listeDesInstCourantes 	;
			nouvExp:=GNU_BODY (decs, stat)
	|	CONSTANT cst ->
							(match cst with 
								CONST_COMPOUND expsc ->  (*Printf.printf "applystore MEMBEROFPTR lid non vide  assigncomma\n" ;*)
									nouvExp:=CONSTANT(CONST_COMPOUND(convaelaux  expsc));
	 								(*Printf.printf "new costant\n";print_expression exp 0; new_line() ;	
									print_expression !nouvExp 0; new_line(); Printf.printf "adresse de...constant\n";*)
								|_->nouvExp:=exp	
							)
	| _->nouvExp:=exp;


and convaelaux l =
if l = [] then []
else
begin
onlyAexpression (List.hd l);
let n = !nouvExp in
List.append [n] (convaelaux  (List.tl l)  )
end

and contruireAuxAux par args	=
	if par = [] || args = [] then ()
	else
	begin
		onlyAexpression (BINARY(ASSIGN, VARIABLE(List.hd(par)), List.hd(args)));
		contruireAuxAux (List.tl par) (List.tl args)
	end			
																
and  construireAsAppelAux dec	appel =
 	let (_, _, name) = dec in 
 	let (_, typep, _, _) = name in
 	let base = get_base_type typep in
 	let liste =
		(match base with
			PROTO (_, pars, _) -> List.map( fun pc -> let (_, _, n) = pc in let (id, _, _, _) = n in id)  pars 
			| OLD_PROTO (_, pars, _) ->	pars 
			| _ -> []) in	
 	match appel with
	 	CALL (_, args) ->	contruireAuxAux liste args | _-> ()


and onlytraiterAF exp args init =
let nom = nomFonctionDeExp exp in
let r = !idAppel in
	if ((existeFonction nom) && (not (is_in_use_partial nom))) then
	begin
		let fonction = rechercheFonction nom in
		let (_, f) = fonction in
		let proto = f.declaration in
		
		let aff =
			if f.lesAffectations = [] then 
			begin


				let nfc = !nomFctCour in
				let a = !listeDesInstCourantes in
				listeDesInstCourantes := [];		
				let m = !listeASCourant in
				listeASCourant := [];	 
			     let res =
					match (getCorpsFonction f).corpsS with  BLOCK (decs, stat) ->	onlyanalysedef (FUNDEF (proto, (decs, stat)));!listeDesInstCourantes 
					|_->[] in

				listeDesInstCourantes := a;
				listeASCourant := m;
				nomFctCour := nfc;
				res (*f.lesAffectations*)
			end 
			else f.lesAffectations in 
			
		entrees := init;
		sorties := [];
		construireListesES f.listeES args;
		ajouterReturn nom aff;
(*Printf.printf "La fonction: %s existe=%b NEW APPEL ONLY\n" nom (existeFonction nom);*)
		listeDesInstCourantes :=   List.append init [ new_instAPPEL r  (new_instBEGIN !entrees)  f.nom (new_instBEGIN !sorties) (new_instBEGIN aff) ""];
	    false
	end
	else (
	
		entrees := init;
		sorties := [];
    	
		
		try (

				let nfc = !nomFctCour in
				 
				listeDesInstCourantes := [];		
				let m = !listeASCourant in
				listeASCourant := [];		

				let (absStore,listeES) = (getAbsStoreFromComp nom),(getESFromComp nom) in
				
				(*Printf.printf "Il y a %u variables E/S" (List.length listeES);*)
				construireListesES listeES args;	  
				 
				listeASCourant := m;
				nomFctCour := nfc;

				(*Printf.printf "Ici on construit le noeud d'appel du composant: %s ONLY\n" nom;*)
(*Printf.printf "La fonction: %s existe=%b NEW APPEL COMPO \n" nom (existeFonction nom);*)
				listeDesInstCourantes :=  List.append init [ new_instAPPELCOMP r  (new_instBEGIN !entrees)  nom (new_instBEGIN !sorties)  absStore ""]; true
		) 
		with  Unix.Unix_error(Unix.ENOENT, _, _)-> 
			(*aUneFctNotDEf := true; *)
(*Printf.printf "La fonction: %s existe=%b NEW APPEL NON ONLY \n" nom (existeFonction nom);*)
          	listeDesInstCourantes :=  List.append init [ new_instAPPEL r  (new_instBEGIN !entrees)  nom (new_instBEGIN !sorties)  (new_instBEGIN []) ""];false
        	| Unix.Unix_error (x,y,z) -> 
           		 Printf.eprintf "%s: %s %s\n%!" y (Unix.error_message x) z;
           		 false

			
	  
	)








and onlyAdefs defs = List.iter	(fun def ->		onlyanalysedef def)		defs


and consListeEnum l valeur =
if l = [] then ()
else
begin
	let ((n,exp), suite) = (List.hd l, List.tl l) in
(*Printf.printf "ENUM %s \n" n;print_expression exp 0; space();flush();new_line();*)
	if exp = NOTHING then 
	begin
		
		let ne =(BINARY(ASSIGN,VARIABLE(n), CONSTANT( CONST_INT (Printf.sprintf "%d" valeur)))) in
		analyse_expression ne;
 
		consListeEnum suite (valeur+1);()
	end
	else 
	begin
		analyse_expression (BINARY(ASSIGN,VARIABLE(n), exp));
		let nval = calculer  (EXP(exp)) !infoaffichNull  [] 1 in
		let nextvat = 
			match nval with 
	 			ConstInt (i)-> (int_of_string  i) +1
			|_-> (valeur+1) in
		let ne =(BINARY(ASSIGN,VARIABLE(n), CONSTANT( CONST_INT (Printf.sprintf "%d" nextvat)))) in
		analyse_expression ne;
 
		consListeEnum suite (nextvat+1)
	end;()
end

and  	consEnum enumCour =
match enumCour with
	
	 ENUM (_, items) -> (*match items with COMMA(l) ->consListeEnum l 0 |_->()*) consListeEnum items 0

|_->()

and onlyanalysedef def =
	match def with
	FUNDEF (proto, body)                 ->	 	
		let (_ , _ , fct )=proto in
		let (nom,_,_,_) =fct in 
	(*	let fonction = rechercheFonction nom in*)
		let listeP = !listeDesInstCourantes in
		(*Printf.printf "dans onlyanalysedef liste affect vide %s %s\n" nom !nomFctCour;*)
			let gp = !estGlobale in
			estGlobale := false;
			listeDesInstCourantes := [];
			let nomPred = !nomFctCour in
			nomFctCour := nom;
			let (decs, stat) = body in onlyAstatement (BLOCK (decs, stat));
			nomFctCour := nomPred;
			listeDesInstCourantes := [ new_instBEGIN  !listeDesInstCourantes];
			estGlobale := gp;
		listeDesInstCourantes:= listeP;
		()
		
	| OLDFUNDEF (proto, (*decs*)_, body) -> 	
		let (_ , _ , fct )=proto in
		let (nom,_,_,_) =fct in 
		(*let fonction = rechercheFonction nom in*)
		let listeP = !listeDesInstCourantes in
			(*Printf.printf "dans onlyanalysedef liste affect vide %s %s\n" nom !nomFctCour;*)
			let gp = !estGlobale in
			estGlobale := false;
			listeDesInstCourantes := [];
			let nomPred = !nomFctCour in
			nomFctCour := nom;
			let (decs, stat) = body in onlyAstatement (BLOCK (decs, stat));
			nomFctCour := nomPred;
			listeDesInstCourantes := [ new_instBEGIN  !listeDesInstCourantes];
			estGlobale := gp;
			listeDesInstCourantes:= listeP;
			()

	| DECDEF (n) -> 
			let listPred = !listeDesInstCourantes in
			listeDesInstCourantes := [];
			let (typ, sto, namelist) = n in 
			(*print_type (fun _ -> ()) typ; new_line();*)
			(*print_base_type typ; new_line();*)
			(*if estProto typ then  Printf.printf "is proto\n" else  Printf.printf "is not proto\n" ;*)
			(*let bbtype = get_base_type typ in*)
			let isPtr = if estProto typ =false then  isPtrType typ else  (*Printf.printf "is proto\n";*) false  in

			if estProto typ =false then   (* déclaration de variable*) varDefList  typ namelist isPtr;

			enumCour := NO_TYPE;
			let baseType = match  get_base_typeEPS  typ  with TYPEDEF_NAME(id) -> id |_-> "" in
			 
			consEnum !enumCour; 
			let (isTypeDefTab, size ) =
				if baseType <> "" && existAssosTypeDefArrayIDsize baseType then  (true,(getAssosTypeDefArrayIDsize baseType)) 
				else (false, NOSIZE) in


			let (estDejaDecl, eststatic) = 
				(	match sto with 				
					STATIC-> 
							if namelist <> [] then 
							begin
								let (id,_,_,exp) = (List.hd namelist) in
								listeASCourant := [];(*static id *)
								let glo = evalStore 	(new_instBEGIN !listeDesInstGlobales) [] []	in
								if (existeAffectationVarListe id glo) then  (true, true)
								else (false, true) 
							end
							else (false , true)
					|_-> (false, false) )in

			if namelist <> [] then	
			List.iter  (fun name -> 
					let (id,typ, _, exp) = name in
					
					
					let (isArray,dim) = 
						(match typ with
							ARRAY (t, dim) -> majAssosArrayIDsize id typ exp; (* a cause des renommages je pense que cela suffit*)
								(match calculer  (EXP(dim)) !infoaffichNull  [] 1 with ConstInt(s)-> (true,(int_of_string  s)) |_->(true,0))
							|_ -> if isTypeDefTab then setAssosArrayIDsize id size; (false,0)) in
							
							if exp <> NOTHING ||( eststatic && estDejaDecl = false) then 
							begin
								if isArray = false then onlyAexpression(BINARY(ASSIGN,VARIABLE(id),exp));
(*Printf.printf "id : %s \n" id; print_expression exp 0;new_line();*) (*else  creerInitTab id 0 (dim-1) exp estChar*)
							end	
						) namelist;
			
			if estDejaDecl then begin listeDesInstCourantes := listPred;consEnum !enumCour end
			else if eststatic =false then listeDesInstCourantes := List.append listPred !listeDesInstCourantes 
				 else if !estGlobale = false  && estDejaDecl = false then
					  begin
							listeDesInstGlobales := List.append !listeDesInstGlobales !listeDesInstCourantes;
							listeDesInstCourantes := listPred
					  end ;
			()

	|TYPEDEF (n, _) -> 		let (typei, sto, namelist) = n in 
		List.iter  (fun name -> 
					let (id,typ, _, exp) = name in
					match typ with ARRAY (t, dim) -> majTypeDefAssosArrayIDsize id typ exp; () |ENUM(_,_)->consEnum typ;()
									 |_->let base = get_base_type typei in 
											(match base with ENUM(_,_) ->consEnum  base ;()|_->());()
					
					) namelist;
		
		()
	| ONLYTYPEDEF n -> 
		let (typ, sto, namelist) = n in 
		List.iter  (fun name -> 
					let (id,typ, _, exp) = name in (*Printf.printf "id : %s\n" id;*)
					match typ with ARRAY (t, dim) -> majTypeDefAssosArrayIDsize id typ exp; () |ENUM(_,_)->consEnum typ;()
				|_->()
					) namelist;
		()



