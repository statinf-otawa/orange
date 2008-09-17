(* cextraireboucle -- use Frontc CAML change loop to normelized loop, construct instructions to eval abstract store, construct flowfact
**
** Project:	O_Range
** File:	cextraireboucle.ml
** Version:	1.1
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
open Increment


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

let (mainFonc :string ref ref) =ref( ref "")
let (evalFunction:( string ref) list ref)= (ref [])

let maj hd tl =
	begin
	mainFonc := ref hd;
	evalFunction := (List.append !evalFunction tl)
	end

let  fileCour = ref "" 
let  numLine = ref 0
let isExactForm = ref false
let nomFctCour = ref !(!mainFonc)



let aUneFctNotDEf = ref false   
(* les expressions caracterisant une boucle for *)
	let expressionDinitFor = ref NOTHING

	let expressionCondFor = ref NOTHING
	let listeDesInstCourantes = ref []
	let listeDesInstGlobales = ref []
	let alreadyAffectedGlobales = ref []
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
		IDBOUCLE of int * string list * string list 
	|	IDAPPEL of int * expression *inst list *string  * string list * string list 

	
	type refAppel = string * int (* id fichier numline*)




	let listAssosTypeDefArrayIDsize  = ref [(" ", NOSIZE)]
	let listeAssosPtrNameType = ref []
	let setAssosPtrNameType  name t =(*Printf.printf"setprt %s\n" name;*) listeAssosPtrNameType := List.append   [(name, t)]   !listeAssosPtrNameType 	
	let existAssosPtrNameType  name  = (List.mem_assoc name !listeAssosPtrNameType)
	let getAssosPtrNameType name  = (List.assoc name !listeAssosPtrNameType)

	let existAssosTypeDefArrayIDsize  name  = (List.mem_assoc name !listAssosTypeDefArrayIDsize)
	let setAssosTypeDefArrayIDsize  name size = 
		if existAssosTypeDefArrayIDsize name = false then listAssosTypeDefArrayIDsize := List.append   [(name, size)]   !listAssosTypeDefArrayIDsize 	

	let getAssosTypeDefArrayIDsize name  = if existAssosTypeDefArrayIDsize name then (List.assoc name !listAssosTypeDefArrayIDsize) else NOSIZE
	


	let listLoopIdRef = ref []
	let listIdCallFunctionRef =ref  []
	let setAssosIdLoopRef id refe = listLoopIdRef := List.append   [(id, refe)]   !listLoopIdRef
	let exitsAssosIdLoopRef id = List.mem_assoc id !listLoopIdRef
	let getAssosIdLoopRef id = if exitsAssosIdLoopRef id then List.assoc id !listLoopIdRef else ("",0)


	let print_AssosIdLoopRef l=
		List.iter (fun (a, (f,num)) -> Printf.printf "Loop %d fichier %s ligne %d \n" a f num) l 	
	let print_listIdCallFunctionRef l=
		List.iter (fun (a, (f,num)) -> Printf.printf "Function %d fichier %s ligne %d \n" a f num) l 	
	 

	let exitsAssosIdCallFunctionRef id = List.mem_assoc id !listIdCallFunctionRef
	let getAssosIdCallFunctionRef id = if  exitsAssosIdCallFunctionRef id  then List.assoc id !listIdCallFunctionRef else ("",0)
	let setAssosIdCallFunctionRef id refe = listIdCallFunctionRef := List.append   [(id, refe)]   !listIdCallFunctionRef
	
	
	let rec getArraysize typ =
        match typ with
			ARRAY (t, dim) -> 
				let size =
					match calculer  (EXP(dim)) !infoaffichNull  [] with  
						ConstInt(s)	-> let dime = int_of_string  s in (*Printf.printf "%d \n"dim; *) [dime]
						|_			-> [] in
				List.append (getArraysize t) size
			| 	_ -> []

	let majAssosArrayIDsize name typ =
	(*Printf.printf "dans majAssosArrayIDsize %s\n" name;*)
	let liste = getArraysize typ in
	(*List.iter(fun dim-> Printf.printf "%d  " dim; )liste;*)
	if liste <> [] then
	begin
		if List.tl liste != [] then  setAssosArrayIDsize name (MSARRAY liste)
		else  setAssosArrayIDsize name (SARRAY  (List.hd liste))
	end
	else setAssosArrayIDsize name NOSIZE

	let majTypeDefAssosArrayIDsize name typ =
	(*Printf.printf "dans majTypeDefAssosArrayIDsize %s\t" name;*)
	let liste = getArraysize typ in
	(*List.iter(fun dim-> Printf.printf "%d  " dim; )liste;Printf.printf "\n" ;*)
	if liste <> [] then
	begin
		if List.tl liste != [] then  setAssosTypeDefArrayIDsize name (MSARRAY liste)
		else  setAssosTypeDefArrayIDsize name (SARRAY  (List.hd liste))
	end
	else setAssosTypeDefArrayIDsize name NOSIZE

	let print_AssosArrayIDsize l=
		List.iter (fun (a, b) -> Printf.printf "%s  " a; 
					match b with 
						 NOSIZE -> Printf.printf "NOSIZE\n"
						| SARRAY (v) -> Printf.printf "SINGLE ARRAY %d\n" v
						| MSARRAY (l) ->  Printf.printf "MULTI ARRAY ";List.iter(fun dim-> Printf.printf "%d  " dim; )l ;Printf.printf "\n"
				   ) l 	

	let print_AssosPtrTypeList l=
		List.iter (fun (a, b) -> Printf.printf "%s  " a;  print_base_type b true; new_line()  ) l 	
	
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
		listeDesBouclesDansCorps: listeDesIdDeBoucle;	
		boucleOuAppel : elementCorpsFonction list;
		corpsS : statement;	
		listeDesAppelDeFonctionsDansCorps : typeListeAppels ;
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
	let getListeDesBouclesFonction f = f.corps.listeDesBouclesDansCorps
	
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
	
	let add_fonction  (n,f) liste=	List.append liste [(n,f)]	
	let doc = ref (new_document [] [] [] [])
	let enumCour = ref NO_TYPE

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
	let ((id, _, _, _), others) = (List.hd names, List.tl names) in
	makeListItem typ others (List.append result [(id, typ)])
end

and get_base_typeEPS  ntyp = 
	match ntyp with
	 PROTO (typ, _, _)| OLD_PROTO (typ, _, _)| PTR typ | RESTRICT_PTR typ | ARRAY (typ, _) | CONST typ | VOLATILE typ | GNU_TYPE (_, typ) | TYPE_LINE (_, _, typ) ->   get_base_typeEPS typ 
	| FLOAT (_) | DOUBLE (_) |NO_TYPE -> FLOAT_TYPE
	| NAMED_TYPE id  ->   TYPEDEF_NAME(id)
	| STRUCT (id, dec) -> if  (List.mem_assoc id !listAssosIdTypeTypeDec)= false then 
			listAssosIdTypeTypeDec := List.append !listAssosIdTypeTypeDec [(id,  newDecTypeSTRUCTORUNION (getItemList dec []))];
						STRUCT_TYPE (id)
	| UNION (id, dec) ->   if  (List.mem_assoc id !listAssosIdTypeTypeDec)= false then 
			listAssosIdTypeTypeDec := List.append !listAssosIdTypeTypeDec [(id, newDecTypeSTRUCTORUNION (getItemList dec []))]; 					  
						UNION_TYPE (id) 
	| ENUM (id, items) -> enumCour := ntyp; INT_TYPE
	| _->   INT_TYPE


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
	
let  reecrireCAll var liste =
List.map (fun e -> 
	match e with
			IDBOUCLE (i,_,_) -> e
		|	IDAPPEL (i , expression, l,_,lt,lf) -> IDAPPEL (i , expression, l,var,lt,lf) ) liste


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

	let new_CorpsFonction listeB bloc lbOa l =
	{
		listeDesBouclesDansCorps = listeB;	
		boucleOuAppel = lbOa;
		corpsS = bloc;
		listeDesAppelDeFonctionsDansCorps = l;
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
	let setAssosIDBasetype name typ =
	if (List.mem_assoc name !listAssocIdType)= false then 
			listAssocIdType := List.append !listAssocIdType [(name, get_base_typeEPS typ)]   
	
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
		(id, (estPtrOuTableau typeAux) or (estPtrOuTableau typ) )

		
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
	List.exists (fun (_,nomF) -> (nomF = nom) ) !listeDesNomsDeFonction    
	
	(* la fonction est dans la liste par précondition *)
	let tupleNumNomFonctionDansListe nom  = List.find (fun (_,nomF) ->  (nomF = nom)  ) !listeDesNomsDeFonction  
	
	let ajouteNomDansListeNomFonction nom =
		if  (existeNomFonctionDansListe nom = false) then (* un nouveau nom de fonction *)
		begin				
			idFonction := !idFonction + 1;
			listeDesNomsDeFonction := (List.append !listeDesNomsDeFonction [(!idFonction, nom)] )
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
	
	let existeFonction nom  = List.exists (fun (_, f) -> (nom = f.nom) ) !doc.laListeDesFonctions  
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
								(
									new_CorpsFonction 	func.corps.listeDesBouclesDansCorps	 func.corps.corpsS
									!listeBoucleOuAppelCourante func.corps.listeDesAppelDeFonctionsDansCorps
								) 
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
				(*let val1 = calculer (EXP exp) !infoaffichNull  []  in *)
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
									let val1 = calculer (EXP n1) !infoaffichNull  []  in 
									let val2 = calculer (EXP n2) !infoaffichNull  []  in 
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
									let val1 = estNul ( calculer (EXP a1) !infoaffichNull  [] ) in 
									let val2 = estNul ( calculer (EXP a2) !infoaffichNull  [] ) in 
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

								if estNul ( calculer (EXP a2) !infoaffichNull  [] ) then
									(rep2, UNARY (MINUS, n2) , BINARY (op,  exp1, c2), CONSTANT (CONST_INT "0")) 
								else  (false, NOTHING, NOTHING, NOTHING) 
							end
							else
							begin
								if rep1 && rep2 then 
								begin
									let val1 = estNul ( calculer (EXP a1) !infoaffichNull  [] ) in 
									let val2 = estNul ( calculer (EXP a2) !infoaffichNull  [] ) in 
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
							if estNul ( calculer (EXP a1) !infoaffichNull  [] ) then 
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
								if estNul ( calculer (EXP a1) !infoaffichNull  [] ) then 
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

let analyseInc infoVar appel typeopPlusouMUL =
	let valinc = calculer (applyStoreVA   (EXP(infoVar.increment)) appel)  !infoaffichNull  [](*appel*) in	
	let op = infoVar.operateur in 
	let sensinc = if estNoComp valinc then NDEF 
				  else if typeopPlusouMUL (*op +or -*) then 
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
									CONST_INT i ->		if i = "1" or i ="-1" then true else false
									| CONST_FLOAT r ->	if r = "1" or r ="-1" then true else false
									| CONST_CHAR _ | CONST_STRING _| CONST_COMPOUND _->false)
			| VARIABLE _ ->		false
			| _ -> false

(*listeDesVarDeExp exp*)
let lesVarBoucle num =( listeDesVarsDeExpSeules (nombreIT num))

(* une seule affectation dans une expression*)
let rec rechercheVarBoucleFor var init  =
(*	Printf.printf  "\n analyseInitFor \n"; print_expression init 1 ;new_line ();*)
match init	with
NOTHING -> ()
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
				|_ ->   ()	)
				|_->())
	else ()
| COMMA exps ->	List.iter(fun ex-> rechercheVarBoucleFor var ex)exps							
|_ -> () (*initialisation :="";*)


let traiterEQ init borne var c =
	if !opEstPlus then (*incrément type +/-constant*)
	begin
		match !estPosInc with 
			INCVIDE -> (CONSTANTE , NOTHING, NOTHING, EQ, false, var, c)(* si init = borne toujours sinon 0*)	
			|POS|NEG-> (CONSTANTE , NOTHING, (CONSTANT (CONST_INT "1")), EQ, false, var, c)(* si init = borne 1 sinon 0*)
			|_ ->  (CROISSANT , (CONSTANT (CONST_INT "1")), NOTHING, EQ, true, var, c)
		end (*incrément type *// constant*)
	else
	begin
		match !estPosInc with
			INCVIDE -> (CONSTANTE , NOTHING, NOTHING, EQ, false, var, c)(* sic=1 alors init = borne toujours sinon 0*)	
			|POS-> (CONSTANTE , NOTHING, (CONSTANT (CONST_INT "1")), EQ, false, var, c)(* si init = borne 1 sinon 0*)
			|_ ->  (CROISSANT , (CONSTANT (CONST_INT "1")), NOTHING, EQ, true, var, c)
		end

let traiterNEQ init borne var c =
	if !opEstPlus then (*incrément type +/-constant*)
	begin
		match !estPosInc with
			INCVIDE  -> (CONSTANTE , NOTHING, NOTHING, NE, false, var, c)(* si init = borne toujours sinon 0*)
			|POS -> (CROISSANT , init, BINARY(SUB, borne,!vEPSILON), LT, false, var, BINARY(LT, VARIABLE(var), borne))(* si init = borne 1 sinon 0*)
			|NEG-> (DECROISSANT , init, BINARY (ADD, borne, !vEPSILON), GT, false, var,BINARY(GT, VARIABLE(var), borne))(* si init = borne 1 sinon 0*)
			|_ ->  (CROISSANT , init, borne, NE, true, var, c)(*voir signe INC*)
		end (*incrément type *// constant*)
	else
	begin
		match !estPosInc with
			INCVIDE  -> (CONSTANTE , NOTHING, NOTHING, NE, false, var, c)(* case constant = 1 then si init = borne 1 sinon 0*)
			|POS -> (CROISSANT , init, BINARY(SUB, borne,!vEPSILON), LT, false, var, BINARY(LT, VARIABLE(var), borne))
			(* case constant > 1  si init = borne toujours sinon 0*)
			|NEG ->  isExactForm := false;(NONMONOTONE , NOTHING, NOTHING, XOR, true, var, c)
			|_ ->   (CROISSANT , init, borne, NE, true, var, c)
		end
	
let changeCompOp op =
		match op with
			LT ->  GE (* from < to >= *)
			| LE ->  GT (*from <= to > *)
			| GT ->  LE(*  from >to <=*)
			| GE -> LT
			| _->  op
let arrayShown = ref true

let rec  rechercheConditionBinary init var op exp1 exp2 liste avant dans cte t c lv l inst=
(*	Printf.printf "rechercheConditionBinary\n";	 print_expression (BINARY (op, exp1, exp2)) 0; new_line();*)
	let l2 =  (listeDesVarsDeExpSeules exp2) in
	let inter2 =  intersection l2  l  in

(*List.iter(fun x-> Printf.printf"%s\n" x)l2;*)
	let l1 =  (listeDesVarsDeExpSeules exp1) in
	let inter1 =  intersection l1 l  in			
(*List.iter(fun x-> Printf.printf"%s\n" x)l1;			*)									
	let (isLoopCtee2, isOnlyVare2) =  if inter2 = [] then (true, false) else if  List.tl inter2 = [] then (false, true) else (false, false) in
	let (isLoopCtee1, isOnlyVare1) =  if inter1 = [] then (true, false) else if  List.tl inter1 = [] then (false, true) else (false, false) in
(*Printf.printf "rechercheConditionBinary\n";	 print_expression (BINARY (op, exp1, exp2)) 0; new_line();*)
	let (sens1, a1,b1, unitairea1, b1nul) = traiterAffineForm  exp1 var l in
	(*print_affine sens1 a1 b1 var;*)
	let (sens2, a2,b2,unitairea2, b2nul) = traiterAffineForm  exp2 var l in
(*	print_affine sens2 a2 b2 var;*)
(*Printf.printf "rechercheConditionBinary\n";	 print_expression (BINARY (op, exp1, exp2)) 0; new_line();*)
	if isLoopCtee2 && isLoopCtee1 || sens1 =  NONMONOTONE || sens2 = NONMONOTONE || (isLoopCtee2 = false && isLoopCtee1 =false)  then
	begin
(*Printf.printf "cas 1\n";	 *)
		if op = AND then traiterANDCOND init var exp1 exp2  liste avant dans cte t (BINARY(op,exp1, exp2)) lv l inst
		else 
		begin

			let testA = if !arrayShown = false then 
						begin arrayShown := true ; (*Printf.printf "traiterTab\n"; *)traiterArray  exp1 exp2 liste avant dans cte t c lv l inst end 
						else NOTHING in
			if testA = NOTHING then	
			begin
				(*Printf.printf"recPow\n";*)
			
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
(*Printf.printf "cas 2\n";	*)
			let nop = if sens1 = CROISSANT then op else changeCompOp op in
			let ne2 = 
				if  b1nul then
					if unitairea1 && sens1 = CROISSANT then exp2
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
					let ((*isindirect,inc,var, before*)isindirect,_,_,_) =  getLoopVarInc var inst in
					if isindirect then
					begin
				 		expressionIncFor := NOTHING;
						(NONMONOTONE , NOTHING, NOTHING, XOR,true, var, BINARY(op,exp1, exp2))
					end
					else traiterEQ init ne2 var ne
			| NE -> let ((*isindirect,inc,var, before*)isindirect,_,_,_) =  getLoopVarInc var inst in
					if isindirect then
					begin
				 		expressionIncFor := NOTHING;
						(NONMONOTONE , NOTHING, NOTHING, XOR,true, var, BINARY(op,exp1, exp2))
					end
					else traiterNEQ init ne2 var ne
			| _-> isExactForm := false;(*| BAND -> | XOR ->| BOR ->*) if !vDEBUG then Printf.printf   "\terreur test for non traite\n";
					(NONMONOTONE , NOTHING, NOTHING, XOR,true, var, BINARY(op,exp1, exp2))
		end
		else
		begin
			if isLoopCtee1 then
			begin
(*Printf.printf "cas 3\n";	*)
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
					| EQ -> let ((*isindirect,inc,var, before*)isindirect,_,_,_) =  getLoopVarInc var inst in
							if isindirect then
							begin
						 		expressionIncFor := NOTHING;
								(NONMONOTONE , NOTHING, NOTHING, XOR,true, var, BINARY(op,exp1, exp2))
							end
							else traiterEQ init ne1 var ne
					| NE ->  let ((*isindirect,inc,var, before*)isindirect,_,_,_) =  getLoopVarInc var inst in
							if isindirect then
							begin
						 		expressionIncFor := NOTHING;
								(NONMONOTONE , NOTHING, NOTHING, XOR,true, var, BINARY(op,exp1, exp2))
							end
							else traiterNEQ init ne1 var ne
					| _-> isExactForm := false;(* | BAND -> | XOR ->| BOR ->*) if !vDEBUG then Printf.printf   "\terreur test for non traite\n";
								(NONMONOTONE , NOTHING, NOTHING, XOR,true, var, BINARY(op,exp1, exp2))
			end
			else begin 
						isExactForm := false;(*if !vDEBUG then Printf.printf   "\terreur test for non traite\n"; *)
						(NONMONOTONE , NOTHING, NOTHING, XOR, true, var,BINARY (op,exp1, exp2))
				end
		end
end

and traiterAffineForm  e var l=
(*if List.mem var (listeDesVarsDeExpSeules  e) = false then   (CONSTANTE, CONSTANT(CONST_INT "0"), e, false ,false)
else
begin*)
let exp1 = calculer (EXP e) !infoaffichNull  []  in
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
(*end*)

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
								let ((*isindirect,inc,var, before*)isindirect,_,_,_) =  getLoopVarInc var inst in
								if isindirect then expressionIncFor := NOTHING;
								let valinc = calculer (applyStoreVA   (EXP(!expressionIncFor)) [])  !infoaffichNull  [](*appel*) in	
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
						let ((*isindirect,inc,var, before*)isindirect,_,_,_) =  getLoopVarInc name inst in
						if isindirect then  expressionIncFor := NOTHING;
						

						
						let valinc = calculer (applyStoreVA   (EXP(!expressionIncFor)) [])  !infoaffichNull  [](*appel*) in	
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
			let ((*isindirect,inc,var, before*)isindirect,_,_,_) =  getLoopVarInc var inst in
			expressionIncFor := if isindirect then  NOTHING else !expressionIncFor ;
				
			let valinc = calculer (applyStoreVA   (EXP(!expressionIncFor)) [])  !infoaffichNull  [](*appel*) in	
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

 (*print_expression exp1 0; new_line();
 print_expression exp2 0; new_line();*)
	let (ninit,nv, nop,ne1,ne2,nl , fin)=
	if isLoopCtee1 then (* exp1 is loop constant *)  
	begin
		let (ispow, k,a,b) = isPowCte var exp2 in 
		if ispow then 
		begin
			(*printResPow var k a b ;*)
			let val1 = calculer (EXP a) !infoaffichNull  []  in
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
				let val1 = calculer (EXP a) !infoaffichNull  []  in
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
		if fin = false then (NONMONOTONE , NOTHING, NOTHING, XOR, true, var, BINARY(op,exp1, exp2))
		else rechercheConditionBinary ninit nv nop ne1 ne2 nl avant dans cte t c lv l inst
(*	end*)


and traiterUn croissant  borneInf borneSup operateur multiple var  cond avant dans cte t inst=
	let (operateur, typevar, multiple,v) = 
		if multiple = false then
		begin
				if croissant = CROISSANT then begin borne:=borneSup; initialisation:=borneInf end 
				else begin  borne:=borneInf; initialisation:=borneSup   end;
				(operateur,croissant, false, var) 
		end		
		else 	( ADD, NONMONOTONE, true, var)   in
	

	let ((*isindirect,inc,var, before*)isindirect,_,_,_) =  getLoopVarInc v inst in
	if isindirect then 
	begin
		expressionIncFor := NOTHING;
		NOTHING
	end
	else expVaToExp (getNombreIt !borne (typevar=CONSTANTE||cte) t cond multiple [] !opEstPlus   
				( new_variation !expressionDinitFor !borne !expressionIncFor typevar  operateur false) v ) 



and construireCondition crois1 bInf1  bSup1  oper1 mult1 v1 cd1 crois2  bInf2  bSup2  oper2 mult2 v2 cd2 lv avant dans cte t inst=
	let nb1 = traiterUn  crois1 bInf1 bSup1  oper1 mult1 v1 cd1 avant dans cte t  inst in
	let nb2 = traiterUn  crois2 bInf2  bSup2 oper2 mult2 v2 cd2 avant dans cte t inst in
	if v1 = v2 then
	begin
		match crois1 with
			CROISSANT | DECROISSANT-> 
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
					let bSup =  if bSup2 != NOTHING  && bSup1 != NOTHING then
								begin if bSup2 = bSup1 then bSup1 else (CALL (VARIABLE("MINIMUM") , (List.append [bSup1] [bSup2] ))) end
								else if bSup1 = NOTHING then begin isExactForm := false; bSup2 end else begin isExactForm := false; bSup1 end in

					if bSup != NOTHING && bInf!= NOTHING then (crois1, bInf, bSup, oper1,false,v1, BINARY(AND, cd1,cd2))
					else	begin isExactForm := false; (NONMONOTONE , NOTHING, NOTHING, XOR,true,v1,BINARY (AND, cd1,cd2)) end
				end 
				else 
					 if crois2 = NONMONOTONE || (crois2 = CONSTANTE && bSup2 = NOTHING) (*revoir*)	
					 then begin isExactForm := false; (crois1, bInf1, bSup1, oper1,mult1, v1, BINARY(AND, cd1,cd2)) end
					 else begin isExactForm := false; (CONSTANTE, NOTHING, bSup2, oper1,false,v2 , BINARY(AND, cd1,cd2) ) end
			| NONMONOTONE ->isExactForm := false; (crois2, bInf2, bSup2, oper2,mult2, v2, BINARY(AND, cd1,cd2))
			| CONSTANTE -> isExactForm := false;
						   if bSup2 = NOTHING then  (CONSTANTE, NOTHING, bSup1, oper2,false, v1, BINARY(AND, cd1,cd2) )
						   else (crois2, bInf2, bSup2, oper2,mult2, v2, BINARY(AND, cd1,cd2))
		end
	else
	begin
		if  nb1 = NOTHING then begin isExactForm := false; (crois2, bInf2, bSup2, oper2,mult2, v2, BINARY(AND, cd1,cd2)) end
		else
		begin
			if  nb2 = NOTHING then begin isExactForm := false;(crois1, bInf1, bSup1, oper1,mult1, v1, BINARY(AND, cd1,cd2 )) end
			else (	CROISSANT, CONSTANT (CONST_INT "0"), (*CONSTANT (CONST_INT "1")*)
					BINARY (SUB, CALL (VARIABLE("MINIMUM") , List.append [bSup1] [bSup2] ), CONSTANT (CONST_INT "1")),
					  LT,mult2, lv, BINARY(AND, cd1,cd2))
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
		if crois1 = NONMONOTONE then  
		begin isExactForm := false; (*Printf.printf "only tab %s\n" v2;*)(crois2, bInf2, bSup2, oper2,mult2,v2, cd2)end
		else construireCondition crois1 bInf1  bSup1  oper1 mult1 v1 cd1 crois2  bInf2  bSup2  oper2 mult2 v2 cd2 lv avant dans cte t inst


and traiterANDCOND init var exp1 exp2 liste avant dans cte t c lv l inst =
	if liste = [] then 
	begin
		 let (crois1,bInf1, bSup1, oper1,mult1,v1,cd1)=
			match exp1 with
				BINARY (op1, exp11, exp12) ->  rechercheConditionBinary init var op1 exp11 exp12 [] avant dans cte t exp1 lv l inst
				|_-> 	(NONMONOTONE , NOTHING, NOTHING, XOR, true, var, c) in

		let (crois2, bInf2, bSup2, oper2,mult2,v2, cd2) =
			match exp2 with 
				BINARY (op2, exp21, exp22) ->  rechercheConditionBinary init var op2 exp21 exp22 [] avant dans  cte t exp2  lv l inst
				|_-> 	(NONMONOTONE , NOTHING, NOTHING, XOR, true, var, c) in

		if crois2 = NONMONOTONE ||crois1 = NONMONOTONE then isExactForm := false;
		construireCondition crois1 bInf1  bSup1  oper1 mult1 v1 cd1 crois2  bInf2  bSup2  oper2 mult2 v2 cd2 lv avant dans cte t inst
	end
	else 
	begin
		let (v, suite) = (List.hd liste, List.tl liste) in
		let (crois1,bInf1, bSup1, oper1,mult1,v1, c1)=
					match exp1 with
						BINARY (op, e1, e2) ->  rechercheConditionBinary (VARIABLE(v))  v op e1 e2 (List.tl liste) avant dans cte t c lv l inst
						|_-> 	(  NONMONOTONE , NOTHING, NOTHING, XOR, true, var , c) in

		let (crois2, bInf2, bSup2, oper2,mult2,v2, c2) =
					match exp2 with
						BINARY (op, e1, e2) ->  rechercheConditionBinary (VARIABLE(v))  v op e1 e2 (List.tl liste) avant dans cte t c lv l inst
						|_-> 	(  NONMONOTONE , NOTHING, NOTHING, XOR, true, var, c) in


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
		| UNARY (_, _) ->  (*BOOLEEN*)(ADD, NONMONOTONE,false, var) (*pas multiple voir pour les booleens*)
		| BINARY (op, exp1, exp2) ->
		   arrayShown := false;	 
		   let  (croissant,borneInf,borneSup,operateur,multiple,var,_)= rechercheConditionBinary init var op exp1 exp2 l avant dans cte t comp lv lvb  inst in

			if multiple = false then
			begin
				if croissant = CROISSANT then
				begin
					borne:=borneSup; initialisation:=borneInf; (operateur,	CROISSANT, false, var)  
				end
				else begin  borne:=borneInf; initialisation:=borneSup; (operateur,croissant, false, var)   end
			end		
			else 	( ADD, NONMONOTONE, true, var)  
		| _-> (*BOOLEEN*) ( ADD, NONMONOTONE,false, var) (*pas multiple meme chose que pour unary si booleen*)


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


and getNombreIt une conditionConstante typeBoucle  conditionI conditionMultiple appel typeopPlusouMUL infoVar var=

(*Printf.printf "getnombre d'it valeur de la condition : %s\n" var;*)
	let const = calculer (applyStoreVA   (EXP(conditionI)) appel)  !infoaffichNull  [](*appel*) in
	let isExecutedV = (match const with Boolean(b)				->  if b = false then false  else true |_->true) in	
(*Printf.printf "getnombre d'it valeur de la condition : %s\n" var;*)
		(*	
			print_expTerm const; new_line ();
			if isExecutedV  then Printf.printf "isexecuted \n" else Printf.printf "is not executed \n" ;
			Printf.printf "FIN...\n";*)

	if isExecutedV then
	begin

		if (conditionMultiple) then   EXP(NOTHING)
		else
		begin	
			let (valinc, op, sensinc) = analyseInc infoVar appel typeopPlusouMUL in
			(*Printf.printf "NON MULTIPLE\n";*)
			match sensinc with
			 NOVALID ->	 EXP(NOTHING)
			| INCVIDE ->
					(match typeBoucle with
					"for" |"while"->
						(match const with (*estExecutee*)
							ConstInt(i) 	-> if (int_of_string  i) = 0  then EXP(CONSTANT (CONST_INT "0")) else	 EXP(NOTHING) 		 	
							|ConstFloat (f) -> 	if (float_of_string  f) = 0.0  then EXP(CONSTANT (CONST_INT "0")) else   EXP(NOTHING)
							| _->		(*Printf.printf (" boucle for infinie\n");*)EXP(NOTHING))
					|"dowhile"->
						(match const with
							ConstInt(i) -> 	if (int_of_string  i) = 0  then EXP(CONSTANT (CONST_INT "1"))  else   EXP(NOTHING)
							|ConstFloat (f) -> 	if (float_of_string  f) = 0.0  then EXP(CONSTANT (CONST_INT "1"))   else EXP(NOTHING)
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
						| _->		(*Printf.printf (" boucle for infinie\n");*)EXP(NOTHING))
					|"dowhile"->
					(match const with
						ConstInt(i) -> 	if (int_of_string  i) = 0  then EXP(CONSTANT (CONST_INT "1"))
										  else if  op = EQ  then  EXP(CONSTANT (CONST_INT "2"))   else EXP(NOTHING)
						|ConstFloat (f) -> 	if (float_of_string  f) = 0.0  then EXP(CONSTANT (CONST_INT "1"))
											else if  op = EQ then   EXP(CONSTANT (CONST_INT "2"))   else EXP(NOTHING)
						| _->				EXP(NOTHING))
					|_-> EXP(NOTHING)
				end
				else 
				begin 

				
					let typeInc =  expressionType valinc  in

					let bie = expVaToExp (applyStoreVA 
										(EXP ( remplacerValPar  "EPSILON" (CONSTANT (CONST_INT "1")) (infoVar.borneInf))) appel)  in
					
					let borneinf =  if listeDesVarsDeExpSeules bie = [] 

					then calculer  (EXP ( bie)) !infoaffichNull  [] else NOCOMP in
					let typeInf =  expressionType borneinf  in
					let bse = expVaToExp (applyStoreVA 
										(EXP ( remplacerValPar  "EPSILON" (CONSTANT (CONST_INT "1")) (infoVar.borneSup))) appel)  in
					let bornesup = if listeDesVarsDeExpSeules bse = [] then calculer  (EXP ( bse)) !infoaffichNull  [] else NOCOMP in
					let typeSup = expressionType bornesup in 

					let valEPSILON = if typeInf = INTEGERV && typeSup  = INTEGERV && typeInc  = INTEGERV then (CONSTANT (CONST_INT "1")) 
										 else if typeInf = FLOATV || typeSup  = FLOATV || typeInc  = FLOATV then !vEPSILONFLOAT
											  else  if 	espIsNotOnlyVar bornesup || espIsNotOnlyVar borneinf  || espIsNotOnlyVar valinc then !vEPSILON
													else !vEPSILONFLOAT in
				
					(*afficherListeAS appel; new_line();*)
 					let bs = applyStoreVA   (EXP ( infoVar.borneSup)) appel in
					let bi = applyStoreVA   (EXP ( infoVar.borneInf)) appel in
					let bu = applyStoreVA   (EXP ( une )) appel in
					(*print_expVA bs; new_line();*)

(*Printf.printf "getNombreIt recherche de affect : \n";
print_expression infoVar.borneSup 0; space() ;flush() ;new_line(); flush();new_line(); 
print_expression infoVar.borneInf 0; space() ;flush() ;new_line(); flush();new_line(); 
print_expression  une 0; space() ;flush() ;new_line(); flush();new_line(); 
Printf.printf "getNombreIt recherche de affect : \n";*)

					let (rep, var) = hasPtrArrayBoundCondition bs in
					let (bsup, binf,expune)=
								if rep = true then 
								begin
									(*Printf.printf "getNombreIt recherche de affect :%s \n"var;
									

 
								afficherListeAS appel; Printf.printf "FIN CONTEXTE \n";*)

									let av = (rechercheAffectVDsListeAS var appel) in
									(*print_expVA av;flush(); space(); new_line();*)
									let newe = expVaToExp av  in
									let (tab1,lidx1, e1) =getArrayNameOfexp newe in
									if tab1 != "" then
									begin
										let nsup = changeExpInto0 e1 (expVaToExp bs) in
										(*print_expression e1 0; new_line();*)
										(*Printf.printf "nom du tableau :%s\n"tab1;*)
										let ninf = changeExpInto0 e1 (expVaToExp bi) in
										
										let nune = changeExpInto0 e1 (expVaToExp bu) in
										
										let size = getAssosArrayIDsize tab1 in
										let varName =  Printf.sprintf "%s_%s" "getvarTailleTabMax" var in
										(match size with 
											NOSIZE -> (nsup, ninf, nune)
											| SARRAY (v) ->
												let arraySize = (CONSTANT (CONST_INT (Printf.sprintf "%d" v) )) in
												(remplacerValPar  varName arraySize  nsup, ninf,remplacerValPar  varName arraySize  nune)
											| MSARRAY (lsize) -> 
												let tsize = expressionEvalueeToExpression (prodListSize lsize) in
												(*flush(); space();
												print_expression tsize 0; flush(); space();new_line();flush(); space();*)

												(*let nb = remplacerValPar  varName tsize  nsup in*)
												(*print_expression nb 0; flush(); space(); new_line();*)
												(remplacerValPar  varName tsize  nsup, ninf,remplacerValPar  varName tsize  nune))
									end
									else  (infoVar.borneSup, infoVar.borneInf, une)
								end
								else (infoVar.borneSup, infoVar.borneInf, une) in
					if sensinc = NDEF || (op != NE) then  applyStoreVA   (EXP( remplacerValPar  "EPSILON" valEPSILON expune)) appel
					else if sensinc = POS then  
						applyStoreVA   (EXP(calculForIndependant typeBoucle (BINARY(SUB, bsup,valEPSILON)) binf infoVar.increment typeopPlusouMUL infoVar.afterindirect)) appel
						else 
						begin
						(*	sensNE := NEG;*)
							applyStoreVA   (EXP(calculForIndependant typeBoucle (BINARY (ADD, binf, valEPSILON))  bsup infoVar.increment typeopPlusouMUL infoVar.afterindirect)) appel
						end
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


and prodListSize l =
if l = [] then ConstInt ("1")
else  evalexpression(	Prod (ConstInt (Printf.sprintf "%d" (List.hd l)), prodListSize (List.tl l) ))



let rec typeDefList typ name result =
if name != [] then 
begin
	let ((id, _, _, _), others) = (List.hd name, List.tl name) in
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
			begin
				List.iter (fun (n, _ , _,_)-> ajouteNomDansListeNomFonction n) namelist
			end;
		()	
		| TYPEDEF (n, _)  -> 
			begin
				let (typ, _, names) =n in 
				typeDefList (get_base_typeEPS typ) names []  
			end;()	
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
	| STAT_LINE (stat, file, line) -> fileCour := file; numLine := line; consRefstatement stat;()
	| _ ->				()
	 

and  consRefexpression exp =
	 match exp with
	UNARY (_, e) ->   consRefexpression e;()
	| BINARY (_, exp1, exp2) ->  consRefexpression exp1 ; consRefexpression exp2;	()
	| QUESTION (exp1, exp2, exp3) -> consRefexpression exp1 ; consRefexpression exp2; consRefexpression exp3;()
	| CAST (_, e) 		 ->  consRefexpression e ; ()
	| CALL (_ , _) 				->		idAppel := !idAppel+1;
		
				
				setAssosIdCallFunctionRef !idAppel (!fileCour , !numLine );()
	| COMMA e 				->    List.iter (fun ep -> consRefexpression ep) e; ()
	| MEMBEROF (e , _) 		
	| MEMBEROFPTR (e , _) 	->		consRefexpression e ; ()
	| GNU_BODY (decs, stat) ->  consRefstatement   (BLOCK (decs, stat));()
	| EXPR_SIZEOF e ->consRefexpression e;()
	| INDEX (e, _) ->consRefexpression e;()
	| EXPR_LINE (exp, file, line)->fileCour := file; numLine := line; consRefexpression exp;()		
	| _->()



and ajouteFonctionDansDocument proto body =					
	let (_ , _ , fct )=proto in
	let (nom,_,_,_) =fct in
	ajouteNomDansListeNomFonction nom;
	let (num, _) = tupleNumNomFonctionDansListe nom in
	 
	let (decs, stat) = body in
	consRefstatement (BLOCK (decs, stat));
	let nouCorpsFonction = new_CorpsFonction  []   (BLOCK (decs, stat)) [] [](*!laListeDesAppelsDsFctCourante *)in
	listeRes := []; 
	creerListeES proto ; 
(*Printf.printf"ajoute fonction\n";*)
	let nouInfoFonc = new_Infofonction  nom proto nouCorpsFonction [] !listeRes in	
	let nouListe = add_fonction ( num,  nouInfoFonc ) !doc.laListeDesFonctions in		
	doc := new_document !doc.laListeDesBoucles nouListe  !doc.laListeDesAssosBoucleBorne  !doc.laListeDesNids

let isDivInc exp =
	let val1 = calculer (EXP exp) !infoaffichNull [] in 
	if val1 = NOCOMP  then false
	else
	begin
		let varMoinsUn = calculer (EXP (BINARY(SUB,exp, CONSTANT  (CONST_INT "1")))) !infoaffichNull [] in 
		 
		if estStricPositif varMoinsUn then false
		else true
	end

 let traiterConditionBoucleFor t nom nbIt cond eng (*exp*) init inc var cte var2 listLoopVar avant dans lvb vcond inst =
(*afficherLesAffectations inst;*)
	let liste = listeDesVarsDeExpSeules cond in
	let listeV = listeDesVarsDeExpSeules init in

	expressionDinitFor :=NOTHING;
	expressionIncFor:= NOTHING;
	rechercheVarBoucleFor var init;
	
	let (operateur,typevar,multiple,v) = analyseCompFor var !expressionDinitFor cond listLoopVar avant dans cte t var2 lvb inst in	

	let ( indirect,nv,nt, indirectafter)=

		if v != var2 then
		begin
			expressionDinitFor := expVaToExp(rechercheAffectVDsListeAS v avant);
			opEstPlus:= true;	
			let ((*isindirect,inc,var, before*)isindirect,_,var, before) =  getLoopVarInc v inst in
			if isindirect then 
			begin 
				expressionDinitFor := expVaToExp(rechercheAffectVDsListeAS var avant);
				expressionDinitFor := if !expressionDinitFor = NOTHING then VARIABLE(var) else !expressionDinitFor;
				(true, var, "dowhile", before = false) 
			end
			else (false, v, t, false)
		end
		else
		begin
			expressionDinitFor :=  (CONSTANT (CONST_INT "0"));
			opEstPlus:= true;	
			expressionIncFor:=CONSTANT (CONST_INT "1");
			(false, v, t, false)
		end in

	let (sup, inf, inc) = 
	if indirect && !opEstPlus = false && isDivInc !expressionIncFor then (!expressionDinitFor, !borne,  BINARY (DIV, CONSTANT  (CONST_INT "1"), !expressionIncFor)) 
	else (!borne,!expressionDinitFor,!expressionIncFor) in
	borne := sup;
	initialisation := inf;	
	expressionDinitFor := inf;
	expressionIncFor := inc;

(*Printf.printf "\n\ntraiterConditionBoucleFor  2\n" ;*)
	let (increment, typeopPlusouMUL) = (!expressionIncFor, !opEstPlus)	in
	(*if !expressionDinitFor = NOTHING then expressionDinitFor := VARIABLE(nv);*)
	let infoVar =   new_variation !expressionDinitFor !borne !expressionIncFor typevar  operateur indirectafter in

	let nb = expVaToExp (getNombreIt !borne (typevar=CONSTANTE||cte) t vcond multiple [] typeopPlusouMUL  infoVar v) in
	listeBoucleOuAppelCourante := reecrireCAll var2 !listeBoucleOuAppelCourante;

	let info = (new_boucleInfo t nom liste nbIt eng cte vcond multiple !listeBoucleOuAppelCourante 
				( new_variation !expressionDinitFor nb !expressionIncFor typevar operateur indirectafter) typeopPlusouMUL) in
	
	let boucleFor = new_boucleFor  info  listeV  var2  !expressionDinitFor  nb !expressionIncFor  in
	let nouvBoucle = new_bouclef boucleFor in
	doc := 	new_document 
				(new_ListeDesBoucles !doc.laListeDesBoucles  [nouvBoucle]) 
				!doc.laListeDesFonctions
				(new_ListeDesBoucles !doc.laListeDesAssosBoucleBorne
					[new_infoBorneDeBoucle nouvBoucle  
						(getBorneBoucleFor t boucleFor.n boucleFor.valInit.valeur boucleFor.c typeopPlusouMUL infoVar.afterindirect) [] !isExactForm])
				!doc.laListeDesNids;(*isExactForm*)
	(nb, indirect)

and traiterConditionBoucle t nom nbIt cond eng  var cte (*inc typeopPlusouMUL*) var2 listLoopVar avant dans lvb vcond inst =
(*Printf.printf "\n\ntraiterConditionBoucleFor  analyseCompFor\n" ;*)
 	let (operateur, typevar,multiple,v) = analyseCompFor    var  (VARIABLE(var)) cond listLoopVar  avant dans cte t var2 lvb inst in
	let liste = listeDesVarsDeExpSeules  cond in
	expressionIncFor:= NOTHING;
(*Printf.printf "\n\ntraiterConditionBoucleFor  analyseCompFor\n" ;*)
 
	let ( indirect,nv,nt, indirectafter)=
		if v != var2 then
		begin
			expressionDinitFor := expVaToExp(rechercheAffectVDsListeAS v avant);
			opEstPlus:= true;	
			let ((*isindirect,inc,var, before*)isindirect,_,var, before) =  getLoopVarInc v inst in
			if isindirect then 
			begin 
				expressionDinitFor := expVaToExp(rechercheAffectVDsListeAS var avant);
				(true, var, "dowhile", before = false) 
			end
			else (false, v, t, false)

		end
		else
		begin
			expressionDinitFor :=  (CONSTANT (CONST_INT "0"));
			opEstPlus:= true;	
			expressionIncFor:=CONSTANT (CONST_INT "1");
			(false, v, t, false)
		end in

	let (sup, inf, inc) = 
	if indirect && !opEstPlus = false && isDivInc !expressionIncFor then ((VARIABLE(nv)), !borne,  BINARY (DIV, CONSTANT  (CONST_INT "1"), !expressionIncFor)) 
	else (!borne,(VARIABLE(nv)),!expressionIncFor) in
	borne := sup;
	initialisation := inf;	
	expressionIncFor := inc;

(*Printf.printf "\n\ntraiterConditionBoucleFor  2\n" ;*)
 	let infoVar =   new_variation !expressionDinitFor !borne !expressionIncFor typevar  operateur indirectafter in

	let nb = expVaToExp (getNombreIt !borne (typevar=CONSTANTE||cte) t vcond multiple [] !opEstPlus   infoVar v) in
	listeBoucleOuAppelCourante := reecrireCAll var2 !listeBoucleOuAppelCourante;
	let b = new_boucleWhileOuDoWhile 
				(new_boucleInfo t nom liste nbIt eng multiple vcond cte  !listeBoucleOuAppelCourante
				(new_variation (VARIABLE(v)) nb !expressionIncFor typevar operateur indirectafter) !opEstPlus ) [] []  in
	let ba = (new_boucleA b )  in	

	doc := new_document 	(new_ListeDesBoucles !doc.laListeDesBoucles  [ba])  !doc.laListeDesFonctions
							(new_ListeDesBoucles !doc.laListeDesAssosBoucleBorne
								[ new_infoBorneDeBoucle ba (getBorneBoucleFor t nb !initialisation !expressionIncFor !opEstPlus indirectafter) [] !isExactForm] )		
							!doc.laListeDesNids;
(nb, indirect)
													
																			
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
			| APPEL (_,_, _, _,_,_) ->true
		) listeInst in
(*	Printf.printf "ideng %d EVAL var %s\n" idEng varDeBoucle ;*)
	evalStore   (new_instBEGIN (listeInter)) []
	
			
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

let rec rechercheListeDesVarDeBoucle listeVCond aS =
if listeVCond = [] then begin (*Printf.printf "fin liste variable \n"	;*) [] end
else
begin
(*Printf.printf "variable courante :%s\n"	(List.hd listeVCond);*)
	if (estDef (List.hd listeVCond)  aS)	then  List.append [List.hd listeVCond]  (rechercheListeDesVarDeBoucle (List.tl listeVCond) aS)
	else rechercheListeDesVarDeBoucle (List.tl listeVCond) aS
end		

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
	 
	if suite = [] then IF (test, (listeSwitchStatementToSeq stat), listDefault) else IF (test, (listeSwitchStatementToSeq stat), (buildSwitchStatement suite listDefault ))
end
else listDefault
	


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
		
		let trueListPred = !trueList in
		let falseListPred = !falseList in
		
		idIf := !idIf + 1;
		analyse_expression   exp ;
		let ne = !nouvExp in   
		let varIfN =  Printf.sprintf "%s_%d" "IF" !idIf  in	 
		let newaffect =new_instVar  varIfN  (EXP(ne)) in 
		listeDesInstCourantes := List.append !listeDesInstCourantes  [newaffect]; 
		let listePred = !listeDesInstCourantes in	
		listeDesInstCourantes := [];
		trueList := List.append !trueList [varIfN];
		analyse_statement  s1;
		trueList := trueListPred ;
  
		if (s2 = NOP)	then 
		begin
			listeDesInstCourantes :=  List.append listePred  [ new_instIFV (EXP(VARIABLE(varIfN))) (new_instBEGIN (!listeDesInstCourantes)) ]
		end
		else 	
		begin
			let listeVrai = !listeDesInstCourantes in
			listeDesInstCourantes := [];
			falseList := List.append !falseList [varIfN];
			analyse_statement  s2;													
			listeDesInstCourantes := 
				List.append  listePred  [new_instIFVF (EXP(VARIABLE(varIfN))) (new_instBEGIN (listeVrai))  (new_instBEGIN (!listeDesInstCourantes)) ];
			falseList := falseListPred
		end;	
												
	| WHILE (exp, stat) ->  	(*analyse_expression  exp ;rien condition sans effet de bord*)	
		nbImbrications := !nbImbrications + 1;

		if !nbImbrications >= !nbImbricationsMaxAppli then nbImbricationsMaxAppli := !nbImbrications;

		listeNextExp := [];
		analyse_expressionaux exp ;
		let ne = !nouvExp in   
		idBoucle := !idBoucle +1;
		let numBoucle = !idBoucle in	
		let varIfN =  Printf.sprintf "%s_%d" "TWH" numBoucle  in	 
		let newaffect =new_instVar  varIfN  (EXP(ne)) in 
		listeDesInstCourantes := List.append !listeDesInstCourantes  [newaffect]; 


		let varBoucleIfN =  Printf.sprintf "%s_%d" "bIt" !idBoucle in	
		listAssocIdType := List.append !listAssocIdType [(varBoucleIfN, INT_TYPE)] ;
		let listePred = !listeDesInstCourantes in
		listeDesInstCourantes := !listeNextExp;																	
		listeBoucleOuAppelCourante	:= List.append  !listeBoucleOuAppelCourante   [IDBOUCLE(numBoucle, !trueList,!falseList)];	
		let maListeDesBoucleOuAppelPred = 	!listeBoucleOuAppelCourante		in
		listeBoucleOuAppelCourante := [];
								
		let listeBouclesInbriqueesPred = !listeDesBouclesDuNidCourant in
		listeDesBouclesDuNidCourant := List.append  !listeDesBouclesDuNidCourant [numBoucle];			
		listeBouclesImbriquees := [];
			
		let idBoucleEngPred = !idBoucleEng in	
		idBoucleEng := numBoucle;
		let deg = !nbImbrications in 
		aUneFctNotDEf := false;
		analyse_statement  stat;
		listeNextExp := [];
		analyse_expressionaux exp ;
		idBoucleEng := idBoucleEngPred;

		let lesInstDeLaBoucle = !listeDesInstCourantes in
		idBoucleEng := idBoucleEngPred;

		let li = if !aUneFctNotDEf = true then 
		begin 
		(*	Printf.printf "traitement particuloier boucle\n";*)
			listeDesInstCourantes := []; onlyAstatement stat;onlyAexpression   exp ; !listeDesInstCourantes
		end 
		else !listeDesInstCourantes in


		let listeVCond =  listeDesVarsDeExpSeules  exp in  
(*ICI*)
		let na = extractVarCONDAffect  li listeVCond in
		let asna = evalStore (new_instBEGIN (na)) []  in


		let listeVDeBoucle =  	rechercheListeDesVarDeBoucle  listeVCond 	asna in
		let (varDeB, constante, lVB) =
			(if listeVDeBoucle = [] then (varBoucleIfN, true, [])
			else
				if (List.tl listeVDeBoucle) = [] then  (List.hd listeVDeBoucle, false, []) (*la boucle ne depend que d'1 variable on peut traiter*)	
				else (varBoucleIfN, false, listeVDeBoucle))in

	
		
		(*afficherLesAffectations na;*)
		
		let listeASC = evalStore (new_instBEGIN (listePred)) [] in
		isExactForm := (hasMultiOuputInst stat = false) && (!trueList = []) && (!falseList = []);
(*Printf.printf "\n\nAnalyse statement : la boucle %d   \n" numBoucle;*)
(*Printf.printf "\n\nAnalyse statement : la boucle %d   \n" numBoucle;
if !isExactForm then Printf.printf "exact\n" else Printf.printf "non exact\n" ;*)
		let (nb, addtest) = traiterConditionBoucle "while" numBoucle deg exp idBoucleEngPred  varDeB constante varBoucleIfN lVB listeASC  asna (*aS*) listeVDeBoucle (VARIABLE(varIfN)) na in
(*Printf.printf "\n\nAnalyse statement : la boucle %d   ap\n" numBoucle;*)

		listeDesInstCourantes := 
				[	new_instFOR numBoucle varBoucleIfN	(EXP(NOTHING)) (EXP(exp)) (EXP(NOTHING))
								 (EXP( nb)) (new_instBEGIN (lesInstDeLaBoucle ))];
																										
		let res = majABB []	!doc.laListeDesAssosBoucleBorne 	numBoucle !listeDesInstCourantes in
		if !vDEBUG then  Printf.printf "\n\nAnalyse statement : noeud traité : %d varDEBOUCLE %s \n\n "  numBoucle varBoucleIfN;
		if (!listeBouclesImbriquees = []) then 	(*  test ne contient pas de boucle *)
		begin
			if !vDEBUG then  	Printf.printf "\n\nAnalyse statement : la boucle %d ne contient pas de boucle \n" numBoucle;
			noeudCourant :=(new_NidDeBoucle exp  (rechercheAssosBoucleBorne numBoucle) varBoucleIfN  (*lesInst*)!listeDesInstCourantes []) 	
		end
		else 
		begin
			if !vDEBUG then Printf.printf "\nAnalyse statement : la boucle %d contient boucles appel relierLesNoeudsEnglobesAuNoeudCourant\n" numBoucle;
			(* attention on peut avoir X sous noeuds et donc 1 liste de noeuds et pas un seul*)
			relierLesNoeudsEnglobesAuNoeudCourant 	numBoucle varBoucleIfN !listeNoeudCourant !listeBouclesImbriquees exp
		end;									
		(* si la boucle est au départ d'un noeud*)
		let nonEstTeteNid = aBoucleEnglobante (getBoucleInfoB (rechercheBoucle numBoucle)) in
		if (nonEstTeteNid = false) then
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
		listeDesInstCourantes :=  List.append( List.append listePred !listeDesInstCourantes) !listeNextExp;
		nbImbrications := !nbImbrications - 1; 		
		listeBoucleOuAppelCourante :=  maListeDesBoucleOuAppelPred 
									
	| DOWHILE (exp, stat) ->		
		nbImbrications := !nbImbrications + 1;
		if !nbImbrications >= !nbImbricationsMaxAppli then nbImbricationsMaxAppli := !nbImbrications;
	(*	analyse_expression   exp ;*)
		idBoucle := !idBoucle +1;
		let numBoucle = !idBoucle in
		let varBoucleIfN =  Printf.sprintf "%s_%d" "bIt" !idBoucle in	
		let listePred = !listeDesInstCourantes in
		listeDesInstCourantes := [];
		listAssocIdType := List.append !listAssocIdType [(varBoucleIfN, INT_TYPE)] ;									
		listeBoucleOuAppelCourante	:= List.append !listeBoucleOuAppelCourante  [IDBOUCLE(numBoucle, !trueList,!falseList)];
		let listeBouclesInbriqueesPred  = !listeDesBouclesDuNidCourant in					
		listeDesBouclesDuNidCourant := List.append  !listeDesBouclesDuNidCourant [numBoucle];			
		listeBouclesImbriquees := [];

		let maListeDesBoucleOuAppelPred = 	!listeBoucleOuAppelCourante		in
		listeBoucleOuAppelCourante := [];

		let idBoucleEngPred = !idBoucleEng in 										
		idBoucleEng := numBoucle;	
		let deg = !nbImbrications in 
		aUneFctNotDEf := false;
		analyse_statement  stat;
		idBoucleEng := idBoucleEngPred;


		listeNextExp := [];
		analyse_expressionaux exp ;
		let ne = !nouvExp in   
		let varIfN =  Printf.sprintf "%s_%d" "TWH" numBoucle  in	 
		let newaffect =new_instVar  varIfN  (EXP(ne)) in 
		listeDesInstCourantes := List.append !listeDesInstCourantes  [newaffect]; 
		listeDesInstCourantes := List.append !listeDesInstCourantes  !listeNextExp; 

 		let lesInstDeLaBoucle = !listeDesInstCourantes in
	
		let li = if !aUneFctNotDEf = true then 
		begin 
			(*Printf.printf "traitement particuloier boucle\n";*)
			listeDesInstCourantes := []; onlyAstatement stat;onlyAexpression   exp ; !listeDesInstCourantes
		end 
		else !listeDesInstCourantes in
		

		let listeVCond =  listeDesVarsDeExpSeules  exp in  
	
(*ICI*)
		let na = extractVarCONDAffect  li listeVCond in
		let asna = evalStore (new_instBEGIN (na)) [] in


		let listeVDeBoucle =  	rechercheListeDesVarDeBoucle  listeVCond 	asna in
	
		let (varDeB, constante, lVB) =
			(if listeVDeBoucle = [] then (varBoucleIfN, true, [])
			else
				if (List.tl listeVDeBoucle) = [] then 
					(List.hd listeVDeBoucle, false, []) (*la boucle ne depend que d'une seule variable on peut traiter*)	
				else (varBoucleIfN, false, listeVDeBoucle))in


		
		let las = evalStore (new_instBEGIN (listePred)) [] in
		isExactForm := (hasMultiOuputInst stat = false) && (!trueList = []) && (!falseList = []);
		(*Printf.printf "\n\nAnalyse statement : la boucle %d   \n" numBoucle;*)
		(*if !isExactForm then Printf.printf "exact\n" else Printf.printf "non exact\n" ;
*)
		let (nb,_) =  traiterConditionBoucle "do" numBoucle deg exp idBoucleEngPred  varDeB constante  varBoucleIfN lVB las asna listeVDeBoucle  (VARIABLE(varIfN)) na in 
	(*Printf.printf "\n\nAnalyse statement : la boucle %d   ap\n" numBoucle;*)
		listeDesInstCourantes :=  [new_instFOR numBoucle varBoucleIfN (EXP(NOTHING)) (EXP(exp)) (EXP(NOTHING)) (EXP( nb)) 
									(new_instBEGIN (lesInstDeLaBoucle ))];				
		
		let res = majABB []	!doc.laListeDesAssosBoucleBorne 	numBoucle (*lesInst*)!listeDesInstCourantes in
		if !vDEBUG then Printf.printf "\n\nAnalyse statement : noeud traité : %d varDEBOUCLE %s \n\n " numBoucle varBoucleIfN;
		if (!listeBouclesImbriquees = []) then 	(*  test ne contient pas de boucle *)
		begin
			if !vDEBUG then Printf.printf "\n\nAnalyse statement : la boucle %d ne contient pas de boucle \n" numBoucle;
			noeudCourant :=(new_NidDeBoucle exp (rechercheAssosBoucleBorne numBoucle)  varBoucleIfN !listeDesInstCourantes []) 
		end
		else 
		begin
			if !vDEBUG then Printf.printf "\nAnalyse statement : la boucle %d contient boucles appel relierLesNoeudsEnglobesAuNoeudCourant\n" numBoucle;
			(* attention on peut avoir X sous noeuds et donc 1 liste de noeuds et pas un seul*)
			relierLesNoeudsEnglobesAuNoeudCourant numBoucle varBoucleIfN !listeNoeudCourant !listeBouclesImbriquees
			exp
		end;									
		(* si la boucle est au départ d'un noeud*)
		let nonEstTeteNid = aBoucleEnglobante (getBoucleInfoB (rechercheBoucle numBoucle)) in
		if (nonEstTeteNid = false) then
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
		listeDesInstCourantes :=   List.append listePred !listeDesInstCourantes;	
		nbImbrications := !nbImbrications - 1; 										
		listeBoucleOuAppelCourante :=  maListeDesBoucleOuAppelPred 

	| FOR (exp1, exp2, exp3, stat) ->
		nbImbrications := !nbImbrications + 1;

		if !nbImbrications >= !nbImbricationsMaxAppli then  nbImbricationsMaxAppli := !nbImbrications;

		listeNextExp := [];
		analyse_expression  exp1 ;
		idBoucle := !idBoucle +1;
		let num = !idBoucle in			
		analyse_expressionaux  exp2;
		let ne = !nouvExp in   
		let varIfN =  Printf.sprintf "%s_%d" "TWH" num  in	 
		let newaffect =new_instVar  varIfN  (EXP(ne)) in 
		listeDesInstCourantes := List.append !listeDesInstCourantes  [newaffect]; 


		let varBoucleIfN =  Printf.sprintf "%s_%d" "bIt" !idBoucle in	
		let listePred = !listeDesInstCourantes in
		listAssocIdType := List.append !listAssocIdType [(varBoucleIfN, INT_TYPE)] ;
		listeDesInstCourantes := !listeNextExp;	
									
		listeBoucleOuAppelCourante	:= List.append  !listeBoucleOuAppelCourante [IDBOUCLE(num, !trueList,!falseList )];	
		let listeBouclesInbriqueesPred  = !listeDesBouclesDuNidCourant in
		let maListeDesBoucleOuAppelPred = 	!listeBoucleOuAppelCourante		in
		listeBoucleOuAppelCourante := [];
					
		listeDesBouclesDuNidCourant := List.append  !listeDesBouclesDuNidCourant [num];
		listeBouclesImbriquees := [];
		let idBoucleEngPred = !idBoucleEng in 	
		aUneFctNotDEf := false;	
		idBoucleEng := num;
		analyse_statement   stat;
		idBoucleEng := idBoucleEngPred;

		(* recherche des variables de la condition qui sont dans le aS cad modifiées par la boucle*)
		analyse_expression  exp3;
		listeNextExp := [];
		analyse_expressionaux  exp2;
		let lesInstDeLaBoucle = !listeDesInstCourantes in
		listeASCourant := [];
		let li = if !aUneFctNotDEf = true then  
		begin 
			
			listeDesInstCourantes := []; onlyAstatement stat;onlyAexpression   exp3 ;onlyAexpression   exp2; !listeDesInstCourantes
		end  
		else !listeDesInstCourantes in

	

		let listeVCond =  listeDesVarsDeExpSeules  exp2 in  
	
(*ICI*)
		
		let na = extractVarCONDAffect  li listeVCond in
		let asna = evalStore (new_instBEGIN (na)) []  in		 
		let listeVDeBoucle =  	rechercheListeDesVarDeBoucle  listeVCond 	asna in
		(*remarque ajouter les initialisations au bloc englobant et exp3 à la boucle *)
		

		let (varDeBoucle, constante, 	listeVB) =
		(if listeVDeBoucle = [] then (varBoucleIfN, true, [])
		else
			if (List.tl listeVDeBoucle) = [] then (List.hd listeVDeBoucle, false, [])(*la boucle ne depend que d'une seule variable on peut traiter*)
			else (varBoucleIfN, false, listeVDeBoucle))in	

		let las=  evalStore (new_instBEGIN (listePred)) [] in
				isExactForm := (hasMultiOuputInst stat = false) && (!trueList = []) && (!falseList = []);
(*Printf.printf "\n\nAnalyse statement : la boucle %d   \n" num;*)(*
if !isExactForm then Printf.printf "exact\n" else Printf.printf "non exact\n" ;*)
		let (nb,addtest) = traiterConditionBoucleFor 	"for" num !nbImbrications exp2
					idBoucleEngPred exp1 exp3  varDeBoucle constante varBoucleIfN listeVB las asna listeVDeBoucle (VARIABLE(varIfN)) na in	
		(*Printf.printf "\n\nAnalyse statement : la boucle %d  ap \n" num;*)
		listeDesInstCourantes := 
				[	new_instFOR num varBoucleIfN	(EXP(exp1)) (EXP(exp2)) (EXP(exp3))  (EXP( nb)) (new_instBEGIN lesInstDeLaBoucle )  ];
					
																		
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
		let nonEstTeteNid = aBoucleEnglobante (getBoucleInfoB (rechercheBoucle num)) in
		if (nonEstTeteNid = false) then
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
		listeDesInstCourantes :=  List.append( List.append listePred !listeDesInstCourantes) !listeNextExp;
		nbImbrications := !nbImbrications - 1; 														
		listeBoucleOuAppelCourante :=  maListeDesBoucleOuAppelPred 
	
	| BREAK | CONTINUE -> 			()
	| RETURN (exp) ->		if exp = NOTHING	then ()	else 
							begin
								(*analyse_expression  exp ;*)
								listeNextExp := [];
								analyse_expressionaux  exp ;
								let ne = !nouvExp in
								let nouvarres = Printf.sprintf "res%s" !nomFctCour  in
								let newaffect = new_instVar  (nouvarres)  (EXP(ne))in
								listeDesInstCourantes :=List.append ( List.append !listeDesInstCourantes  [newaffect]) !listeNextExp
							end
	| SWITCH (exp, stat) ->			analyse_expression   exp ;
									let ne = !nouvExp in   
									idSwitch := !idSwitch + 1;
									let varIfNaux =  Printf.sprintf "%s_%d" "SW" !idSwitch  in	 
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
						sorties := List.append !sorties (instPourVarDeExpEnSortie valeurParam (VARIABLE(nom)));
						construireListesES (List.tl listeDesES) (List.tl arg)  
				| ENTREESORTIE (nom) -> 
					entrees := List.append !entrees [new_instVar nom  (EXP(valeurParam))];
					sorties := List.append !sorties (instPourVarDeExpEnSortie valeurParam (VARIABLE(nom)));
					construireListesES (List.tl listeDesES) (List.tl arg)  
		end

	(* nom est de type pointeur soit fonction : f (void * k,...) et appel de f
	on peut avoir : f(&exp, ...), f(ptr, ...), f(ptr+i, ...) on doit dans le premier car construire 
	l'affectation en fin d'appel de la fonction : exp = *k et dans l'autre *ptr=*k *)
	and instPourVarDeExpEnSortie valeurParam expressionAffectation =
		match valeurParam with
		VARIABLE n -> 
					  [new_instMem ("*"^n) (EXP(VARIABLE(n))) (EXP (UNARY(MEMOF, expressionAffectation)))]
			(*  cas ou on passe ptr car hypothèse code OK *)
		| UNARY (op , e)->
			(	match op with 
				ADDROF	-> 
				(	match e with 
					(*on a &exp mais exp peut être une variable, un tableau ou un champ de struct*)
					VARIABLE v -> [new_instVar v  (EXP (UNARY(MEMOF, expressionAffectation)))]
							
					| INDEX (t, i) -> 
						( 	match t with 
							VARIABLE v -> 
								[new_instTab v (EXP(i)) (EXP (UNARY(MEMOF, expressionAffectation)))]
							| _-> if !vDEBUG then Printf.printf "exp pour tab avec nom tab pas variable non traité\n";
							[])														
					| MEMBEROF (_, _) ->
						[new_instVar (expressionToString "" e 0)(EXP (UNARY(MEMOF, expressionAffectation)))]
					| MEMBEROFPTR (_, _) ->	
						[new_instVar (expressionToString "" e 0) (EXP (UNARY(MEMOF, expressionAffectation)))]
					| _->if !vDEBUG then  Printf.printf "erreur lvalue attendue pour ce param (impossible car code OK)"; []
				)
				| _->if !vDEBUG then  Printf.printf "erreur lvalue attendue pour ce param (impossible car code OK)"; []
			)
		| BINARY (_,_,_)-> (* on peut avoir en paramètre ptr +i*)
			[new_instVar 	(expressionToString  "" valeurParam 0) (EXP (UNARY(MEMOF, expressionAffectation)))]
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
		| MEMBEROFPTR (e , t) 	->	let lid =	getInitVarFromStruct e  in
					if lid != [] then 
					begin
						
						let (btype, id) =  ( getBaseType (List.assoc (List.hd lid) !listAssocIdType) , List.hd lid)  in
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
	if par = [] or args = [] then ()
	else
	begin
		analyse_expression (BINARY(ASSIGN, VARIABLE(List.hd(par)), List.hd(args)));
		contruireAux (List.tl par) (List.tl args)
	end			
																
and  construireAsAppel dec	appel =
 	let (_, _, name) = dec in 
 	let (_, typep, _, _) = name in
 	let base = get_base_type typep in
 	let liste =
		(match base with
			PROTO (_, pars, _) -> List.map( fun pc -> let (_, _, n) = pc in let (id, _, _, _) = n in id)  pars 
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
			analyse_expressionaux e;	
			let ne = !nouvExp in
			(match op with		(*je ne distingue pas pre et post operation linearise attention aux conditions *)
				PREINCR  -> 	affectationUnaire ADD ne
				| POSINCR -> 	
					let p = !listeDesInstCourantes in
								listeDesInstCourantes := [];
								affectationUnaire ADD ne ;
								listeNextExp :=  List.append !listeNextExp !listeDesInstCourantes;
								listeDesInstCourantes := p;
								
				| PREDECR  ->   affectationUnaire SUB ne
				| POSDECR ->  
					let p = !listeDesInstCourantes in
								listeDesInstCourantes := [];
								affectationUnaire SUB ne ;
								listeNextExp :=  List.append !listeNextExp !listeDesInstCourantes;
								listeDesInstCourantes := p;
				| ADDROF	->(** "&" . nouvExp :=VARIABLE("&"^v)*)
					(match e with
						INDEX (t,i) ->
(*Printf.printf "adresse de...\n";print_expression e 0; new_line(); *)
							let (tab,lidx) = analyseArray e []  in
							if tab = "" then nouvExp := exp
							else 
							begin
(*								let sygmaIndex = getSygma lidx in*)
								let sygmaIndex = (*(CONSTANT(CONST_INT("0"))) in*)
										if lidx = [] then NOTHING else if (List.tl lidx) = [] then (CONSTANT(CONST_INT("0"))) else  i in
								nouvExp := BINARY (ADD, (VARIABLE(tab)), sygmaIndex) ;
(*print_expression !nouvExp 0; new_line(); Printf.printf "adresse de...\n";*)
							end
						| _->
								nouvExp := exp)
				|_ -> 		if !vDEBUG then Printf.printf "non traite\n";nouvExp := UNARY (op, ne) 
			);
		

	| BINARY (op, exp1, exp2) -> 
		analyse_expressionaux exp1 ;
		let ne1 = !nouvExp in 	
		analyse_expressionaux exp2;	
		let ne = !nouvExp in   
		(	match op with		
			ASSIGN		->
			(	match exp1 with
				VARIABLE n ->  
					let newaffect =new_instVar  n  (EXP(ne)) in
						(* afficherUneAffect newaffect; flush(); new_line(); *)
					listeDesInstCourantes := List.append !listeDesInstCourantes  [newaffect]
				|INDEX (t,i)-> 
					( match t with 
						VARIABLE v -> listeDesInstCourantes := List.append !listeDesInstCourantes 
									[new_instTab v (EXP(i))	(EXP(ne))]
						| UNARY (opr,e) ->
							(
								match e with
								VARIABLE v ->
								(
									match opr with
									MEMOF		->
					(** "*" operator. *)(* revoir e n'est pas forcement une variable *)
										listeDesInstCourantes := 
											List.append !listeDesInstCourantes 
														[new_instTab ("*"^v) (EXP(i))	(EXP(ne))]
									| ADDROF	->(** "&" operator. *)
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
					let p = !listeNextExp in
					analyse_expressionaux e ;
					listeNextExp := p;
					let neunary = !nouvExp in 	
					(
						match opr with
							MEMOF		->

								(match neunary with
								  VARIABLE v ->
									(** "*" operator. *)
									(*afficherUneAffect( new_instMem ("*"^v) (EXP(VARIABLE(v))) (EXP(ne))); flush(); new_line(); *)
									listeDesInstCourantes := List.append !listeDesInstCourantes 
																		[new_instMem ("*"^v) (EXP(VARIABLE(v))) (EXP(ne))]
								  | UNARY(ADDROF,expaux)	->(** "&" operator. *)
									(match expaux with
									 VARIABLE v ->
										listeDesInstCourantes := List.append !listeDesInstCourantes  [new_instVar v 	(EXP(ne))]
								     |_->if !vDEBUG then Printf.printf "expr pour tableau  non traitée\n" )
								|_->if !vDEBUG then Printf.printf "expr pour tableau  non traitée\n" )
					
							
							| ADDROF	->(** "&" operator. *)
								(match neunary with
								  VARIABLE v ->
									  listeDesInstCourantes := List.append !listeDesInstCourantes 
																			[new_instVar ("&"^v) 	(EXP(ne))]
									| UNARY(MEMOF,expaux)	->(** "&" operator. *)
										(match expaux with
										VARIABLE v ->
											listeDesInstCourantes := List.append !listeDesInstCourantes  [new_instVar v 	(EXP(ne))]
										|_->if !vDEBUG then Printf.printf "expr pour tableau  non traitée\n" )
									|_->if !vDEBUG then Printf.printf "expr pour tableau  non traitée\n" )

							|  _->	 if !vDEBUG then Printf.printf "expr pour tableau  non traitée\n" 	 )
						
				 (*  *)
				 | MEMBEROF (e , t) 			
				 | MEMBEROFPTR (e , t) 	->		
						let lid =	getInitVarFromStruct e  in
						if lid != [] then 
						begin
						
							let (btype, id) =  ( getBaseType (List.assoc (List.hd lid) !listAssocIdType) , List.hd lid)  in
							(*Printf.printf "varDefList id %s type :\n"id; printfBaseType btype;new_line();*)
							let nee = consCommaExp (VARIABLE(id)) btype [id] lid ne  in
							let newaffect = new_instVar id (EXP(nee) ) in
							
							listeDesInstCourantes := List.append !listeDesInstCourantes  [newaffect];
						end;
					
	
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
				analyse_expressionaux exp1 ;
				let ne1 = !nouvExp in
				analyse_expressionaux exp2;
				let ne2 = !nouvExp in
				analyse_expressionaux exp3;
				let ne3 = !nouvExp in 
    			nouvExp:=QUESTION (ne1, ne2, ne3)
																					
	| CAST (t, e) 						->  analyse_expressionaux e ; nouvExp:=CAST (t, !nouvExp) 
	| CALL (e , args) 				->		
				(* List.iter (fun ep -> analyse_expression ep) args;*)
				 
				let listeInstPred = !listeDesInstCourantes in
				idAppel := !idAppel + 1;
				let ida = !idAppel in									
				if existeFonction (nomFonctionDeExp e) then 
				begin

					let fonction = rechercheFonction (nomFonctionDeExp e) in
					let (_, f) = fonction in
					listeDesInstCourantes := [];
					construireAsAppel f.declaration	exp ;

					listeBoucleOuAppelCourante	:= 
						List.append  !listeBoucleOuAppelCourante  [IDAPPEL(!idAppel, exp, !listeDesInstCourantes,"", !trueList,!falseList )];
					traiterAppelFonction e args !listeDesInstCourantes;
					
					let nouvar = Printf.sprintf "call%s%d" (nomFonctionDeExp e) ida in
					let nouvarres = Printf.sprintf "res%s" (nomFonctionDeExp e) in
					let newaffect = new_instVar  (nouvar)  (EXP(VARIABLE(nouvarres))) in
					listeDesInstCourantes :=  List.append !listeDesInstCourantes  [newaffect];
					listeDesInstCourantes :=  List.append listeInstPred !listeDesInstCourantes ;
					nouvExp:=VARIABLE(nouvar)
				end
				else 
				begin 
					List.iter (fun ep -> analyse_expressionaux ep) args;

					listeBoucleOuAppelCourante	
						:= List.append  !listeBoucleOuAppelCourante [IDAPPEL(!idAppel, exp,!listeDesInstCourantes,"" , !trueList,!falseList )];
					traiterAppelFonction e args !listeDesInstCourantes;
					let nouvar = Printf.sprintf "call%s%d" (nomFonctionDeExp e) ida in
					let nouvarres = Printf.sprintf "res%s" (nomFonctionDeExp e) in
					let newaffect = new_instVar  (nouvar)  (EXP(VARIABLE(nouvarres))) in
					listeDesInstCourantes :=  List.append !listeDesInstCourantes  [newaffect];
					listeDesInstCourantes :=  List.append listeInstPred !listeDesInstCourantes ;
					(*nouvExp:=VARIABLE(nouvar)*)nouvExp:=exp
				end		;
	| COMMA e 	-> (*Printf.printf "dans comma\n";print_expression exp 0; new_line();*) List.iter (fun ep -> analyse_expressionaux ep) e;
					nouvExp:=COMMA(e)
	| MEMBEROF (e , t) 			(*->	analyse_expression e ;  nouvExp:=MEMBEROF (!nouvExp , t)*)
	| MEMBEROFPTR (e , t) 	->	(*Printf.printf "dans ptr\n";print_expression exp 0; new_line();	*)analyse_expressionaux e ; nouvExp:=MEMBEROFPTR (!nouvExp , t) (*nouvExp:=exp*)
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
	| _->nouvExp:=exp

(* je suppose que pas d'appel de fonction dans les arguments de la fonction, peut être déjà traité 
par Hugues dans ces réécriture lui demander quand il aura le temps ...*)		

and convael l =
if l = [] then []
else
begin
analyse_expression (List.hd l);
let n = !nouvExp in
List.append [n] (convael  (List.tl l)  )
end
									
and ajouterReturn nomF lesAffectations =
	let nouvarres = Printf.sprintf "res%s" nomF  in
	
	if lesAffectations = [] then begin  ()end
	else
	begin
		
		let asl = evalStore (new_instBEGIN(lesAffectations)) [] in
		if existAffectVDsListeAS nouvarres !listeASCourant then
		begin 
			let resaux = rechercheAffectVDsListeAS nouvarres (*index*) asl in
			listeASCourant := [];
			if resaux <> EXP(NOTHING) then
			begin
				let newaffect = new_instVar  nouvarres resaux in
				sorties := List.append !sorties [newaffect]
			end		
		end
		
	end
	

and traiterAppelFonction exp args init =
	let nom = nomFonctionDeExp exp in (* il faut construire la liste d es entrées et la liste des sorties*)
	if existeFonction nom then
	begin
		let fonction = rechercheFonction nom in
		let (_, f) = fonction in
		let aff =  f.lesAffectations in
		if f.lesAffectations = [] then   aUneFctNotDEf := true;
		entrees := [];
	    sorties := [];
(*Printf.printf"Call %s existe traiterAppelFonction avant construire\n" nom;*)
		construireListesES f.listeES args;
(*Printf.printf"Call %s existe traiterAppelFonction apres construire\n" nom;*)
		ajouterReturn nom aff;
(*Printf.printf"Call %s existe traiterAppelFonction apres ajouter return\n" nom;*)
		listeDesInstCourantes :=  [ new_instAPPEL !idAppel  (new_instBEGIN init)  f.nom (new_instBEGIN !sorties) (new_instBEGIN aff) ""]
	end

(* pour variables *)
and analyse_defs defs = List.iter	(fun def ->		analyse_def def)		defs

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
						ARRAY (t, dim) -> majAssosArrayIDsize id typ; (* a cause des renommages je pense que cela suffit*)
							(match calculer  (EXP(dim)) !infoaffichNull  [] with ConstInt(s)-> (true,(int_of_string  s)) |_->(true,0))
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
					match typ with ARRAY (t, dim) -> majTypeDefAssosArrayIDsize id typ; () |ENUM(_,_)->consEnum typ;()
									 |_->let base = get_base_type typi in 
											(match base with ENUM(_,_) ->consEnum  base ;()|_->());()
					) namelist; ;
		
		()
	| ONLYTYPEDEF n -> 
		let (typ, sto, namelist) = n in 
		List.iter  (fun name -> 
					let (id,typ, _, exp) = name in  
					match typ with ARRAY (t, dim) -> majTypeDefAssosArrayIDsize id typ; () |ENUM(_,_)->consEnum typ;|_->()
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
										let nouvarres = Printf.sprintf "res%s" !nomFctCour  in
										let newaffect = new_instVar  (nouvarres)  (EXP(ne))in
										listeDesInstCourantes :=  List.append ( List.append !listeDesInstCourantes  [newaffect]) !listeNextExp
									end
	| SWITCH (exp, stat) ->			
									onlyAexpression   exp ;


									let ne = !nouvExp in   
									idSwitch := !idSwitch + 1;
									let varIfNaux =  Printf.sprintf "%s_%d" "SW" !idSwitch  in	 
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
				(*| MEMOF -> 	
					(match e with
						NOTHING ->  nouvExp := exp
						| UNARY (op, e2) ->
							(match op with
							  ADDROF -> analyse_expression e2;
							| PREINCR | PREDECR  | POSINCR  | POSDECR -> onlyAexpression (UNARY(op, UNARY(MEMOF, e2)));
							| _->onlyAexpression e;	nouvExp := UNARY (op, !nouvExp))
						| _->onlyAexpression e;	 nouvExp := UNARY (op, !nouvExp))
						(* "*" *)(* revoir e n'est pas forcement une variable nouvExp :=VARIABLE("*"^v)*)*)
				| ADDROF	->(** "&" . nouvExp :=VARIABLE("&"^v)*)
					(match e with
						INDEX (t,i)->
(* Printf.printf "adresse de...\n"; print_expression e 0; new_line();*)
							let (tab,lidx) = analyseArray e []  in
							if tab = "" then nouvExp := exp
							else 
							begin
(*								let sygmaIndex = getSygma lidx in*)
											
								let sygmaIndex = (*(CONSTANT(CONST_INT("0"))) in*)
										if lidx = [] then NOTHING else if (List.tl lidx) = [] then (CONSTANT(CONST_INT("0"))) else  i in
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
				if existeFonction (nomFonctionDeExp e) then 
				begin
					let fonction = rechercheFonction (nomFonctionDeExp e) in
					let (_, f) = fonction in
					listeDesInstCourantes := [];
					construireAsAppelAux f.declaration	exp ;(*pb si arg est un appel de fonction revoir*)
					onlytraiterAF e args !listeDesInstCourantes;
					
					let nouvar = Printf.sprintf "call%s%d" (nomFonctionDeExp e) 0 in
					let nouvarres = Printf.sprintf "res%s" (nomFonctionDeExp e) in
					let newaffect = new_instVar  (nouvar)  (EXP(VARIABLE(nouvarres))) in
					listeDesInstCourantes :=  List.append !listeDesInstCourantes  [newaffect];
					listeDesInstCourantes :=  List.append listeInstPred !listeDesInstCourantes ;
					nouvExp:=VARIABLE(nouvar)
				end
				else nouvExp:=exp
			 
	| COMMA e 				->  (*Printf.printf "dans only comma\n";print_expression exp 0; new_line();*) List.iter (fun ep -> onlyAexpression ep) e; nouvExp:=COMMA(e)
	| MEMBEROF (e , t) 		
	| MEMBEROFPTR (e , t) 	->		onlyAexpression e ; nouvExp:=exp
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
	if par = [] or args = [] then ()
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
	if existeFonction nom then
	begin
		let fonction = rechercheFonction nom in
		let (_, f) = fonction in
		let proto = f.declaration in
		let r = !idAppel in
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
		entrees := [];
	    sorties := [];
		construireListesES f.listeES args;
		ajouterReturn nom aff;
		listeDesInstCourantes :=  [ new_instAPPEL r  (new_instBEGIN init)  f.nom (new_instBEGIN !sorties) (new_instBEGIN aff) ""];()
	end

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
		let nval = calculer  (EXP(exp)) !infoaffichNull  [] in
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
								let glo = evalStore 	(new_instBEGIN !listeDesInstGlobales) []	in
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
							ARRAY (t, dim) -> majAssosArrayIDsize id typ; (* a cause des renommages je pense que cela suffit*)
								(match calculer  (EXP(dim)) !infoaffichNull  [] with ConstInt(s)-> (true,(int_of_string  s)) |_->(true,0))
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
					match typ with ARRAY (t, dim) -> majTypeDefAssosArrayIDsize id typ; () |ENUM(_,_)->consEnum typ;()
									 |_->let base = get_base_type typei in 
											(match base with ENUM(_,_) ->consEnum  base ;()|_->());()
					
					) namelist;
		
		()
	| ONLYTYPEDEF n -> 
		let (typ, sto, namelist) = n in 
		List.iter  (fun name -> 
					let (id,typ, _, exp) = name in (*Printf.printf "id : %s\n" id;*)
					match typ with ARRAY (t, dim) -> majTypeDefAssosArrayIDsize id typ; () |ENUM(_,_)->consEnum typ;()
				|_->()
					) namelist;
		()

