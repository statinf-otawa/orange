(* orange -- eval loop bound and eval flowfact 
**
** Project:	O_Range
** File:	orange.ml
** Version:	1.1
** Date:	11.7.2008
** Author:	Marianne de Michiel
*)

open Cabs
open Cxml
open Cprint
open Cexptostr
open Cvarabs
open Cvariables
open Rename

(*open Cevalexpression*)
open Cextraireboucle

let version = "orange Marianne de Michiel"
let enTETE = ref false
let numAppel = ref 0
let estNulEng = ref false
let estDansBoucle = ref false
let varDeBoucleBoucle = ref""

(*type boucleEval idem fonction eval*) 
type evaluationType =
	TBOUCLE   of     int* int * listeDesInst  *  typeListeAS (*numero boucle, numero appel+corsp+contexte *)* bool* string list * string list
|	TFONCTION of 	string * int * listeDesInst * listeDesInst *  typeListeAS * listeDesInst(*nom +id appel+corps+affectappel*) * string list * string list *bool (*is exe*)*bool (*idintoloop*)

type resMaxType =
	EVALEXP   of    expressionEvaluee
|	EXPMAX of 	expression list


(* string list * string list is the true conditionnal list and the false one on whith the call or loop execution depend on *)

(*type resEval of int *int **)


let  afficheEvaluationType liste =
List.iter (fun e -> 
			match e with
				TBOUCLE (num, numa,_,_,_,_,_)-> Printf.printf "Boucle %d dans appel %d\n" num numa
				|TFONCTION(num, numa,_,_, _, _,_,_,_,_)-> Printf.printf "Fonction %s dans appel %d\n" num numa
)liste

let listeDesMaxParIdBoucle = ref []
let existeAssosBoucleIdMax id = List.mem_assoc id  !listeDesMaxParIdBoucle
let getAssosBoucleIdMax id = List.assoc id !listeDesMaxParIdBoucle


let setAssosBoucleIdMaxIfSupOldMax id newmax  =
	if existeAssosBoucleIdMax id then
	begin
		let om = getAssosBoucleIdMax id in
		let maximum = 
			(match newmax with
				EVALEXP(max)->
					(match om with
						EVALEXP(oldMax)->
							if estDefExp oldMax && estDefExp  max then EVALEXP(maxi oldMax max) 
							else 	
								if oldMax != max then 
									EXPMAX (List.append [expressionEvalueeToExpression oldMax] [expressionEvalueeToExpression max] )
								else om  
						|EXPMAX(l) -> 
							if List.mem (expressionEvalueeToExpression max) l then om 
							else EXPMAX(List.append [expressionEvalueeToExpression max] l) )
				|EXPMAX(ml) -> 
					(match om with
						EVALEXP(oldMax)->
							if List.mem (expressionEvalueeToExpression oldMax) ml 
								then newmax else EXPMAX (List.append [expressionEvalueeToExpression oldMax] ml )  
											
							|EXPMAX(l) -> if ml<>[] then begin if List.mem (List.hd ml) l then om else EXPMAX(List.append ml l) end
										  else om)
				
			) in
		listeDesMaxParIdBoucle := List.remove_assoc id !listeDesMaxParIdBoucle;
		listeDesMaxParIdBoucle := List.append [(id, maximum)] !listeDesMaxParIdBoucle
	end
	else  listeDesMaxParIdBoucle := List.append [(id, newmax)] !listeDesMaxParIdBoucle


let typeNidTeteCourant = ref (TBOUCLE(0,0,[], [], true,[], []))
let dernierAppelFct = ref  (TFONCTION(!(!mainFonc),0,[], [], [], [],[], [], true,false))
let predDernierAppelFct  = ref  (TFONCTION(!(!mainFonc),0,[], [], [], [],[],[], true, false))
type nidEval =
{
	condition : expVA;
	inf : expVA;
	sup : expVA;
	inc : expVA;
	sensVariation : sens;
 	idBoucleN : evaluationType;
	expressionBorneUneIt : expression;
	expressionBorneToutesIt : expVA;
	varDeBoucleNidEval : string;
	op : binary_operator ;
	expMaxUneIt : expVA;
	maxUneIt : expVA;
	isExecuted : bool;
	isIntoIf : bool
}

type elementEval =
		BOUCLEEVAL of nidEval * evaluationType *elementEval list
	|	APPELEVAL of evaluationType * expVA *elementEval list

let new_elementEvalb nid n l = BOUCLEEVAL(nid, n, l)
let new_elementEvala n e l=	APPELEVAL (n,e,l)
let corpsEvalTMP = ref [] 
let nouBoucleEval = ref []

let new_nidEval e t e1 e2 var i s incr sensV o n expMax b isi =
{
	condition = e;
	inf =i; 
	sup=s;
	inc =incr;
	sensVariation = sensV;
	idBoucleN = t;
	expressionBorneUneIt = e1;
	expressionBorneToutesIt = e2;	
	varDeBoucleNidEval = var;
	op = o;
	maxUneIt = n;
	expMaxUneIt = expMax;
	isExecuted = b;
	isIntoIf = isi
}
						
type 	documentEvalue =
{
		maListeNidEval:nidEval list;(* transitoire*)
		maListeEval: elementEval list;
}

let new_documentEvalue  listeN listeF =
{
		maListeNidEval = listeN;
		maListeEval = listeF;
}

let docEvalue = ref (new_documentEvalue  [] [])
let appelcourant = ref  [] 

let reslisteSAUFID = ref []
let estTROUVEID = ref false


let rec jusquaB listeInst saufId  =
	if !estTROUVEID then ()
	else
	begin
		if listeInst <> [] then 
		begin
				jusquaPourBoucle (List.hd listeInst) saufId ;
				if !estTROUVEID != true then
				 	jusquaB (List.tl listeInst) saufId ;
				()						
		end
		else  ()
	end

and jusquaPourBoucle premiere sId =
  match premiere with
  FORV ( num, _, _, _, _, _, i) -> 
		if num != sId then 
		begin 
			reslisteSAUFID:=(List.append !reslisteSAUFID [premiere]);
		end 
		else begin estTROUVEID := true;  end	;
		()
  |VAR(_,_)|TAB(_,_,_) |APPEL (_,_, _, _,_,_)| MEMASSIGN(_,_,_)-> reslisteSAUFID:=List.append !reslisteSAUFID [premiere];()						
  |IFVF(_, i1, i2)->if (!estDansBoucle = true) then
		begin
			jusquaPourBoucle i1 sId;  if !estTROUVEID =false then jusquaPourBoucle i2 sId; 
		end
		else
		begin  
			let preced = !reslisteSAUFID in
			reslisteSAUFID := [];
			jusquaPourBoucle i1 sId;  

			if !estTROUVEID =false then 
			begin
			(*	let iftrue = !reslisteSAUFID in*)
				reslisteSAUFID := [];

				jusquaPourBoucle i2 sId; 
				if !estTROUVEID =false then reslisteSAUFID := (List.append preced [premiere])
				else reslisteSAUFID :=List.append preced !reslisteSAUFID ;
			end
			else reslisteSAUFID :=List.append preced !reslisteSAUFID ; 	
		end;		()					
	| IFV ( _, i1) 		-> 
		if (!estDansBoucle = true) then
		begin
			jusquaPourBoucle i1 sId;  
		end
		else
		begin  
			let preced = !reslisteSAUFID in
			reslisteSAUFID := [];
			jusquaPourBoucle i1 sId;  

			if !estTROUVEID =false then  reslisteSAUFID := (List.append preced [premiere])
			else reslisteSAUFID :=List.append preced !reslisteSAUFID ; 
		end;					
		()
  |BEGIN (liste)	->  jusquaB liste sId; ()

let rec jusquaF listeInst saufId  =
	if !estTROUVEID then ()
	else
	begin
		if listeInst <> [] then 
		begin
				jusquaPourF (List.hd listeInst) saufId ;
				if !estTROUVEID != true then jusquaF (List.tl listeInst) saufId ;()								
		end
		else  ()
	end

and jusquaPourF premiere saufId =
	match premiere with
	  FORV ( _, _, _, _, _, _, i) ->  jusquaPourF i saufId	;()							
	| VAR ( _, _) |TAB ( _, _, _) | MEMASSIGN(_,_,_)-> reslisteSAUFID := (List.append !reslisteSAUFID [premiere]);()						
	| APPEL (num,_, _, _,_,_) ->
		if num != saufId then begin reslisteSAUFID :=(List.append !reslisteSAUFID [premiere]);() end
		else begin estTROUVEID := true; appelcourant := [premiere]; ()			 end
	| IFVF ( _	, i1, i2) -> 
		begin  
			let preced = !reslisteSAUFID in
			reslisteSAUFID := [];
			jusquaPourF i1 saufId;  

			if !estTROUVEID =false then 
			begin
				(*let iftrue = !reslisteSAUFID in*)
				reslisteSAUFID := [];

				jusquaPourF i2 saufId; 
				if !estTROUVEID =false then reslisteSAUFID := (List.append preced [premiere])
				else reslisteSAUFID :=List.append preced !reslisteSAUFID ;()
			end
			else reslisteSAUFID :=List.append preced !reslisteSAUFID ; ()	
		end;							
	| IFV ( _, i1) 		-> 
		begin  
			let preced = !reslisteSAUFID in
			reslisteSAUFID := [];
			jusquaPourF i1 saufId;  

			if !estTROUVEID =false then  reslisteSAUFID := (List.append preced [premiere])
			else reslisteSAUFID :=List.append preced !reslisteSAUFID ; ()	
		end;							
	| BEGIN (liste)		->  jusquaF liste saufId; ()
	


let rec nextInstructionsB id inst=
(*Printf.printf "nextInstructionsB\n";*)
if inst = [] then []
else
begin
	let (premiere, suite) =(List.hd inst, List.tl inst)in
	match premiere with
	  FORV ( num, _, _, _, _, _, _) 	-> if num = id then suite else	nextInstructionsB id suite				
	| VAR ( _, _) |TAB ( _, _, _) | MEMASSIGN(_,_,_)-> nextInstructionsB id suite						
	| APPEL (num,_, _, _,_,_) ->     nextInstructionsB id suite		
	| IFVF ( c, i1, i2) -> 
		  
			let c1 = nextInstructionsB id [i1] in
			let c2 = nextInstructionsB id [i2] in
			if  c1 = [] && c2 = [] then nextInstructionsB id suite		
			else List.append [IFVF ( c, BEGIN(c1), BEGIN(c2))] (nextInstructionsB id suite)
			
	| IFV ( c, i1) 		-> 
			let c1 = nextInstructionsB id [i1]  in
			if  c1 = []  then nextInstructionsB id suite		
			else List.append [IFV ( c,  BEGIN(c1))] (nextInstructionsB id suite)						
	| BEGIN (liste)		-> 
		let top =  (nextInstructionsB id liste) in
		if top = [] then (nextInstructionsB id suite)
		else		 List.append [BEGIN (top)] (nextInstructionsB id suite)

end

let rec nextInstructionsF id inst=
(*Printf.printf "nextInstructionsF\n";*)
if inst = [] then []
else
begin
	let (premiere, suite) =(List.hd inst, List.tl inst)in
	match premiere with
	  FORV ( _, _, _, _, _, _, _) 					
	| VAR ( _, _) |TAB ( _, _, _)| MEMASSIGN(_,_,_) -> nextInstructionsF id suite						
	| APPEL (num,_, _, _,_,_) ->    if num = id then suite else nextInstructionsF id suite		
	| IFVF ( c, i1, i2) -> 
		  
			let c1 = nextInstructionsF id [i1]  in
			let c2 = nextInstructionsF id [i2]  in
			if  c1 = [] && c2 = [] then nextInstructionsF id suite		
			else  List.append [IFVF ( c, BEGIN(c1), BEGIN(c2))]  (nextInstructionsF id suite)
			
	| IFV ( c, i1) 		-> 
			let c1 = nextInstructionsF id [i1]  in
			if  c1 = []  then nextInstructionsF id suite		
			else List.append [IFV ( c,  BEGIN(c1))] (nextInstructionsF id suite)						
	| BEGIN (liste)		-> 
		let top =  (nextInstructionsF id liste) in
		if top = [] then (nextInstructionsF id suite)
		else		 List.append [BEGIN (top)] (nextInstructionsF id suite)
end	

let  jusquaFaux listeInst saufId  contexte =
	listeASCourant := [];
	reslisteSAUFID := [] ;
	estTROUVEID := false;
	jusquaF listeInst saufId ;
	evalStore (new_instBEGIN(!reslisteSAUFID)) contexte	;
	!listeASCourant

let rec listeSAUFIDB listeInst sId  l=
  if listeInst <> [] then  List.append [traiterUneIntructionPourBoucle (List.hd listeInst) sId l] (listeSAUFIDB (List.tl listeInst) sId l)
  else  []

and traiterUneIntructionPourBoucle premiere sId  l=
	match premiere with
	FORV ( n, a, b, c, d, e, i) ->  if (n = sId) then BEGIN(l) else FORV (n,a,b,c,d,e, traiterUneIntructionPourBoucle i sId l) 
	| IFVF ( c, i1, i2) ->  IFVF (c, traiterUneIntructionPourBoucle i1 sId l, traiterUneIntructionPourBoucle i2 sId l) 
	| IFV ( c, i1) 		->  IFV ( c, traiterUneIntructionPourBoucle i1 sId l)				
	| BEGIN (liste)		->  BEGIN (listeSAUFIDB liste sId l)
	| APPEL (num, avant, nom, apres,corps,x) -> APPEL (num, avant, nom, apres, traiterUneIntructionPourBoucle corps sId l,x) 
	|_-> premiere
		
let  evalSIDB listeInst saufId contexte  l=
	listeASCourant := [];
	evalStore (new_instBEGIN(listeSAUFIDB listeInst saufId  l)) contexte	;
	!listeASCourant

let rec estDansListeInstBoucle l id =
if l = [] then false
else estDansCorpsBoucle (List.hd l) id || estDansListeInstBoucle (List.tl l) id

and  estDansCorpsBoucle corps id =
	match corps with
	FORV ( num, a, b, c, d, e, i) 	->  if (num = id) then true else estDansCorpsBoucle i id 
	| IFVF ( c, i1, i2) 			->  estDansCorpsBoucle i1 id || estDansCorpsBoucle i2 id
	| IFV ( c, i1) 					->  estDansCorpsBoucle i1 id 		
	| BEGIN (liste)					->  estDansListeInstBoucle liste id 
	|_->  false		
					
let  jusquaBaux listeInst saufId contexte =
	listeASCourant := [];
	reslisteSAUFID := [] ;
	estTROUVEID := false;
	jusquaB listeInst saufId ;
	evalStore (new_instBEGIN(!reslisteSAUFID)) contexte	;
	!listeASCourant

let lesVardeiSansj nEC n l=
	let saufId = (getBoucleInfoB (n.infoNid.laBoucle)).identifiant in
	(*Printf.printf"lesVardeiSansj de i = %d et j = %d \n" (getBoucleInfoB (nEC.infoNid.laBoucle)).identifiant saufId;*)
	let listeInter =  listeSAUFIDB (reecrireCallsInLoop nEC.varDeBoucleNid 	nEC.lesAffectationsBNid)   saufId  l in
	listeASCourant := [];
	evalStore  (new_instBEGIN(listeInter)) []	;
	!listeASCourant

let rec recherche numappel liste =
if liste = [] then TFONCTION(!(!mainFonc),0,[], [], [], [],[],[], true,false)
else
begin
	let pred = (List.hd liste) in
	match pred with 
	TBOUCLE(_, _,_,_,_,_,_) -> recherche numappel (List.tl liste) 
	| TFONCTION (_, numF,_,_, _,_,_,_,_,_)  -> if numF = numappel then pred else recherche numappel (List.tl liste) 
end

let rec majlappel  liste le =
if liste = [] then  []
else
begin
	let premiere = List.hd liste in
	match premiere with 
	FORV ( n, a, b, c, d, e, i1) -> List.append [FORV (n,a,b,c,d,e,  (BEGIN (majlappel  [i1] le)) )] (majlappel (List.tl liste) le)
	| IFVF ( c, i1, i2) 	-> List.append  [IFVF ( c, (BEGIN (majlappel [i1]  le)), (BEGIN (majlappel [i2]  le))) ] (majlappel (List.tl liste) le)
	| IFV (c,i1)-> List.append  [IFV(c,(BEGIN (majlappel [i1]  le)))](majlappel (List.tl liste) le)
	| BEGIN (l)	->  List.append  [BEGIN (majlappel l le)] (majlappel (List.tl liste) le)		
	| APPEL (num, avant, nom, apres,corps,varB) -> 
		List.append [APPEL (num, avant, nom, apres, BEGIN (majlappel [corps] le)  , varB) ] (majlappel (List.tl liste) le)		
	|_-> List.append [premiere] (majlappel (List.tl liste) le)		
end

let filterIF l =
List.filter (fun e ->  match e with ASSIGN_SIMPLE (id, _)->
	if (String.length id > 3) then
		begin 
			if (String.sub id  0 3) = "IF_" then    true 	else false
		end 
	else(* if existAssosPtrNameType  id then true else*) false 
	|_->false ) l

let listeIF =ref[]

let rec listeSAUFIDA listeInst saufId ainserer output input le =
	if listeInst <> [] then 
	begin
		let premiere = List.hd listeInst in
		let suite = List.tl listeInst in
		
		let na = traiterUneIntructionPourAppel premiere saufId ainserer output input le in
		if !estTROUVEID then List.append  [na] (majlappel suite le)
		else  List.append (majlappel [premiere] le) (listeSAUFIDA suite saufId ainserer output input le) 		
	end
	else  []

and traiterUneIntructionPourAppel premiere sId ainserer output input le=
	match premiere with
	FORV (n,a,b,c,d,e,i) -> FORV (n,a,b,c,d,e, traiterUneIntructionPourAppel i sId ainserer output input le)			
	| IFVF ( c, i1, i2) 		-> 
		IFVF ( c, traiterUneIntructionPourAppel i1 sId ainserer output input le,
			 traiterUneIntructionPourAppel i2 sId ainserer output input le) 				
	| IFV (c,i1)-> IFV(c,traiterUneIntructionPourAppel i1 sId ainserer output input le)			
	| BEGIN (liste)		->  	BEGIN (listeSAUFIDA liste sId ainserer output input le)		
	|	APPEL (num, avant, nom, apres,corps,varB) ->
		let sorties = (match apres with BEGIN(sss)-> sss |_->[]) in
		let pred = rechercheTFonction le nom in 
		let corpsF =  match pred with TFONCTION(_,_,c,_,_,_,_,_,_,_) ->  BEGIN (c)|_->  corps in

		if num != sId then 
		begin
			let suite = traiterUneIntructionPourAppel corpsF sId ainserer output input le in
			let new_appel = APPEL (num, avant, nom, BEGIN(List.append sorties  (List.append !listeIF output)), suite,varB ) in
			new_appel
		end
		else 
		begin  
			appelcourant := [premiere]; 
			estTROUVEID := true;
			let aS = !listeASCourant in
			listeASCourant := [];
			evalStore  corpsF []	;
			listeIF :=listeAsToListeAffect (filterIF  !listeASCourant) ;
			(*Printf.printf "APPEL de %s \n " nom;
			Printf.printf "traiterUneIntructionPourAppel contexteAux dans eval FONCTION: \n";
								afficherListeAS !listeASCourant; Printf.printf "FIN CONTEXTE \n";*)

			(*let newinsert = List.map( )ainserer;*)
			listeASCourant := aS;

			let new_appel = APPEL (num, avant, nom, BEGIN(List.append sorties (List.append !listeIF output)),  
						BEGIN ( List.append !listeIF ainserer), varB)	in
			BEGIN (List.append input   [new_appel]);
		end
	|_-> premiere

and rechercheTFonction liste nom =
if liste <> [] then 
begin
	let pred = (List.hd liste) in
	match pred with
	TBOUCLE(_, _,_,_,_,_,_) -> rechercheTFonction (List.tl liste) nom 
	| TFONCTION(n,num,c,_,_,_,_,_,_,_) ->  if n = nom then pred else rechercheTFonction (List.tl liste) nom 
end	
else (TFONCTION(!(!mainFonc),0,[], [], [], [],[], [], true, false))

let existeappel l  saufId=  List.exists (fun i -> match i with APPEL (num,_, _, _,_,_) ->  num = saufId  |_-> false  )l	

let rechercheAppelCourant l saufId= List.find(fun i -> match i with  APPEL (num,_, _, _,_,_) ->  num = saufId |_-> false  )l	
	
let  evalSIDA listeInst saufId  contexte ainserer output input le =
	listeASCourant := [];
	estTROUVEID := false;
	listeIF := [];
	let nc = new_instBEGIN(listeSAUFIDA listeInst saufId ainserer output input le) in
(*Printf.printf "evalSIDA nc\n"; afficherUneAffect nc; Printf.printf "evalSIDA fin\n";*)
	evalStore  nc contexte	;
	!listeASCourant
													
let rechercherEvalParNomAppel nomF idB appel listeF=
 List.find 
(fun e -> 
	match e with 		
	  BOUCLEEVAL  (_,ty,_)->(match ty with TBOUCLE(ide, appele,_,_,_,_,_)-> idB = ide && appele = appel |_-> false)
	| APPELEVAL (ty,_,_)->(match ty with TFONCTION(nom, appele,_,_,_, _,_,_,_,_)-> nom = nomF && appele = appel|_->false)
)listeF

let rec isExecutedNidEval id appel listeEval =
	if listeEval = [] then false
	else
	begin 
		match (List.hd listeEval).idBoucleN  with
		TBOUCLE(ide, appele,_,_,_,_,_)  ->
			if (id = ide) && (appele = appel) then (List.hd listeEval).isExecuted
			else  isExecutedNidEval id appel (List.tl listeEval)
		| _ -> isExecutedNidEval id appel (List.tl listeEval)		
	end


let rec allerJusquaFonction liste =
if liste = [] then []
else
begin
	match (List.hd liste) with TBOUCLE(_, _,_,_,_,_,_) -> allerJusquaFonction (List.tl liste)  | TFONCTION(_,_,_,_,_,_,_,_,_,_) -> liste
end

let rec rechercheDerniereBoucle liste =
	let pred = (List.hd liste) in
	match pred with
	TBOUCLE(a, b,c,d,isExeE,lt,lf) -> (a, b, c,d,isExeE,lt,lf, List.tl liste)
	| TFONCTION(n,_,_,_,_,_,_,_,_,_) ->  dernierAppelFct := pred; rechercheDerniereBoucle  (List.tl liste)

let rec rechercheDernierAppel liste =
	let pred = (List.hd liste) in
	match pred with
	TBOUCLE(a, b,c,d,isExeE,lt,lf) -> rechercheDernierAppel (List.tl liste)
	| TFONCTION(_,_,_,_,_,_,_,_,_,_) ->  dernierAppelFct := pred



let rec rechercheDerniereBoucleApresId id liste =
let pred = (List.hd liste) in
	match pred with
	TBOUCLE(idb, _,_,_,_,_,_) ->
	(*	Printf.printf "rechercheDerniereBoucleApresId boucle cour %d boucle cherchee %d" idb id;*)
		if idb = id then 
		begin
			let (a,b,c,d,isExeE,lt,lf,_) = rechercheDerniereBoucle (List.tl liste) in (a,b,c,d,isExeE,lt,lf)
		end
		else rechercheDerniereBoucleApresId  id (List.tl liste)
	| TFONCTION(n,_,_,_,_,_,_,_,_,_) -> 
		(*Printf.printf "rechercheDerniereBoucle fonction courante %s boucle cherchee %d " n id ;*)
		dernierAppelFct := pred; rechercheDerniereBoucleApresId  id (List.tl liste)

let rec existeDerniereBoucle liste =
	if liste = [] then false
	else 
	begin
		match List.hd liste with
			TBOUCLE(_, _,_,_,_,_,_) -> true | TFONCTION(_,_,_,_,_,_,_,_,_,_) -> existeDerniereBoucle ( List.tl liste)
	end

let rec rechercheNbTotalIti id appel listeEval =
	if listeEval = [] then EXP(NOTHING)
	else
	begin 
		match (List.hd listeEval).idBoucleN  with
		TBOUCLE(ide, appele,_,_,_,_,_)  ->
			if (id = ide) && (appele = appel) then (List.hd listeEval).expressionBorneToutesIt
			else  rechercheNbTotalIti id appel (List.tl listeEval)
		| _ -> rechercheNbTotalIti id appel (List.tl listeEval)		
	end

let  rec existeNidContenant liste  id =
	if liste = [] then false
	else
	begin
		let (listeInt,_,_ ) = (List.hd liste) in
		if List.mem id listeInt then true else existeNidContenant (List.tl  liste) id
	end

let rec rechercheNidContenant liste  id =
	if liste = [] then []
	else
	begin
		let (listeInt,_,_ ) = (List.hd liste) in
		if List.mem id listeInt then [(List.hd liste)]
		else rechercheNidContenant (List.tl  liste) id
	end

let nomFonctionDansDeclaration dec = 
let (_, _, name) = (dec) in 
let (s,_,_,_) = name in s

let existeFonctionParNom nom  doc=
List.exists (fun (_, f) ->  let (_, _, name) = (f.declaration) in 
							let (s,_,_,_) = name in s = nom  )!doc.laListeDesFonctions

let rechercherFonctionParNom nom docu =
	List.find (fun (_, f) ->  	let (_, _, name) = (f.declaration) in 
								let (s,_,_,_) = name in s = nom  )!docu.laListeDesFonctions

let existeFonctionParNom nom docu =
	List.exists (fun (_, f) ->  let (_, _, name) = (f.declaration) in 
								let (s,_,_,_) = name in s = nom  )!docu.laListeDesFonctions
		
let existeEvalParNom t  listeF= List.exists (fun e -> match e with 		
												BOUCLEEVAL  (n,ty,l) ->t = ty
											|	APPELEVAL (ty,e,l)  ->t = ty   )listeF	
															
let rechercherEvalParNom t listeF= List.find (fun e -> match e with 		
												BOUCLEEVAL  (n,ty,l) ->t = ty
											|	APPELEVAL (ty,e,l)  ->t = ty   )listeF
let resAuxTN = ref MULTIPLE
let maxAuxTN = ref MULTIPLE
let isIntoIfLoop = ref false
let isEnd = ref false
let isEndNONZERO = ref false

let afficheUnNidEval n =
	new_line ();
	match n.idBoucleN with
	TBOUCLE(num, a, _,_,_,_,_)->	
		Printf.printf  "\n/*\t\tBoucle id %d id appel %d\n" num a;	new_line ();
		Printf.printf  "\n/*\t\tDans boucle nom variable de boucle %s\n"  n.varDeBoucleNidEval;
		let nid = rechercheNid num in
		Printf.printf "\n/*\t\tDans boucle nom eng %d\n" 
			(getBoucleInfoB (nid.infoNid.laBoucle)).identifiant;
		Printf.printf  "\n/*\t\tCOndition\n";  print_expVA n.condition;new_line ();		
		(*Printf.printf "max pour une it dans appel : \n"; print_expTerm n.maxUneIt; new_line ();*)
		Printf.printf "\n\t\tborne pour une itération: "; 
		print_expression n.expressionBorneUneIt 0;
		new_line ();
		Printf.printf "\t\tvaleur de la borne : pour toutes les it : "; 
		print_expVA n.expressionBorneToutesIt  ;new_line ();						
		Printf.printf "\n*/\n" 
   	|_->	Printf.printf  "\n"
			

let afficheNidEval l = List.iter (fun unNid -> afficheUnNidEval unNid) l

let creerLesAffect tN max tni num nappel=
	let varBoucleTN =  Printf.sprintf "%s_%d_%d" "tN" num nappel in	
	let varBouclemax =  Printf.sprintf "%s_%d_%d" "max" num nappel in	
	let varBoucleTNI =  Printf.sprintf "%s_%d_%d" "tni" num nappel in	
	let output = 	List.append  [new_instVar varBoucleTN (EXP(VARIABLE(varBoucleTN)))] 
		(List.append [new_instVar varBouclemax (EXP(VARIABLE(varBouclemax)))]  [new_instVar varBoucleTNI (EXP(VARIABLE(varBoucleTNI)))]) in
	(varBoucleTN,varBouclemax,varBoucleTNI,
	List.append  [new_instVar varBoucleTN tN] (List.append [new_instVar varBouclemax max] [new_instVar varBoucleTNI tni]), output)

let rec listejusquafonction listeEng id pred  =
	if listeEng = [] then  begin (*Printf.printf "non trouvee %d \n" id ;*)(pred , false)end
	else 
	begin
		let premier =  List.hd listeEng in
		let suite =  List.tl listeEng in
		match premier with
			TBOUCLE(n, _,_,_,_,_,_) -> 
				if id = n then begin (*Printf.printf "boucle trouvee %d \n" id ;*)(pred, true)end
				else
				begin (*Printf.printf "boucle  continue  %d \n" id ;*)
					listejusquafonction suite id pred			 
				end
			| TFONCTION(nom, _,_,_,_,_,_,_, _,_) -> (*Printf.printf "listejusquafonction ajout fonction  %d nom %s\n"  id nom;*)
				listejusquafonction suite id premier
	end




let valeurEng = ref NOCOMP
let borneAux = ref NOCOMP 
let borneMaxAux = ref NOCOMP 
let listeVB = ref [] 
(*let listeVBPredNonNidNonNul = ref [] *)
let isProd = ref false
let isExactEng = ref true


(*liste des bornes nulles pour le moment ce sont les seules qui sont certaines if non pris en compte*)
let rec afficherNidUML nnE  liste tab =
match nnE.idBoucleN with
TBOUCLE(num, appel, _,_,_,_,_) ->
	let estNulEngPred = !estNulEng in
	let exactEng = !isExactEng in
	print_tab (tab+3);
	let (fic,lig)=getAssosIdLoopRef num in
	if nnE.isExecuted then 
		Printf.printf  "<loop loopId=\"%d\" executed=\"true\" line=\"%d\" source=\"%s\" totalcount=\"" num  lig fic 
	else 
		Printf.printf  "<loop loopId=\"%d\" executed=\"false\" line=\"%d\" source=\"%s\" totalcount=\"" num  lig fic ;
 
	let nia = new_infoAffich nnE.condition nnE.inf nnE.sup nnE.inc nnE.sensVariation nnE.op in
	let nm =  nnE.maxUneIt  in
	isProd := false;
	

	(*Printf.printf "max nm \n"; print_expVA   nm  ;new_line();*)
	let new_expmax = (applyStoreVA nm  !listeVB) in
	(*Printf.printf "max new_expmax \n"; print_expVA  new_expmax ;new_line();*)
	let (expmax1, reseval) =(
		let c1 = calculer  nm   nia [] in
		if estDefExp c1 = false then begin 	(calculer new_expmax  nia [], false) end 
		else (c1,true) ) in

	(*Printf.printf "max sans eng \n"; print_expTerm (expmax1 );new_line();*)
	let myMaxIt = (if !estNulEng =false then expmax1 else  ConstInt("0") )in

	(*let ne = (applyStoreVA nnE.expressionBorneToutesIt gl) in*)
	let ne =  nnE.expressionBorneToutesIt  in
	let new_exptt = (applyStoreVA ne !listeVB) in
	(*	print_expVA  new_exptt ;new_line(); print_expVA    ne  ;new_line();*)

	let exptt1 =
	(
		let c1 = calculer  nnE.expressionBorneToutesIt   nia [] in
		if estDefExp c1 =false|| reseval = false then calculer new_exptt  nia [] else c1 ) in

	(*print_expVA nnE.expressionBorneToutesIt;new_line();*)
	let borne = (if (!estNulEng =false) && ((estNul myMaxIt)= false) 
				 then   exptt1  else  ConstInt("0") )in
	(*if (estDefExp borne =false ) then Printf.printf "borne non definie\n"else Printf.printf "borne  definie\n";

	Printf.printf "max\n";print_expTerm (myMaxIt);new_line();
	Printf.printf "enf\n";print_expTerm (!valeurEng);	new_line();
	Printf.printf "borne\n";print_expTerm (borne);new_line();*)

	(*	if (!estNulEng ) then Printf.printf "borne eng nulle\n"; if (estNul myMaxIt ) then Printf.printf "max nulle\n";	*)
		if estDefExp borne =false  then
		begin	
			isProd := true;
			if (estDefExp !valeurEng ) && (estDefExp myMaxIt ) then 
			begin
				if ! vDEBUG then  Printf.printf  "borne nocomp borne eng et max ok produit" ; 
				borneAux := evalexpression (Prod (!valeurEng, myMaxIt)) ;isProd := true;
				print_expTerm (!borneAux ); space();flush()
			end
			else
			begin
				borneAux := NOCOMP;
				print_expTerm (NOCOMP);
				if !vDEBUG && ((estNothing ne ) = false) then
				begin 
					Printf.printf  "\" exptotalcount=\"" ; 
					print_expVA ne  ; space();flush()
				end 
			end;
			if 	nnE.varDeBoucleNidEval ="" then 
				if !vDEBUG then Printf.printf "plusieurs variables de boucle\n" 
		end
		else
		begin
			borneAux := (if ((estNul myMaxIt)= false) then
						begin
				
							let prod = evalexpression (Prod (!valeurEng, myMaxIt)) in
							if estDefExp prod then 
								if estPositif (evalexpression (Diff( prod, borne))) then borne else begin isProd := true; prod end
							else borne
						end
						else ConstInt("0"));
			print_expTerm (!borneAux) ;
			
		end;
		Printf.printf  "\" maxcount=\"" ;
		let varBoucleIfN =  Printf.sprintf "%s_%d" "bIt" num in	
		if estNul !borneAux then 
		begin
			borneMaxAux:= (ConstInt("0"));
			print_expTerm (ConstInt("0"));
			setAssosBoucleIdMaxIfSupOldMax num (EVALEXP(ConstInt("0")));

			listeVB := rond !listeVB 
				[ASSIGN_SIMPLE (varBoucleIfN, EXP(CONSTANT  (CONST_INT "-1")))]  ;
(*attention on peut avoir plusieurs fois la même variable de boucle donc ici on ajoute dans false on peut supprimer*)
			estNulEng := true 
		end
		else  
		begin
			if estDefExp myMaxIt then
			begin 
				borneMaxAux:= myMaxIt ;
(*
Printf.printf"max of %d\n"num;*)
				setAssosBoucleIdMaxIfSupOldMax num (EVALEXP(myMaxIt));

			end

			else 
			begin
				
				let maxp = (rechercheNid num).infoNid.expressionBorne in
				let resaux = calculer (EXP(maxp))  nia [] in
				borneMaxAux := if estDefExp resaux then 
							begin 
								setAssosBoucleIdMaxIfSupOldMax num (EVALEXP (resaux));
								resaux 
							end
							else 
							begin
								setAssosBoucleIdMaxIfSupOldMax num (EXPMAX [maxp]);
								NOCOMP
							end
			end;

			print_expTerm !borneMaxAux;

			listeVB := listeSansAffectVar !listeVB varBoucleIfN;
			estNulEng := false
		end;

		
		if estNoComp !borneMaxAux then
		begin	
			if 	nnE.varDeBoucleNidEval ="" then 
				begin if !vDEBUG then Printf.printf "plusieurs variables de boucle\n" end
			else
				begin 
					let maxp = (rechercheNid num).infoNid.expressionBorne in
					Printf.printf  "\" exptotalcount=\"" ;
					if (estNothing nnE.expMaxUneIt = false && nnE.expMaxUneIt != MULTIPLE) then
					begin	
						print_expression (remplacerNOTHINGParAux( nnE.expMaxUneIt) ) 0;space();flush()
					end;			
					if ((estNothing (EXP(maxp)) ) = false) then
					begin
						Printf.printf  "\" expmaxcountInit=\"max ( " ; 
						print_expression maxp 0 ;space();flush();
						Printf.printf  ")" 
					end 
				end
		end;
			
		
		let valeurEngPred = !valeurEng in
		valeurEng := !borneAux;
		
		let (iAmExact, myVar,myBorne)=
			((rechercheNid num).infoNid.isExactExp && (!isProd = false) && (hasSygmaExpVA ne = false) && !isExactEng && (nnE.isIntoIf = false), varBoucleIfN, !borneAux) in
	let iAmNotNul = !estNulEng = false in
		if iAmExact = false then isExactEng := false
		else isExactEng := true;
		if iAmExact then Printf.printf "\" exact=\"true\">\n" else  Printf.printf "\" exact=\"false\">\n" ;
		afficherCorpsUML liste  (tab+5) ;

		isExactEng := exactEng;
		if iAmExact   then 
			begin
				(*Printf.printf "varBoucleIfN : %s is exact\n" myVar;*)
	
				let nb = expressionEvalueeToExpression (evalexpression  (Diff (myBorne, ConstInt ("1"))))  in
			(*	print_expression nb 0; new_line();*)
				listeVB := rond !listeVB  [ASSIGN_SIMPLE (myVar, EXP(nb))]  ;
			end
		else
		begin
			if  iAmNotNul	 then listeVB := listeSansAffectVar !listeVB myVar 
			
		end;
		estNulEng := estNulEngPred;
		valeurEng := valeurEngPred;
		 
		print_tab (tab+3);		
		(*borneAux := memvborneaux;*)
		Printf.printf "</loop>\n" 			
	| _->new_line ()


and afficherUnAppelUML  exp  l tab numCall isExe isInLoop=
	match exp with
		EXP(appel)->
			let nomFonction = (match appel with CALL (exp,_)->  (match exp with  VARIABLE (nomFct) -> nomFct | _ -> "") | _ -> "") in
			
			afficherInfoFonctionUML nomFonction l (tab ) numCall isExe isInLoop;
			new_line();
			
		| _-> Printf.printf "MULTIPLE\n"
					
and afficherInfoFonctionUML nom corps  tab numCall isExe isInLoop  =
	print_tab (tab);	Printf.printf  "<call name=\"%s\" numcall=\"%d\"" nom numCall;
	
	let (fichier , ligne ) = getAssosIdCallFunctionRef numCall in
		(*	
			*)
	if isInLoop = false then if isExe then Printf.printf " executed=\"true\"" else Printf.printf " executed=\"false\"";
	
    if (existeFonctionParNom	nom doc) =false then
	begin
		 Printf.printf " line=\"%d\" source=\"%s\" extern=\"true\">\n" ligne fichier 
	end
	else  begin Printf.printf " line=\"%d\" source=\"%s\">\n" ligne fichier ; afficherCorpsUML corps	 (tab+5)    end;
	
	print_tab (tab);	Printf.printf  "</call>"; 	

and afficherCorpsUML lboua  tab =	 
	List.iter(
			fun unboua	->
				match unboua with
					BOUCLEEVAL (nid, _, cont)->  		afficherNidUML nid  cont tab 
				|	APPELEVAL (ty, expr,liste)-> 	
					let (numCall, isExe, isInLoop) =	(match ty with TFONCTION(nom, appele,_,_,_, _,_,_,e,b)-> (appele, e, b) |_->(0, true, false)) in
					afficherUnAppelUML  expr liste tab numCall isExe isInLoop
			)lboua


let rec isExecutedTrue ltrue contexte  affiche=
if ltrue = [] then begin (*Printf.printf " liste isexecuted vide pour true \n" ;*)true end
else
begin  
	(*Printf.printf "isExecutedTrue liste des variables true :\n"; List.iter (fun e-> Printf.printf "%s "e) ltrue;*)
	if existeAffectationVarListe (List.hd ltrue) contexte then
	begin
 
		let affect = rechercheAffectVDsListeAS  (List.hd ltrue) contexte in
   (*   Printf.printf "CALCUL affect true %s\n" (List.hd ltrue) ; print_expVA affect;flush(); space(); new_line();print_expVA affect;flush(); space(); new_line();*)
		let cond = calculer  affect !infoaffichNull  [] in
		if affiche then
		begin
				(*print_expTerm  cond; flush(); space();new_line();	*)
				 space(); new_line() ;flush();
		 	 	Printf.printf "%s=" (List.hd ltrue) ;	print_expTerm  cond;  space(); new_line() ;flush();
		end;
		(* 
			print_expTerm  cond;flush(); space(); new_line();	*)
		match cond with
		  Boolean(false) -> (*Printf.printf " non execute %s" (List.hd ltrue);*)false
		| Boolean(true)  |_-> isExecutedTrue (List.tl ltrue) contexte affiche
	end
	else true
end

let rec isExecutedFalse lfalse contexte affiche=
if lfalse = [] then begin (*Printf.printf " liste isexecuted vide pour false \n" ;*)true end
else
begin 
(*Printf.printf "isExecutedFalse liste des variables false :\n"; List.iter (fun e-> Printf.printf "%s "e) lfalse;*)
	if existeAffectationVarListe (List.hd lfalse) contexte then
	begin
(*Printf.printf "existe \n";*)
        let affect = rechercheAffectVDsListeAS  (List.hd lfalse) contexte in
	(*	Printf.printf "CALCUL affect false %s\n" (List.hd lfalse) ; print_expVA affect; flush(); space();new_line();print_expVA affect;flush(); space(); new_line();*)	
		let cond = calculer   affect  !infoaffichNull  [] in
		if affiche then
		begin
				(*print_expTerm  cond; flush(); space();new_line();	*)
				 space(); new_line() ;flush();
		 	 	Printf.printf "%sn" (List.hd lfalse) ;	print_expTerm  cond;  space(); new_line() ;flush();
		end;
		match cond with
		  Boolean(true) -> (*Printf.printf "isExecutedFalse non execute %s" (List.hd lfalse) ;*) false
		| Boolean(false)  |_-> isExecutedFalse (List.tl lfalse) contexte affiche
	end
	else begin (*Printf.printf " liste affect non trouve sur n autre chemin\n" ;*) true end
end


let isExecuted ltrue lfalse contexte appel globales affiche= 

	(*Printf.printf "isExecuted : traiterboucleinterne contexteAux : \n"; afficherListeAS contexte; Printf.printf "FIN CONTEXTE \n";
	Printf.printf "isExecuted : traiterboucleinterne appel : \n"; afficherListeAS appel; Printf.printf "FIN appel \n";*)
(*	Printf.printf "isExecuted : traiterboucleinterne globales : \n"; afficherListeAS globales; Printf.printf "FIN CONTEXTE \n";*)
	let listeP = !listeASCourant in
	let res =rond globales (rond appel contexte) in
	let valeur = if ltrue = [] && lfalse = [] then true else (isExecutedTrue ltrue res affiche) && (isExecutedFalse lfalse res affiche) 	in
	listeASCourant := listeP;
	valeur

let isExeBoucle =ref true
let listeInstNonexe = ref []

(*let funcContext = ref []*)

let rec traiterBouclesInternes 	nT (*tete nid contenant bi*)  nEC (*noeud englobantcourant *) 
								idEng (*id noeud englobant  où stopper *)
								n (*courant à  évaluer bi*) aS   (*listeVarBorne listeDep *) tN
								appel (*contexte appel pour le moment fonction puis doc *) 
								listeEng typeE numAp max isExeE lt lf borne pred tetePred sansP=				
	(* il faut evaluer le nombre total d'itération  de la boucle courante n*)
	(*	Pour toutes les boucles bi englobantes de Bj à partir de la	boucle immédiatement englobante de Bj 
	jusqu'à la mère du nid faire*) (*donc en remonté de recursivité*)

	let info = (getBoucleInfoB (nEC.infoNid.laBoucle)) in
	let nomE = info.identifiant  in
	let saBENG = (if aBoucleEnglobante info then info.nomEnglobante else 0) in
	if !vDEBUG then 
	begin
(*1 traiterBouclesInternes num 39 nom eng 68 ou stopper 0 sa eng 0 tete nid 68*)
(* 1 traiterBouclesInternes num 1 nom eng 16 ou stopper 16 sa eng 0 tete nid 16*)
		Printf.printf "1 traiterBouclesInternes num %d nom eng %d ou stopper %d sa eng %d tete nid %d\n" (getBoucleIdB n.infoNid.laBoucle)	nomE idEng saBENG (getBoucleIdB nT.infoNid.laBoucle);
		(* afficheNidEval !docEvalue.maListeNidEval; *)
	(*	Printf.printf "FIN NID ENG COURANT \n"*)
	end;
	let conte = match typeE with  TBOUCLE(n,ap,_,_,_,_,_) -> ap |_-> 0 in
	if nomE = idEng (*|| (nomE = (getBoucleIdB nT.infoNid.laBoucle) && nomE != 0*) then 
	begin	
		if nomE = 0 then Printf.printf "fin de la remontée\n";
		let info = (getBoucleInfoB nEC.infoNid.laBoucle) in
		let nbEngl =getNombreIt (nEC.infoNid.expressionBorne) 
					info.conditionConstante info.typeBoucle  info.conditionI  info.conditionMultiple  [] info.estPlus 
					info.infoVariation  nEC.varDeBoucleNid in
		
		if !vDEBUG then
		begin
			Printf.printf "2 traiterBouclesInternes num %d nom eng %d \n"  (getBoucleIdB n.infoNid.laBoucle) nomE ;
			(*afficherNid nEC;*) Printf.printf "FIN NID ENG COURANT \n";

			if lt <> [] then begin Printf.printf "IF true :\n"; List.iter (fun e-> Printf.printf "%s "e) lt end;

			if lf <> [] then begin Printf.printf "IF false :\n"; List.iter (fun e-> Printf.printf "%s "e) lf end
		end;
		(*Soit VDij l'ensemble des variables modifiées par Bi dont dépend la borne TN *)
		let tni = rechercheNbTotalIti nomE numAp !docEvalue.maListeNidEval in
(*		Printf.printf "total englobante\n"; print_expVA tni; new_line();
Printf.printf "max\n"; print_expVA max; new_line();
Printf.printf "tn\n"; print_expVA tN; new_line();*)
		(*Printf.printf "av traiterBouclesInternes num %d nom eng %d ou stopper %d\n" (getBoucleIdB n.infoNid.laBoucle)	nomE idEng;
					Printf.printf "total englobante :\n";print_expVA tni; new_line();*)
		(* si fonction boucle1 boucle2 fonction boucle3 boucle4 *)
		(* il faut calculer pour boucle 4 le as de boucle1 jusqu'à la fonction union de la fonction à boucle 4*)

		
		(*Printf.printf "av traiterBouclesInternes num %d nom eng %d \n"  (getBoucleIdB n.infoNid.laBoucle) nomE ;*)
		let(varTN,varmax,varTni,l, output) =   creerLesAffect tN max tni (getBoucleIdB n.infoNid.laBoucle) conte in
		isExeBoucle := isExeE;
		(*if !isExeBoucle then  Printf.printf "la boucle englobante est exécutée\n"  
		else  Printf.printf "la boucle englobante n'est pas exécutée\n";*)

		let lesAs = 
		(	if (!dernierAppelFct <> !predDernierAppelFct)  || sansP
			then 
			begin
				match !dernierAppelFct with
				TFONCTION (_, _,_,_, _,_,_,_,_,_) ->		
					let numB  = (getBoucleIdB n.infoNid.laBoucle) in
					let (pred, trouve) = 
					listejusquafonction (List.rev listeEng) numB !dernierAppelFct in
					let calllist = (reecrireCallsInLoop  nEC.varDeBoucleNid nEC.lesAffectationsBNid) in 
					
					(match pred with
						TFONCTION (nomf, numF,corps,listeInputInst, contexteAvantAppel,appelF,lFt,lFf,_,_) ->		
					
						(*Printf.printf"traiterboucleinterne Dans evaluation de la fonction...%s %d %s \n "nomf numB nEC.varDeBoucleNid ;*)
						if appelF = [] then []
						else
						begin
							(match List.hd appelF with  											
							APPEL (_,e,nomFonc,s,c,v) ->
								let ainserer = listeSAUFIDB  (reecrireCallsInLoop  nEC.varDeBoucleNid corps) numB l in
								(*afficherLesAffectations( corps);new_line () ;*)
								(*Printf.printf "ces as\n";*)

								(*afficherLesAffectations( ainserer);new_line () ;*)
								(*Printf.printf "ces as\n";*)

								let aSC = (*if sansP = false then*) evalSIDA calllist numF  [] ainserer output listeInputInst listeEng 
										(*  else 
										  begin Printf.printf "sansP\n";
												evalStore (new_instBEGIN(ainserer)) []; !listeASCourant 
										  end*) in
								
								let isExecutedF = isExecuted lFt lFf aSC appel !abGlobales true in
								listeInstNonexe := List.append [pred] !listeInstNonexe;
								(*if isExecutedF then 
								
								Printf.printf "la fonction est exécutée\n" 
								else Printf.printf "la fonction n'est pas exécutée\n";*)
								(*afficherListeAS( !listeASCourant);new_line () ;
								Printf.printf "traiterBouclesInternes ces as\n";*)
								isExeBoucle := isExeE && isExecutedF;
								(*let asf = rond !abGlobales !listeASCourant in
								afficherListeAS( !listeASCourant);new_line () ;
								asf*)
(*afficherLesAffectations( corps);new_line () ;
afficherListeAS(aSC);new_line () ;*)
								aSC
							| _-> [])
						
						
						end
						|_->[])
				|_->(*Printf.printf "lesAS NON par fonction valeur\n"; *) (*rond !abGlobales*)  (lesVardeiSansj nEC n   l)
			end
			else begin(* Printf.printf "cas3\n";*) (*rond !abGlobales *) (lesVardeiSansj nEC n   l)end
		)in
		let ii = (nEC.varDeBoucleNid) in
		let vij =  rechercheLesVar  lesAs [] in


(*Printf.printf "av traiterBouclesInternes num %d nom eng %d \n"  (getBoucleIdB n.infoNid.laBoucle) nomE ;
 (* afficherUneAffect ( List.hd lappel) ;new_line () ; *)
				
			
				afficherListeAS( lesAs);new_line () ;*)


(*if vij = [] then Printf.printf"vij vide\n";*)
	(*	Printf.printf "CALCUL DE TN num %d nom eng %d\n" (getBoucleIdB n.infoNid.laBoucle) nomE;*)					
(*afficherListeAS  lesAs; Printf.printf "fin liste 	as num %d nom eng %d\n" (getBoucleIdB n.infoNid.laBoucle) nomE;		*)	
		let resExptN  =    rechercheAffectVDsListeAS varTN lesAs in 
(*Printf.printf "varTN varmax %s %s\n" varTN varmax;		
		print_expVA resExptN; new_line();Printf.printf "CALCUL DE AS fin\n";*)
		let recExptMax = rechercheAffectVDsListeAS  varmax  lesAs in
	(*	print_expVA recExptMax; new_line();Printf.printf "CALCUL DE AS fin\n";*)
	(*	let isExe = !isExeBoucle && isExecuted lt lf lesAs [] [] in*)
	isIntoIfLoop := false;
	
	isEnd := false;
	isEndNONZERO := false;
	let resauxmax = calculer max  !infoaffichNull [] in
	let resauxmax2 = calculer (applyStoreVA max !abGlobales) !infoaffichNull [] in
	isEnd := if estDefExp resauxmax then if  estNul resauxmax then true else false else false ;
	
	resAuxTN :=  
	(  match resExptN with
		MULTIPLE ->(* Printf.printf"resAuxTN MULTIPLEdef\n";*)
			if sansP = false then	
			begin 
				if estDefExp resauxmax then 
				begin 
					isIntoIfLoop := true ; 
					EXP(BINARY(MUL,expVaToExp borne,(expressionEvalueeToExpression resauxmax))) 
				end	
				else if estDefExp resauxmax2  then 
						EXP(BINARY(MUL,expVaToExp borne,expVaToExp max)) 
					 else EXP(NOTHING)
			end
			else MULTIPLE
		|EXP  ( exptN) -> 
			if sansP = false then	
			begin 
				(*Printf.printf"resAuxTN def\n";*) 
				(*let resExptni  =  rechercheAffectVDsListeAS  varTni lesAs in*)
				(*Printf.printf "CALCUL DE TNi num %d nom eng %d\n" (getBoucleIdB n.infoNid.laBoucle)	nomE ;*)
				(*print_expVA resExptni; new_line();Printf.printf "CALCUL DE AS fin\n";*)
				let vdij = ( intersection (listeDesVarsDeExpSeules exptN)  ( union [ii]  vij)) in 
				(* idenpendant*)
				if vdij = [] then
				begin
					if !vDEBUG then  Printf.printf "intersection vide\n";
					(* si les deux contiennent une même variable max * max ici ou dans evaluation ???*)
					 (match nbEngl with 
						MULTIPLE->(*Printf.printf"borne  multiple\n";*)  MULTIPLE 
						|EXP(exptni)->							
							if estDefExp resauxmax then 
							begin
								(*Printf.printf"borne  MUL 1\n";*)
								isEndNONZERO := true;
								EXP(BINARY(MUL,expVaToExp borne,(expressionEvalueeToExpression resauxmax))) 
							end
							else 
								if estDefExp resauxmax2  then EXP(BINARY(MUL,expVaToExp borne,expVaToExp max) )
								else
									if estNothing nbEngl || estNothing (EXP(exptN)) then 
									begin (*Printf.printf"borne  NOTHING 1\n";*) EXP(NOTHING) end
									else begin (*Printf.printf"borne  MUL 2\n";*) EXP(BINARY(MUL,exptni,exptN)) end)
				end
				else
				begin
					(*tant que vD != [ii] faire begin pour toute variable x appartenant à vD faire
	 				remplacer dans tN x
					 par l'expression qui lui est associée dans la liste des vij	end	*)
					(*remplacerVar tN vD vij;*)
					(* avant il faut modifiee lesAs mais uniquement pour les variables*)
					(*let lesAs = (if vdij <> [ii] then majAs lesAs vdij ii else lesAs) in*)
					if !vDEBUG then Printf.printf("!!!Depend de la boucle englobante sans var \n");	
					match nbEngl with 
					MULTIPLE -> (*Printf.printf"borne  multiple 2\n";*)MULTIPLE; 
					| EXP(exptni) ->
						begin
						 	(* si tN contient lui meme un SYGMA de i il faut composer *)
							(*Printf.printf"borne  SYGMA 2\n";*)
							if estNothing nbEngl || estNothing (EXP(exptN)) then  
							begin (*Printf.printf"borne  NOTHING 2\n";*) EXP(NOTHING) end
							else
								EXP(CALL(VARIABLE("SYGMA") ,
									(List.append
										(List.append [VARIABLE (ii)]	
												[BINARY(SUB, exptni,CONSTANT (CONST_INT "1"))])  [ exptN])));
											
						end
						(* remarque la seule variable modifiée par la boucle englobante courante dont
						 doit dépendre TN à ce stade est ii *)			
				end
			end
			else resExptN) ;
		maxAuxTN := 
		(	if sansP = false then	
			begin 
				match recExptMax with
				MULTIPLE->
					if estDefExp resauxmax then 
					begin isIntoIfLoop := true ;
						 EXP(expressionEvalueeToExpression resauxmax) 
					end	
					else if estDefExp resauxmax2  then 
							EXP( expVaToExp max)
						 else EXP(NOTHING)
				  | EXP (e)->(*Printf.printf"resAuxTN def\n";*)
					if (intersection (listeDesVarsDeExpSeules e) (union [ii] vij)) = [] then 
					begin (*Printf.printf "la borne max ne contient pas de var fct de ii :%s\n" ii;*)
						EXP (e);
					(*	print_expVA !maxAuxTN; new_line ();Printf.printf"\n"	*)
					end
					else  
					begin
						(*Printf.printf "la borne max  contient  la variable fct de ii :%s\n" ii;*)
						(match nbEngl with 
						MULTIPLE ->   MULTIPLE
						| EXP(exp) ->  
							if estNothing nbEngl || estNothing (EXP(e)) then  EXP(NOTHING) 
							else
								EXP(CALL(VARIABLE("MAX") , (List.append (List.append
			 						[VARIABLE (ii)]	
									[BINARY(SUB,	exp, (CONSTANT (CONST_INT "1")))])  [e])))
								(*print_expVA !maxAuxTN; new_line ();Printf.printf"\n";	*)	)
					end
				end
				else recExptMax
			);
(*Printf.printf"traiter calcul MAX pour %s =\n" ii; print_expVA !maxAuxTN; new_line ();Printf.printf"\n";
Printf.printf"traiter calcul Total pour %s =\n" ii; print_expVA !resAuxTN; new_line ();Printf.printf"\n";*)
(*Printf.printf"resAuxTN et max fin eval\n";
		Printf.printf "nouNidEval av traiterBouclesInternes num %d nom eng %d \n"  (getBoucleIdB nT.infoNid.laBoucle) saBENG ;	*)		
 
(*Printf.printf"appel rec de traiterBouclesInternes 	\n";*)

(* 1 traiterBouclesInternes num 1 nom eng 16 ou stopper 16 sa eng 0 tete nid 16*)
(*Printf.printf "1 traiterBouclesInternes  nom eng %d ou stopper %d sa eng %d tete nid %d\n" 	nomE idEng saBENG (getBoucleIdB nT.infoNid.laBoucle);
*)
		let fini = (nomE = idEng) && (nomE =  (getBoucleIdB nT.infoNid.laBoucle)) in
		if   !isIntoIfLoop = false && !isEnd  = false && !isEndNONZERO = false && fini = false then 
			traiterBouclesInternes nT  nT saBENG
			n  aS   ( !resAuxTN)  appel listeEng typeE numAp  ( !maxAuxTN) true lt lf borne n tetePred sansP
		else
		begin
					(*Printf.printf"traiter calcul MAX pour %s =\n" ii; print_expVA !maxAuxTN; 
					new_line ();Printf.printf"\n";		*)

			(*if !isExeBoucle = true then Printf.printf "!isExeBoucle= true" else Printf.printf "!isExeBoucle= false" ;*)

					let isExe2 = if nT = nEC then !isExeBoucle && isExecuted lt lf lesAs appel !abGlobales true else !isExeBoucle in
	
					if isExe2 = false || !isEnd then
					begin
						(*Printf.printf "la boucle n'est pas exécutée\n";*)		
						maxAuxTN :=EXP(CONSTANT (CONST_INT "0"));
						resAuxTN:=EXP(CONSTANT (CONST_INT "0"));
				 		listeInstNonexe := List.append [typeE] !listeInstNonexe
					end;
					let endcontexte = (*rond*) (rond  !abGlobales  appel) (*!funcContext *)in
					let nTN =  (applyStoreVA (!resAuxTN) endcontexte)  in
					let nMax = (applyStoreVA (!maxAuxTN) endcontexte) in


			(*Printf.printf"traiter calcul MAX pour %s =\n" ii; print_expVA nMax; new_line ();Printf.printf"\n";
			Printf.printf"traiter calcul Total pour %s =\n" ii; print_expVA nTN; new_line ();Printf.printf"\n";
			(*if !vDEBUG then*) Printf.printf "evalNid contexte  boucle: %d\n"  (getBoucleIdB n.infoNid.laBoucle)	 ;*)
					(*afficherListeAS (rond endcontexte lesAs);flush(); space(); new_line();*)

					let info = (getBoucleInfoB (n.infoNid.laBoucle)) in	
					let nouNidEval = new_nidEval	 	
									(applyStoreVA (EXP(n.condN)) endcontexte)
									typeE
									n.infoNid.expressionBorne 
									(applyStoreVA ( !resAuxTN) endcontexte)
									n.varDeBoucleNid  
									(applyStoreVA (EXP(info.infoVariation.borneInf)) endcontexte)
									(applyStoreVA (EXP(info.infoVariation.borneSup)) endcontexte)
									(applyStoreVA (EXP(info.infoVariation.increment)) endcontexte)
									info.infoVariation.direction  
									info.infoVariation.operateur 
									nMax nTN isExe2 !isIntoIfLoop in	
			(*Printf.printf "1 traiterBouclesInternes  %d nom eng %d ou stopper %d sa eng %d tete nid %d\n" (getBoucleIdB n.infoNid.laBoucle)	nomE idEng saBENG (getBoucleIdB nT.infoNid.laBoucle);*)
					afficherNidUML nouNidEval  [] 1 ;
					docEvalue := new_documentEvalue 
								(List.append  [ nouNidEval] !docEvalue.maListeNidEval) !docEvalue.maListeEval;
							nouBoucleEval := [nouNidEval]
		end
	end
	else 
	begin	
	(* fin de la récursivité lorsque en descendant dans les boucles on rencontre bi lui même *)
	(*	if (existeNidContenant nEC.listeTripletNid  idEng) then 
		begin 
			let liste = (rechercheNidContenant 	nEC.listeTripletNid idEng) in
			if liste <> [] then
			begin			
				let (_,_,nid) =List.hd liste in
Printf.printf "4 traiterBouclesInternes TRAITEMENT  DE %d \n" (getBoucleIdB nid.infoNid.laBoucle);
				traiterBouclesInternes nT  nid idEng n  aS  !resAuxTN appel listeEng typeE  numAp !maxAuxTN isExeE lt lf borne n tetePred sansP
			end
		end
		else
		begin (* on ne passe pas ici déjà sortis *)
			(*|| (nomE = (getBoucleIdB nT.infoNid.laBoucle) && nomE != 0*)
			if ((idEng <> 0) && (idEng <> (getBoucleIdB nT.infoNid.laBoucle))) then
			begin
				let reverseliste = List.rev listeEng in			    	
				let (nbou, nab, _,_,_,_,_) =
				rechercheDerniereBoucleApresId (getBoucleIdB nEC.infoNid.laBoucle) reverseliste in

				let evalP = isExecutedNidEval nbou nab  !docEvalue.maListeNidEval  in
				Printf.printf "5 traiterBouclesInternes TRAITEMENT  DE %d id b fin :%d id b cour %d \n"
					(getBoucleIdB n.infoNid.laBoucle) idEng nbou;
				Printf.printf "traiterBouclesInternes REMONTER JUSQU4A SUIVANT DE %d suivant %d\n"	
					(getBoucleIdB nEC.infoNid.laBoucle) nbou;
				let nidCourantCC = (rechercheNid nbou) in
				traiterBouclesInternes nT  nidCourantCC idEng n aS 
				!resAuxTN appel listeEng typeE  nab  
				!maxAuxTN evalP lt lf borne n tetePred sansP
			end
			else 
			begin *)
				if (nomE = (getBoucleIdB nT.infoNid.laBoucle) && nomE != 0) || (idEng != (getBoucleIdB nT.infoNid.laBoucle)) then
				begin
					let appelP = !dernierAppelFct in
					rechercheDernierAppel listeEng ;
					(match !dernierAppelFct with
						TFONCTION (nomf, numF,corps,listeInputInst, contexteAvantAppel,appelF,lFt,lFf,_,_) ->		
							Printf.printf"traiterboucleinterne Dans evaluation de la fonction remontee...fin 0%s\n "nomf;
							
							traiterBouclesInternes nT  nT nomE n aS 
							!resAuxTN appel listeEng typeE  numF  
							!maxAuxTN isExeE lt lf borne n tetePred true (* true = sans prod*);
 							(*	funcContext :=[]*)
							(*Printf.printf "faire contexte\n"*)
				|_->()(*funcContext :=[]*));				
				(*  Printf.printf "pas de boucle englobante fin traiterBouclesInternes apres creer\n"*)
				dernierAppelFct := appelP;
				end
		(*	end
		end*)
	end
		
let rechercheTriplet n liste= 
List.find (fun e -> let (_,_,nid) =e in (getBoucleIdB nid.infoNid.laBoucle) = n) liste

let rec existeTFonction liste nom numF=
if liste <> [] then 
begin
	let pred = (List.hd liste) in
	match pred with
	TBOUCLE(_, _,_,_,_,_,_) -> existeTFonction (List.tl liste) nom numF
	| TFONCTION(n,num,_,_,_,_,_,_,_,_) ->  if n = nom && num = numF then true else existeTFonction (List.tl liste) nom numF
end	
else false

let rec existeTBoucle liste id appel=
if liste <> [] then 
begin
	let pred = (List.hd liste) in
	match pred with
	TBOUCLE(ide, appele,_,_,_,_,_)  ->
			if (id = ide) && (appele = appel)   then true else existeTBoucle (List.tl liste) id appel
	| TFONCTION(_,_,_,_,_,_,_,_,_,_) ->  existeTBoucle (List.tl liste) id appel
end	
else false

let rec reecrireCorpsNonExe  listeinst listeTypeNonExe numAppel=
if listeinst = [] || listeTypeNonExe = [] then listeinst
else 
begin
	let i = List.hd listeinst in
	let suite = List.tl listeinst in
	match i with 
		VAR (id, exp) -> List.append [i] (reecrireCorpsNonExe  suite listeTypeNonExe numAppel)
		| TAB (id, exp1, exp2) -> List.append [i] (reecrireCorpsNonExe  suite listeTypeNonExe numAppel)
		| MEMASSIGN(id, exp1, exp2) -> List.append [i] (reecrireCorpsNonExe  suite listeTypeNonExe numAppel)
		| BEGIN liste -> 		
				List.append [BEGIN(reecrireCorpsNonExe  liste listeTypeNonExe numAppel)]	
						 (reecrireCorpsNonExe  suite listeTypeNonExe numAppel)
		| IFVF (t, i1, i2) -> 	
			let liste1 = match i1 with BEGIN(e)-> e |_->[] in
			let res1 = reecrireCorpsNonExe  liste1 listeTypeNonExe numAppel in
			let liste2 = match i2 with BEGIN(e)-> e |_->[]  in
			let res2 = reecrireCorpsNonExe  liste2 listeTypeNonExe numAppel in
			List.append  [IFVF(t, BEGIN(res1), BEGIN(res2))] (reecrireCorpsNonExe  suite listeTypeNonExe numAppel)
		| IFV ( t, i1) 		-> 
			let liste1 = match i1 with BEGIN(e)-> e |_->[] in
			let res1 = reecrireCorpsNonExe  liste1 listeTypeNonExe numAppel in
			List.append [IFV ( t, BEGIN(res1))] (reecrireCorpsNonExe  suite listeTypeNonExe numAppel)
		| FORV (num,id, e1, e2, e3, nbIt, inst)	-> 
			if existeTBoucle listeTypeNonExe num numAppel then (reecrireCorpsNonExe  suite listeTypeNonExe numAppel)
			else
			begin
				let liste1 = match inst with BEGIN(e)-> e |_->[] in
				let res1 = reecrireCorpsNonExe  liste1 listeTypeNonExe numAppel in
				List.append [FORV (num,id, e1, e2, e3, nbIt,  BEGIN(res1))] 
					(reecrireCorpsNonExe  suite listeTypeNonExe numAppel)
			end
		| APPEL (i,e,nomFonc,s,c,var)-> 
			if existeTFonction listeTypeNonExe nomFonc i then (reecrireCorpsNonExe  suite listeTypeNonExe numAppel)
			else
			begin
				let liste1 = match c with BEGIN(e)-> e |_->[] in
				let res1 = reecrireCorpsNonExe  liste1 listeTypeNonExe i in
				List.append [APPEL (i, e ,nomFonc,s,BEGIN(res1),var)] (reecrireCorpsNonExe  suite listeTypeNonExe numAppel)
			end
end

(*ATTENTION NE DEVRAIT ON PAS ENVOYER LA SUITE DU CODE CAD DES AFFECTATIONS ??*)
let rec  evalCorpsFOB corps affectations contexte listeEng estexeEng = 
	if corps <> [] then
	begin
		let new_cont = evalUneBoucleOuAppel (List.hd corps) affectations contexte listeEng  estexeEng in
		if (List.tl corps) != [] then
		begin
			let (next_cont, last) = evalCorpsFOB (List.tl corps) affectations new_cont listeEng estexeEng in
			(next_cont, last)
		end
		else (new_cont,  [(List.hd corps)])
	end
	else begin (contexte, []) end

and endOfcontexte affec  last new_contexte =
    listeASCourant := [];
	if last = [] then begin (*Printf.printf"lastvide \n"; *) evalStore (BEGIN(affec)) new_contexte end
	else
	begin
		let fin = 
		(match List.hd last with
		IDBOUCLE (num, _,_) ->  (*Printf.printf"last boucle %d\n" num; *) nextInstructionsB num affec
		| IDAPPEL (numf,_,_,_, _,_) ->  (*Printf.printf"last function  %d\n" numf; *) nextInstructionsF numf affec)
 		in
		(*afficherUneAffect (BEGIN(fin)); *)
		if fin = [] then listeASCourant :=new_contexte else evalStore (BEGIN(fin)) new_contexte
	end; !listeASCourant

and evalUneBoucleOuAppel elem affectations contexte listeEng estexeEng=
(match elem with
	IDBOUCLE (num, lt,lf) -> 
		if  (existeNid  num) then
		begin
			(*Printf.printf"Dans evalUneBoucleOuAppel de la boucle...%d \n"num;*)
			let nid = (rechercheNid num) in
			let asL = if !estDansBoucle = false then  (jusquaBaux affectations num  contexte ) 
					  else  (evalSIDB affectations num contexte [])  in
		 	evalNid nid asL  listeEng  lt lf estexeEng
		end
		else  
		begin
			if !vDEBUG then Printf.printf "eval corps fonction nid %d non trouve\n" num	;
			contexte
		end
	| IDAPPEL (numf,appel,listeInputInstruction,var, lt,lf) ->
		let numAppelPred = !numAppel in
		let nomFonction =	
			(match appel with
				CALL(exp,_)->(match exp with VARIABLE(nomFct)->nomFct|_-> "")|_->"") in		
		listeDesInstCourantes := [];
		
		if !vDEBUG then Printf.printf "evalUneBoucleOuAppel Eval appel FONCTION %s: num appel %d \n" nomFonction numf;
		let dansBoucle = !estDansBoucle in
		let asf = (jusquaFaux affectations numf  contexte) in

		let contexteAvantAppel = (if dansBoucle = false then asf else contexte) in
		let (lappel, entrees) = if  !appelcourant <> [] then
					 begin
						match List.hd !appelcourant with  															
							APPEL (n,e,nomFonc,s,c,v) ->
								if existeFonctionParNom	nomFonction doc then
								begin				
									let (_, func) = (rechercherFonctionParNom nomFonction doc) in
									let ne = (match e with BEGIN(eee)-> eee |_->[]) in
									([APPEL (n,e,nomFonc,s,BEGIN(func.lesAffectations),v)], ne)
								end
								else ([],listeInputInstruction)
							|_->([], listeInputInstruction)
					 end
					 else ([], listeInputInstruction) in
		
		(* non le contexte de l'appel se réduit à la valeur des *)
		let asLAppel = (if dansBoucle = false then 
						begin
							let gc = filterGlobales contexteAvantAppel !globalesVar in
							List.append gc (evalInputFunction contexteAvantAppel listeInputInstruction !abGlobales)
						end
					  else contexte)  in
		
		let isExecutedCall =   estexeEng && isExecuted lt lf asLAppel [] [] (dansBoucle = false) in

		if  lappel <> [] then 
		begin
			(*Printf.printf"Dans evaluation de la fonction FONCTION %s: num appel  3\n" nomFonction ;*)
			(*	afficherListeAS( evalInputFunction contexteAvantAppel listeInputInstruction globales);new_line () ;*)
			let appelC = List.hd lappel in
			match appelC with  															
			APPEL (_,e,nomFonc,s,c,v) ->
				if existeFonctionParNom	nomFonction doc then
				begin				
					numAppel := numf;      
					let (_, func) = (rechercherFonctionParNom nomFonction doc) in
					let affec = if dansBoucle = false then func.lesAffectations  
								else reecrireCallsInLoop !varDeBoucleBoucle func.lesAffectations in 
					(*afficherLesAffectations ( func.lesAffectations) ;new_line () ; *)
					if !vDEBUG then Printf.printf "evalUneBoucleOuAppel FIN Eval appel FONCTION %s:\n" nomFonction ;
					let typeE =  
						TFONCTION(nomFonction,!numAppel,affec , listeInputInstruction, asLAppel,lappel,lt,lf, 
							isExecutedCall || dansBoucle , dansBoucle)
						in   
					let (new_contexte,last) = 
						evaluerFonction nomFonction func asLAppel (EXP(appel))  (List.append [typeE] listeEng) typeE 
								(isExecutedCall || dansBoucle ) in	
			
					numAppel := numAppelPred ;	
					if dansBoucle = false then 
					begin
						if isExecutedCall && nomFonction != !(!mainFonc) then
						begin
							let rc = endOfcontexte affec  last  new_contexte in
							listeASCourant := []; 
							let sorties = (match s with BEGIN(sss)-> sss |_->[]) in
							if sorties <> [] then
							begin				
								List.iter (
									fun sortie -> 
									(match sortie with 
									VAR (id, e) ->  
										listeASCourant :=  List.append 
										[new_assign_simple id (applyStoreVA e rc) ]  !listeASCourant; 
										()
									| TAB (id, e1, e2) ->  
										listeASCourant := List.append
											[ASSIGN_DOUBLE (id,  (applyStoreVA e1 rc),  (applyStoreVA e2 rc))] !listeASCourant;
											()
										|_-> ())
									)sorties	
							end;
							let returnf = Printf.sprintf "res%s"  nomFonc in
							if existeAffectationVarListe returnf rc then
							begin
								let affectres = ro returnf rc in
								listeASCourant :=  List.append [affectres] !listeASCourant
							end;
							(*abGlobales := majVG !abGlobales rc;*)
							let nginterne = filterGlobales rc !globalesVar in
								 
(*afficherListeAS( nginterne);new_line () ;*)
							let ncont = rond contexteAvantAppel (List.append  !listeASCourant nginterne) in(*voir remarque cvarabs.ml*)
							(*Printf.printf "FIN Eval appel FONCTION %s:\n" nomFonction ;
							afficherListeAS( ncont);new_line () ;*)
							ncont
							 
						end	
						else begin (*Printf.printf "FIN Eval appel FONCTION  2%s:\n" nomFonction ; *) contexte end
					end
					else  begin (*Printf.printf "FIN Eval appel FONCTION 3%s:\n" nomFonction ;  *) contexte end
				end 
				else  	  begin (*Printf.printf "FIN Eval appel FONCTION 4%s:\n" nomFonction ;*)   contexte end
				|_-> begin (*Printf.printf "FIN Eval appel FONCTION 5%s:\n" nomFonction ; *) contexte end;
			end
			else 
			begin 
					numAppel := numf;     
					if dansBoucle = false then 
					begin
						if isExecutedCall then
						begin
							let typeE =  
								TFONCTION(nomFonction,!numAppel,[] , listeInputInstruction, contexteAvantAppel,[],lt,lf,
									 isExecutedCall, dansBoucle)
								in  
							let new_fct = [ new_elementEvala typeE (EXP(appel)) []] in						
							corpsEvalTMP := List.append !corpsEvalTMP	 new_fct;	
							docEvalue := new_documentEvalue !docEvalue.maListeNidEval (List.append !docEvalue.maListeEval new_fct);
							
						end
					end;
					numAppel := numAppelPred ;	 
					(*Printf.printf "FIN Eval appel FONCTION 5%s:\n" nomFonction ; *)
					contexte (*asLAppel REVOIR !!!*)
			end )


and evaluerFonction id f contexte exp listeEng typeA estexeEng=	
	let corpsEvalTMPPred = !corpsEvalTMP in
	corpsEvalTMP := [];
	let aff =  
		(if !varDeBoucleBoucle ="" then f.lesAffectations else  reecrireCallsInLoop !varDeBoucleBoucle 	f.lesAffectations) in
	let (new_contexte, next) = evalCorpsFOB f.corps.boucleOuAppel  aff contexte listeEng estexeEng in
	let corpsEvalPourAppel = !corpsEvalTMP  in 
	let new_fct = [ new_elementEvala typeA exp corpsEvalPourAppel] in
	corpsEvalTMP := List.append corpsEvalTMPPred	 new_fct;	
	docEvalue := new_documentEvalue !docEvalue.maListeNidEval (List.append !docEvalue.maListeEval new_fct);
	(new_contexte, next)
					
and evalNid nid  appel (*appelée pour une mere de nid*) listeEng lt lf estexeEng=	
if !vDEBUG then Printf.printf "evalNid NID av eval nid de %d \n" (getBoucleIdB nid.infoNid.laBoucle)	;
	dernierAppelFct :=   !predDernierAppelFct;
	let info = getBoucleInfoB nid.infoNid.laBoucle in
	let mesBouclesOuAppel = info.boucleOuAppelB in
	if !estDansBoucle = false then
	begin
		
		let aSC =  rond !abGlobales appel in 
		if !vDEBUG then Printf.printf "evalNid contexte  boucle: \n";
		(*Printf.printf "FIN CONTEXTE globale \n";*)
		(*if lt <> [] then begin Printf.printf "liste des variables IF true :\n"; List.iter (fun e-> Printf.printf "%s "e) lt end;
		if lf <> [] then begin Printf.printf "liste des variables IF false :\n"; List.iter (fun e-> Printf.printf "%s "e) lf end;*)
		listeInstNonexe :=[];
		if !vDEBUG then Printf.printf "NID av eval nid de %d pas dans autre boucle\n" (getBoucleIdB nid.infoNid.laBoucle)	;


		let isExe =  estexeEng && isExecuted lt lf appel [] !abGlobales true in
		(*Printf.printf"evalNid : valeur de isexe dans evalboucel pas dans autre : ";
		if isExe then Printf.printf"vrai\n" else Printf.printf"false\n" ;*)
	
		estDansBoucle := true;
		let varDeBouclePred = !varDeBoucleBoucle in
		varDeBoucleBoucle :=nid.varDeBoucleNid;
		let corpsEvalTMPPred = !corpsEvalTMP in
		corpsEvalTMP := [];

		(*print_expression nid.infoNid.expressionBorne 0;*)
		let nb = if isExe then applyStoreVA (getNombreIt (nid.infoNid.expressionBorne) 
					info.conditionConstante info.typeBoucle  info.conditionI info.conditionMultiple
 					aSC info.estPlus  info.infoVariation nid.varDeBoucleNid) !abGlobales
				 else EXP(CONSTANT (CONST_INT "0")) in
		

		let typeEval = TBOUCLE((getBoucleIdB nid.infoNid.laBoucle), !numAppel,
					(reecrireCallsInLoop nid.varDeBoucleNid 	nid.lesAffectationsBNid),appel, isExe,[],[]) in
		if !vDEBUG then Printf.printf "evalNid contexte  boucle: %d\n" (getBoucleIdB nid.infoNid.laBoucle);
		(*		afficherListeAS aSC;flush(); space(); new_line();*)
	
		let nouNidEval = 
			new_nidEval	(applyStoreVA  (EXP(nid.condN)) aSC) 	
					typeEval
					(nid.infoNid.expressionBorne) (*borne pour une exécution*)
					nb (* borne total *) (nid.varDeBoucleNid) 
					  (applyStoreVA (EXP(info.infoVariation.borneInf)) aSC)
					  (applyStoreVA (EXP(info.infoVariation.borneSup)) aSC)
					  (applyStoreVA (EXP(info.infoVariation.increment)) aSC)
					info.infoVariation.direction  info.infoVariation.operateur 
					 nb  nb isExe false
		 in
		docEvalue :=  new_documentEvalue  (List.append [ nouNidEval] !docEvalue.maListeNidEval) !docEvalue.maListeEval;		
		if !vDEBUG then Printf.printf "av evaluerSN de %d dans nid tete appel %d\n" (getBoucleIdB nid.infoNid.laBoucle)	!numAppel;
		afficherNidUML nouNidEval  [] 1 ;

		let borne  =  nouNidEval.expressionBorneToutesIt  in
		let tetePred = (TBOUCLE(0,0,[],[], true,[],[]))  in
		
		typeNidTeteCourant := typeEval;

		let resaux = calculer nb  !infoaffichNull [] in
		let isNull = if  estDefExp resaux then  if estNul resaux then true else false else false in
		(*let listeSauf =*)evaluerSN   nid	nid	appel mesBouclesOuAppel  (List.append  [typeEval] listeEng) isExe borne nid;
					(*	resaux in*)

		if !vDEBUG then  Printf.printf "ap evaluerSN de %d dans nid tete appel %d\n"  (getBoucleIdB nid.infoNid.laBoucle) !numAppel;

		typeNidTeteCourant :=tetePred;
		let corpsEvalPourB = !corpsEvalTMP  in 
		let new_b = [ new_elementEvalb nouNidEval typeEval corpsEvalPourB] in

		corpsEvalTMP := List.append corpsEvalTMPPred	 new_b;	
		docEvalue := new_documentEvalue !docEvalue.maListeNidEval (List.append	!docEvalue.maListeEval   new_b);
		if !vDEBUG then Printf.printf "ajout dans liste corpsEval %d\n"  (getBoucleIdB nid.infoNid.laBoucle);
		
		varDeBoucleBoucle :=varDeBouclePred;
		estDansBoucle := false;	
		if isExe && isNull = false then
		begin
		 	(*Printf.printf "est exécutée\n" ;*)
(*supprimer tous ceux qui sont dans  !listeInstNonexe; *)
			let ni = reecrireCorpsNonExe  nid.lesAffectationsBNid !listeInstNonexe !numAppel in
			evalStore (new_instBEGIN ni) appel;
			(*abGlobales := majVG !abGlobales !listeASCourant;*)

			!listeASCourant
		end
		else
		begin (*	Printf.printf "n'est pas exécutée\n";*)
			appel
		end
	end
	else
	begin	
		(*Printf.printf "EVAL evaluation fonction nid dans boucle\n"	;*)
		(*Printf.printf "contexte appel boucle\n" ; afficherListeAS appel; Printf.printf "fin contexte\n" ;*)
		(* Printf.printf "NID av eval nid de %d dans autre boucle\n" (getBoucleIdB nid.infoNid.laBoucle)	;*)
		(*if lt <> [] then begin Printf.printf "liste des variables IF true :\n"; List.iter (fun e-> Printf.printf "%s "e) lt end;
		if lf <> [] then begin Printf.printf "liste des variables IF false :\n"; List.iter (fun e-> Printf.printf "%s "e) lf end;*)
		if existeDerniereBoucle listeEng then
		begin
			let  (numTete, numApp, cont, isExe, ltB,lfB)= 
			match !typeNidTeteCourant with TBOUCLE (numT, numA, _,cont, b, ltB,lfB) -> (numT, numA, cont, b, ltB,lfB)
										 |_-> (0, 0,[], false, [],[]) in
			let (numBouclePred, numAppBP, _, _,listeAvantAppel,_,_,_) =  rechercheDerniereBoucle listeEng in
			let borneP = rechercheNbTotalIti numBouclePred numAppBP !docEvalue.maListeNidEval in
			
			let (ouStopper, isExeE) = 
				if numBouclePred = 0 then (numTete,isExecutedNidEval numTete numApp  !docEvalue.maListeNidEval) 
									 else (numBouclePred, 
											isExecutedNidEval numBouclePred numAppBP  !docEvalue.maListeNidEval) in
			(*	if isExeE then Printf.printf"isExeE = vrai\n" else Printf.printf"isExeE = false\n" ;*)
			let varDeBouclePred = !varDeBoucleBoucle in
			varDeBoucleBoucle :=nid.varDeBoucleNid;

			let typeEval = TBOUCLE((getBoucleIdB nid.infoNid.laBoucle), !numAppel, 	
				(reecrireCallsInLoop nid.varDeBoucleNid nid.lesAffectationsBNid) ,appel, isExeE, lt,lf)
 			in			
			if (existeNid numTete) then 
			begin 
				if (existeNid numBouclePred) then 
				begin 
					let nidTETE = (rechercheNid numTete) in
					let nidAppel = (rechercheNid numBouclePred) in
					let info = (getBoucleInfoB nid.infoNid.laBoucle) in
					let valBorne =	if isExeE then getNombreIt (nid.infoNid.expressionBorne) 
										info.conditionConstante info.typeBoucle  info.conditionI
	 									info.conditionMultiple [] info.estPlus  info.infoVariation nid.varDeBoucleNid
				 					else EXP(CONSTANT (CONST_INT "0")) in

					let courcont = rond  !abGlobales cont in 
					(*Printf.printf "NID av eval nid de %d dans autre boucle\n" (getBoucleIdB nid.infoNid.laBoucle)	;
					Printf.printf "valeur initiale borne :\n";print_expVA valBorne; new_line();*)
					let nle = (List.append  [typeEval] listeEng) in
				(*let reverseliste = List.rev nle in			    	
				let (_, _, _,_,_,_,_) =
				rechercheDerniereBoucle (getBoucleIdB nid.infoNid.laBoucle) reverseliste in*)



					traiterBouclesInternes 	
							nidTETE  nidAppel  ouStopper
							(* le noeud englobant où il faut s'arreter ici id boucle englobante *)
							nid	[] (* les as de la boucle englobante sans lui *)
							(*(EXP(n.infoNid.expressionBorne)) *)valBorne
							courcont nle typeEval numAppBP valBorne isExeE lt lf borneP nid nid false;		

					let nouNidEval = List.hd !nouBoucleEval in
					let borne  =  nouNidEval.expressionBorneToutesIt  in
					let corpsEvalTMPPred = !corpsEvalTMP in
					corpsEvalTMP := [];	

					if !vDEBUG then Printf.printf "evalNid av evaluerSN de %d dans nid tete %d appel %d\n" (getBoucleIdB nid.infoNid.laBoucle)
							(getBoucleIdB nidTETE.infoNid.laBoucle) !numAppel;

				
					evaluerSN   nidTETE	nid	courcont mesBouclesOuAppel (List.append  [typeEval] listeEng) isExeE borne nid;

					if !vDEBUG then   Printf.printf "ap evaluerSN de %d dans nid tete appel %d\n" 
							(getBoucleIdB nid.infoNid.laBoucle)	!numAppel;
					let corpsEvalPourB = !corpsEvalTMP  in 
					let new_b = [ new_elementEvalb nouNidEval typeEval corpsEvalPourB] in



					corpsEvalTMP := List.append corpsEvalTMPPred	 new_b;	
					docEvalue := new_documentEvalue !docEvalue.maListeNidEval  (List.append !docEvalue.maListeEval new_b);
					
					varDeBoucleBoucle :=varDeBouclePred;
					appel
				end
				else 
					begin
						if !vDEBUG then Printf.printf "pb pas de nid pour boucle %d :\n" numTete;
						appel
					end
			end
			else 
			begin
				if !vDEBUG then Printf.printf "pb pas de nid pour boucle %d :\n" numBouclePred;
				appel
			end
		end
		else 
		begin
			if !vDEBUG then Printf.printf "evalNID : pas de boucle englobante  boucle autre nid\n";
			appel
		end
	end;
	(*if !vDEBUG then Printf.printf "ap evalNID\n" ;*)
	
(*  pour toutes les boucles b de niveau niveau courant +1 du nid N faire	RechercherExpressionTNj B N *)
and evaluerSN nid  (*tete*) niddepart (*tete niveau courant *) appel mesBouclesOuAppel listeEng isExeE borne tetePred=
List.iter
 	(fun  c ->
		match c with
			IDBOUCLE (num,lt,lf) -> 
				if !vDEBUG then Printf.printf "NID av sous nid de %d  dans autre boucle\n" num;
				(*if isExeE then Printf.printf"evaluerSN isExeE = vrai\n" else Printf.printf"evaluerSN isExeE = false\n" ;*)
(*Printf.printf "evaluerSN contexte dans eval sous nid: \n";
					afficherListeAS appel;
					Printf.printf "FIN CONTEXTE \n";
Printf.printf "evaluerSN cglobales: \n";
					afficherListeAS !abGlobales ;
					Printf.printf "FIN globales \n";*)


				let ((*listeId*)_,_,n) = rechercheTriplet num niddepart.listeTripletNid in
				if !vDEBUG then 
					Printf.printf "1 evaluerSN nid %d nid depart %d  nid tete %d\n" num  (getBoucleIdB niddepart.infoNid.laBoucle)
					(getBoucleIdB nid.infoNid.laBoucle);
				let varDeBouclePred = !varDeBoucleBoucle in
				varDeBoucleBoucle :=n.varDeBoucleNid;

				let info = getBoucleInfoB n.infoNid.laBoucle in
				let valBorne =	if isExeE then getNombreIt (n.infoNid.expressionBorne) 
									info.conditionConstante info.typeBoucle  info.conditionI 
									info.conditionMultiple [] info.estPlus  info.infoVariation n.varDeBoucleNid
								else EXP(CONSTANT (CONST_INT "0")) in
				
				let corps = info.boucleOuAppelB in	
				let typeEval = TBOUCLE ( (getBoucleIdB n.infoNid.laBoucle), !numAppel, 
					(reecrireCallsInLoop n.varDeBoucleNid 	n.lesAffectationsBNid),appel, isExeE, lt,lf) in
				dernierAppelFct := !predDernierAppelFct;
				traiterBouclesInternes 	
							nid (*le noeud complet qui la contient *)
							niddepart (* noeud courant *)
							((getBoucleInfoB (n.infoNid.laBoucle)).nomEnglobante) 
							(* le noeud englobant où il faut s'arreter ici id boucle englobante *)
							n (*sous noeud conserné*)
							[] (* les as de la boucle englobante sans lui *) (*(EXP(n.infoNid.expressionBorne)) *)valBorne
							appel listeEng typeEval !numAppel valBorne isExeE lt lf borne n tetePred false;
				let nouNidEval = List.hd !nouBoucleEval in
				let borneN  =  nouNidEval.expressionBorneToutesIt  in
				let corpsEvalTMPPred = !corpsEvalTMP in
				corpsEvalTMP := [];		
	
				if !vDEBUG then 
				begin
					Printf.printf "av eval sous nid de %d\n" (getBoucleIdB n.infoNid.laBoucle)	;
					Printf.printf "CORPS boucles %d:\n"  (getBoucleIdB n.infoNid.laBoucle);
					(*afficherElementCorpsFonction corps ;	*)
					Printf.printf "av eval sous nid de FIN%d\n"  (getBoucleIdB n.infoNid.laBoucle)	;
					(*Printf.printf "contexte dans eval sous nid: \n";
					afficherListeAS appel;
					Printf.printf "FIN CONTEXTE \n"*)
				end;					
				evaluerSN nid (*tete*) n 	appel corps	(* passer au niveau suivant *) (List.append [typeEval] listeEng) isExeE 
				 borneN tetePred;
				if !vDEBUG then 
					Printf.printf "AP EVALUERSN ajout sousnid de %d = %d 
					dans liste des boucle de %d\n" (getBoucleIdB n.infoNid.laBoucle)	
					num (getBoucleIdB nid.infoNid.laBoucle);
					(*	if lt <> [] then begin Printf.printf "liste des variables IF true :\n"; 
					List.iter (fun e-> Printf.printf "%s "e) lt end;
					if lf <> [] then begin Printf.printf "liste des variables IF false :\n"; 
					List.iter (fun e-> Printf.printf "%s "e) lf end;*)

				let new_b =  new_elementEvalb nouNidEval typeEval !corpsEvalTMP in
				corpsEvalTMP := List.append corpsEvalTMPPred	[ new_b];		

				varDeBoucleBoucle :=varDeBouclePred;()
			| IDAPPEL (_,_,_,_,lt,lf) ->  				
				let _ = 
					evalUneBoucleOuAppel c (reecrireCallsInLoop niddepart.varDeBoucleNid niddepart.lesAffectationsBNid) 
					appel listeEng isExeE  in ()		
	)	mesBouclesOuAppel



let  printendExp l=
	print_commas false 
	(fun max -> if max = NOTHING then Printf.printf "NOTHING" 
					else print_expression (remplacerNOTHINGParAux(EXP(max))) 0) l


let afficherInfoFonctionDuDocUML listeF =	
if listeF <> [] then
begin
	valeurEng :=  NOCOMP ;
	borneAux :=  NOCOMP ;	
	Printf.printf "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?>\n";
	Printf.printf "<flowfacts>\n";
	match ((rechercherEvalParNomAppel !(!mainFonc) 0 0 listeF)) with
		APPELEVAL(tyc,_,corps) ->
			let (isExe,isInLoop) =	(match tyc with TFONCTION(_, _,_,_,_, _,_,_,a,b)-> (a,b) |_->(true,false)) in
			print_tab (1);	Printf.printf  "<function name=\"%s\" " !(!mainFonc) ;
			new_line();	
			if isInLoop = false then if isExe then Printf.printf " executed=\"true\"" else Printf.printf " excuted=\"false\"";
			if (existeFonctionParNom	!(!mainFonc) doc) =false then
			begin
				 Printf.printf "extern=\"true\">\n" ; 
			end
			else begin Printf.printf ">\n" ; afficherCorpsUML corps	 (5)    end;
			new_line ();
			print_tab (1);	Printf.printf  "</function>"; new_line();

			(*afficherInfoFonctionUML !mainFonc corps 1 *) (* plus tard définitions globales asf ???*) 
			Printf.printf "</flowfacts>"	;new_line();
			Printf.printf"<loopsfacts>\n";
			List.iter 
			(fun (id,max) -> 
				Printf.printf "\t <loopId=\"%d\" maxcountAnyCalls=\"" id ;
				(match max with
				EVALEXP(oldMax)->
					if estDefExp oldMax  then  begin print_expTerm oldMax ; Printf.printf  "\" >" 	;	new_line();end
					else
					begin
						Printf.printf "NOCOMP\" expmaxcountAnyCalls=\"maximum(";print_expTerm oldMax;  space();flush(); 
						Printf.printf  ")\" >" 	;	new_line();
					end;
				|EXPMAX(l) ->  Printf.printf "NOCOMP\" expmaxcountAnyCalls=\"maximum(";printendExp l; space() ;flush();  
						Printf.printf  ")\" >" 	;	new_line();)						 	
					)!listeDesMaxParIdBoucle;
			Printf.printf "</loopsfacts>\n"	;flush(); new_line();
		|_-> flush();
	
end

let evaluerFonctionsDuDoc  doc=	
	if !doc.laListeDesFonctions <> [] then
	begin
		let (_, f) = (rechercherFonctionParNom !(!mainFonc) doc) in
		listeASCourant := [];
		globalesVar := !alreadyAffectedGlobales;
		evalStore 	(new_instBEGIN !listeDesInstGlobales) []	;
		abGlobales := !listeASCourant;
(*Printf.printf"GLOBALE\n";
afficherListeAS( !abGlobales);new_line () ;flush(); space();
Printf.printf"FIN GLOBALE\n";*)
		let typeE = TFONCTION(!(!mainFonc),!numAppel, f.lesAffectations, !listeDesInstGlobales, [], [], [],  [], true, false) in  
		dernierAppelFct := typeE;
		predDernierAppelFct := typeE;
		let (_,_) = evaluerFonction !(!mainFonc) f !listeASCourant  (EXP(NOTHING))   [typeE]  typeE true in()			
	end
	else ()

let rec afficherFonction corps tab=
List.iter (fun a->
match a with
	IDBOUCLE (num, _,_) -> 
		if (existeBoucle num) then
		begin
			estNulEng := false;
			let b = rechercheBoucle  num in	
			Printf.printf"Boucle nid...%d \n"num;
			afficherFonction (getBoucleInfoB b).boucleOuAppelB  (tab+3);
			Printf.printf"FIN Boucle nid...%d \n"num;
		end
		else   Printf.printf "Boucle nid %d non trouve\n" num	;

	| IDAPPEL (numf,appel,_,_, _,_) ->
	
		let nomFonction =	
			(match appel with
				CALL(exp,_)->(match exp with VARIABLE(nomFct)->nomFct|_-> "")|_->"") in		
		


		print_tab (tab);	Printf.printf  "<call name=\"%s\" numcall=\"%d\"" nomFonction numf;
		let (fichier , ligne ) = getAssosIdCallFunctionRef numf in 
	
		if (existeFonctionParNom	nomFonction doc) =false then
		begin
			 Printf.printf " line=\"%d\" source=\"%s\" extern=\"true\">" ligne fichier 
		end
		else  
		begin 
			Printf.printf " line=\"%d\" source=\"%s\">" ligne fichier ; 
			new_line();
			let (_, f) = (rechercherFonctionParNom nomFonction doc) in
			afficherFonction f.corps.boucleOuAppel	 (tab+3)    
		end;
	
		print_tab (tab);	Printf.printf  "</call>"; 	new_line()
) corps


let  afficherFonctionsDuDoc doc	=
	Printf.printf "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?>\n";
	Printf.printf "<flowfacts>\n";

		if !doc.laListeDesFonctions <> [] then
		begin
			if existeFonctionParNom  !(!mainFonc) doc then
			begin

				let (_, f) = (rechercherFonctionParNom !(!mainFonc) doc) in
				print_tab (1);	Printf.printf  "<function name=\"%s\">" !(!mainFonc) ;
				new_line (); 
				afficherFonction  f.corps.boucleOuAppel 5 ;	
				
				print_tab (1);	Printf.printf  "</function>"; 
			end
			else Printf.printf "\n/* \t fonction main %s  non trouvee*/\n" !(!mainFonc)
		end;
		new_line();
		Printf.printf "</flowfacts>"	;new_line()


let listCaseFonction = ref []
let existCaseAssosFunction id = List.mem_assoc id  !listCaseFonction
let getCaseAssosFunction  id = List.assoc id !listCaseFonction 
let setNewCaseAssosFunction id na =
List.map (fun(idFunc,list)-> if id =idFunc then (id,na) else (idFunc,list) )!listCaseFonction

let rec  consCaseCorpsFOB corps  numCall  = 
List.iter(fun e-> consCaseUneBoucleOuAppel e numCall)corps


and oneFunction    id    numCall lt lf=	
if  existCaseAssosFunction id then
begin
	let old_assos = getCaseAssosFunction  id in
	listCaseFonction :=		setNewCaseAssosFunction id (List.append [(lt,lf)] old_assos);
end
else listCaseFonction :=		List.append [(id, [(lt,lf)])] !listCaseFonction;
	
and consCaseUneBoucleOuAppel elem  numCall =
match elem with
	IDBOUCLE (num, lt,lf) -> 
		if  (existeNid  num) then
		begin
			let nid = (rechercheNid num) in
			let info = getBoucleInfoB nid.infoNid.laBoucle in
			let mesBouclesOuAppel = info.boucleOuAppelB in
		 	consCaseCorpsFOB mesBouclesOuAppel  numCall
		end

	| IDAPPEL (numf,appel,_,_, lt,lf) ->
		
		let nomFonction =	
			(match appel with
				CALL(exp,_)->(match exp with VARIABLE(nomFct)->nomFct|_-> "")|_->"") in		
		
				if existeFonctionParNom	nomFonction doc then
				begin				
					let (_, func) = (rechercherFonctionParNom nomFonction doc) in
					consCaseFonction nomFonction func (numCall+1) lt lf;	
				end 
				else  oneFunction    nomFonction    numCall lt lf


and consCaseFonction id f   numCall lt lf=	
	oneFunction    id    numCall lt lf;
	consCaseCorpsFOB f.corps.boucleOuAppel   numCall


let evaluerCaseFonctionsDuDoc  doc=	
	if !doc.laListeDesFonctions <> [] then
	begin
		let (_, f) = (rechercherFonctionParNom !(!mainFonc) doc) in
		consCaseFonction !(!mainFonc) f  0 (*num appel*) [] []
	end

let printFuncCaseAssos l=
List.iter(fun (name,listCase) ->
	Printf.printf "\n%s :\n" name;
	List.iter(fun(lt,lf)->
			Printf.printf "\tIF true : "; List.iter (fun e-> Printf.printf "%s "e) lt ;

			Printf.printf "\tIF false : "; List.iter (fun e-> Printf.printf "%s "e) lf ;
			Printf.printf "\n"

	 )listCase
)l
		

let rec consProdT l b=
if b then
	if List.tl l = [] then VARIABLE( List.hd l) else  BINARY (MUL , VARIABLE(  List.hd l), consProdT (List.tl l) b)
else 
	if List.tl l = [] then UNARY( NOT ,VARIABLE( List.hd l)) else  BINARY (MUL ,  UNARY( NOT ,VARIABLE( List.hd l)), consProdT (List.tl l) b)


let consProdCaseTF lt lf=
if lt = [] && lf = [] then CONSTANT( CONST_INT "1")
else if lt = [] then consProdT lf false
	 else if lf = [] then consProdT lt true else BINARY(MUL, consProdT lt true,consProdT lf false)

let nb_loop = ref 0
let rec  consNbCorpsFOB corps  numCall evalFunction = 
	if corps = [] then CONSTANT( CONST_INT "0")
	else 
	begin
		let v1 = consNBUneBoucleOuAppel (List.hd corps) numCall evalFunction in
		let v2 = consNbCorpsFOB (List.tl corps) numCall evalFunction in

		let add1 = calculer  (EXP(v1)) !infoaffichNull  []  in
		let add2 = calculer  (EXP(v2)) !infoaffichNull  [] in
		if estNoComp add1 = false && estNoComp add2 =false &&  estNul add1 && estNul add2 then CONSTANT( CONST_INT "0")
			else if estNoComp add1 = false && estNul add1 then v2 else if estNoComp add2 = false && estNul add2 then v1 else BINARY(ADD, v1 ,v2)
	end
	
	
and consNBUneBoucleOuAppel elem  numCall evalFunction=
match elem with
	IDBOUCLE (num, lt,lf) -> 
		
		let nvar =  Printf.sprintf "%s_%d_%d_%d" "NBIT" num numCall  !nb_loop in	
		nb_loop := !nb_loop +1;
 
		if  (existeBoucle   num) then
		begin
			let b = (rechercheBoucle  num) in
				
			let info = getBoucleInfoB b in
			let mesBouclesOuAppel = info.boucleOuAppelB in
			let profinit = consProdCaseTF lt lf in 
			let valprod = (calculer  (EXP(profinit)) !infoaffichNull  []) in
			let prod = if estNoComp valprod = false && estUn valprod then VARIABLE(nvar) else
					 BINARY(MUL, VARIABLE(nvar), profinit) in
			let other = consNbCorpsFOB mesBouclesOuAppel  numCall evalFunction in
			let value = calculer  (EXP(other)) !infoaffichNull  [] in
			if estNoComp value = false &&  estNul value then CONSTANT( CONST_INT "0")
			else if estNoComp value = false &&  estUn value then prod else  BINARY(MUL,prod,other)
		end
		else begin  CONSTANT( CONST_INT "0") end

	| IDAPPEL (numf,appel,_,_, lt,lf) ->
		
		let nomFonction =	
			(match appel with
				CALL(exp,_)->(match exp with VARIABLE(nomFct)->nomFct|_-> "")|_->"") in		
		
				if existeFonctionParNom	nomFonction doc then
				begin				
					let (_, func) = (rechercherFonctionParNom nomFonction doc) in
					consNBFonction nomFonction func numf lt lf evalFunction;	
				end 
				else if nomFonction = evalFunction then  consProdCaseTF lt lf else CONSTANT( CONST_INT "0")


and consNBFonction id f   numCall lt lf evalFunction=	
let prod = consProdCaseTF lt lf in
let valprod = (calculer  (EXP(prod)) !infoaffichNull  []) in

if id = evalFunction then (* fonction non recursive*)    prod 
else
begin
	let other =consNbCorpsFOB f.corps.boucleOuAppel   numCall evalFunction in
	let value = calculer  (EXP(other)) !infoaffichNull  [] in
	if estNoComp value = false && estNul value then CONSTANT( CONST_INT "0")
			else if estNoComp value = false && estUn value then prod else
		 			if estNoComp valprod = false && estUn valprod then other else   BINARY(MUL,prod,other)
end


let evaluerOneFunctionOfDoc  doc evalFunction=	
	if !doc.laListeDesFonctions <> [] then
	begin
		let (_, f) = (rechercherFonctionParNom !(!mainFonc) doc) in
	 	nb_loop :=  0;
		Printf.printf "nbAppels de %s = "evalFunction ; print_expression (consNBFonction !(!mainFonc) f  0 [] [] evalFunction) 0;flush(); space();
		new_line()
	end


let rec evaluerNbFunctionOfDoc  doc evalFunction=	
	match evalFunction with
	[]-> new_line()
	|e::l -> begin
		 evaluerOneFunctionOfDoc doc !e ;
		 evaluerNbFunctionOfDoc doc l; flush(); space();new_line()
		 end


let initref (result : out_channel) (defs : file) =
  	out := result;
	enTETE :=  false;
	numAppel :=  0;
	estNulEng :=  false;
	estDansBoucle :=  false;
	varDeBoucleBoucle := "";
	analyse_defsPB defs(*;
	print_AssosIdLoopRef  !listLoopIdRef;	
	print_listIdCallFunctionRef !listIdCallFunctionRef*)

let printFile (result : out_channel)  (defs2 : file)=
	idBoucle := 0;
	idAppel:=0;
	nbImbrications := 0;
 	out := result;
	enTETE :=  false;
	numAppel :=  0;
	estNulEng :=  false;
	estDansBoucle :=  false;
 

	analyse_defs defs2; (*step 1*)
	(*afficherNidDeBoucle doc;	 *)
	(*Printf.printf "les globales\n";
	List.iter(fun x->Printf.printf "%s\t" x)!alreadyAffectedGlobales;
	Printf.printf "les tableaux\n";
    print_AssosArrayIDsize !listAssosArrayIDsize;
	Printf.printf "les typesdefs tableaux\n";
	print_AssosArrayIDsize !listAssosTypeDefArrayIDsize;
	Printf.printf "les pointeurs\n";
	print_AssosPtrTypeList !listeAssosPtrNameType;*)

  (*	evaluerCaseFonctionsDuDoc  doc;
	printFuncCaseAssos !listCaseFonction;*)

 	flush ()    ;
	if !doc.laListeDesNids <> [] then
	begin
		evaluerNbFunctionOfDoc  doc  !evalFunction;
		Printf.printf "\n\n\n DEBUT EVALUATION \n\n\n";
		evaluerFonctionsDuDoc doc ; 
		(*afficheNidEval !docEvalue.maListeNidEval; *)
 		Printf.printf "\n\n\n FIN EVALUATION \n\n\n";

  		afficherInfoFonctionDuDocUML !docEvalue.maListeEval; 
	end
	else afficherFonctionsDuDoc  doc;
 	 new_line ();
	(*Cprint.print stdout defs;*)
  flush ()    
