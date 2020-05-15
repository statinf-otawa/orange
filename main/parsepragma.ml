
(* parseprama.ml 
Marianne de Michiel 2020*)
open Printf
open Util

let extract s =
try
  Scanf.sscanf s "%s %d %s " (fun x y z -> (x,y,z))
  with Scanf.Scan_failure _ ->
  ("", 0,"")

let extractAnnotations s =
  try
    let (boundtype1, value1, boundtype2, value2) = Scanf.sscanf s "%s %d %s %s %d %s %d" (fun x y z t u v w -> (t,u, v, w)) in
    if (boundtype1 = "max" && boundtype2 = "min") then (value1, value2)
    else if (boundtype1 = "min" && boundtype2 = "max") then (value2, value1)
    else (-1, -1)
  with Scanf.Scan_failure _ ->
    try
        let (boundtype1, value1) = Scanf.sscanf s "%s %d %s %s %d" (fun x y z t u  -> (t,u)) in
        if (boundtype1 = "max"  ) then (value1, -1)
        else if (boundtype1 = "min") then (-1, value1)
        else (-1, -1)

    with Scanf.Scan_failure _ ->(-1, -1)
    
    
let extractAnnotationsendLine s =
  try
    let (boundtype1, value1, boundtype2, value2) = Scanf.sscanf s "%s %s %d %s %d" (fun z t u v w -> (t,u, v, w)) in
    
    if (boundtype1 = "max" && boundtype2 = "min") then (value1, value2)
    else if (boundtype1 = "min" && boundtype2 = "max") then (value2, value1)
    else (-1, -1)
  with Scanf.Scan_failure _ ->
    try
        let (boundtype1, value1) = Scanf.sscanf s "%s %d %s %s %d" (fun x y z t u  -> (t,u)) in
        if (boundtype1 = "max"  ) then (value1, -1)
        else if (boundtype1 = "min") then (-1, value1)
        else (-1, -1)

    with Scanf.Scan_failure _ ->(-1, -1)
    



let analyse_pragmaLine lineFile  =
  if lineFile != "" then
  (
    let (file , line, next) = extract lineFile in
    
   if next = "loopbound" then begin
      let loca = (Loc.make file line) in
      let (max,min ) = extractAnnotations lineFile in
      let bb = (LoopBounds.make max min) in
      locationMapadd loca bb;
      ()
   end
  )

let analyse_onepragma file  line next   =
   if next != "" then
  ( 
	  let length = String.length next in
	  let newString =
	  try
			let beginS = String.index  next   'l' in
			 String.sub next beginS (length - beginS)
	   with  Not_found ->   "" in
	
	  if newString != "" then
	  begin
		   let first = Scanf.sscanf newString "%s" (fun x   -> x) in
 		   if first = "loopbound" then begin
			  let loca = (Loc.make file line) in
			  let (max,min ) = extractAnnotationsendLine newString in
			  let bb = (LoopBounds.make max min) in
			  locationMapadd loca bb;
			  ()
		   end
	  end
  )
    
  

  let parse_file filename =
    let in_channel = open_in filename in
    try
      while true do
        let line = input_line in_channel in
            analyse_pragmaLine line ;
      done;

    with End_of_file ->
      close_in in_channel;
      (**)
