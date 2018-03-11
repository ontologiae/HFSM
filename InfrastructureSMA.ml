open Spacechampion_t;;
open Printexc;;
(*open Unix*)

module H = BatHashtbl;;

module O = struct 
  include BatOption 
  let eqOption a b = match a with
    | Some c -> c = b
    | None   -> false
end;;

module Debug = struct
  let enable = ref false
end


exception CherchTransitionListeVide;;
exception AscendanceInterval of string;;
       
exception ErreurConstructionPileMessageInTestTransition;;
exception ListeTransitionValideVide;; (*Ce qui n'est pas un problème en soit*)
exception ErreurQuiNormalementArrivePas___AgentNonExistantDansMasEvent;;
exception DirectionFausse;;
exception PasDobjetJeuErreurgetCurrentObjet;;
exception PasDobjetJeuErreurgetCurrentObjet1;;
exception PasDobjetJeuErreurgetCurrentObjet2;;
exception AucunEtatDisponiblePourLAgent;;

exception NO_ID_ERREUR of string;;

Printexc.record_backtrace true;; 


let pdebug s = ();;

module L = struct
        include BatList
        (** Fonction supplémentaires pour les listes*)
        (*let rec union m = function 
                | [] 		-> m
                | t :: q     	-> t :: (union (L.remove  m t) q);;  *)
        let rec union l1 l2 = let lr = append l1 l2 in unique lr

        let rec intersect m = function
                | []                     -> []
                | t::q when mem t m -> t :: (intersect (remove m t) q) 
                | t :: q                 -> intersect m q;; 

        let rec difference  m1 m2 = match m1 with
        | [] 				->[]
        | t::q when     mem t m2 -> difference q (remove m2 t)
        | t::q 				-> t::(difference  q m2);;

end;;


let (@@) = Array.append;;
let (>::) e a = Array.append [|e|] a;;   


let now = function () ->   int_of_float(Unix.gettimeofday()-.946681200.);;


let raise_msg = function
  | AscendanceInterval (s) -> 
      Printf.printf "Exception : %s\n" s;
      Printexc.print_backtrace (Pervasives.stderr);
      raise (AscendanceInterval(s))
  | e ->  (* catch all exceptions *)
      Printf.eprintf "Exception ici : %s" (Printexc.to_string e);
      (*If using Ocaml >= 3.11, it is possible to also print a
        backtrace: *)
      Printexc.print_backtrace (Pervasives.stderr);
      raise (AscendanceInterval("autre"))
;;

(* Règles :

   - Un état qui a un état fils, ne peut pas avoir d'action, que des begin et end
   action
   - Lorsqu'on switche d'état, il faut remonter de l'état où on est (le fils le
   plus profond) jusqu'à l'état responsable de la transition et d'appliquer tous
   les end_action entre
   - Pour chaque état dans lequel on peut basculer suite à une transition, il doit
   avoir le même parentstate que l'état qui l'a appelé SI transition cible = n
   fils cible
   - Tout état doit avoir un parentState, sauf l'état englobant qui n'en n'a pas
   ---> bien faire gaffe au fait que les setParentState et isIn doivent être bien
   affectés 

   TODO : 
   - créer le addTransition , on fera ça à la main OK, AT
   - Ecrire le cherchetransition OK, AT
   - 2) ecrire le getMail ds agent
   - rajouter la pile de mail -> principe dès qu'un event match avec une
   transition, on la vire de la liste, et on continue à dépiler. Au bout de 5s, le
   mail est considéré comme trop vieux  ; ds agent
   -1) ecrire le module, contenant un objet avec données seulement qui servira de
   bureau de poste 
   -3) en lui donnant l'agent, la fonction agent-> bool de la transition ira
   chercher le mail : lui préparer une fonction tout bien -> en fait c là qu'elle
   dépilerait toute la pile
*)

module TimeLine = struct
        type eventime =
                | Marker   of  float
                | Goal     of  float
                | Asked    of  float
                | MarkerRule of float * float * ( float -> float) 

        type intern = {
                mutable timeline : (string,eventime) H.t ; 
        }

        let create () = {
                timeline = H.create 128
        }

        let addMarker self id =
                let deja_existant =  (H.find_all self.timeline id |> L.filter (fun e -> match e with Asked _ | Marker _ -> true | _ -> false) |> L.length) > 0 in
                if not deja_existant then
                        H.add self.timeline id (Marker(Unix.gettimeofday()))

        let addGoal self idMarker time =
                (*test*)
                 let deja_existant = (H.find_all self.timeline idMarker |> L.filter (fun e -> match e with Asked _ | Marker _ -> true | _ -> false) |> L.length) > 0 in
                 if not deja_existant then
                         H.add self.timeline idMarker (Goal(Unix.gettimeofday()+.time))


        (*TODO 11/6 : Il faudra penser à VIDER la hashtable, car celle-ci va se remplir indéfiniment sur les qq id présentés*)

        let age self id =
          let now  = Unix.gettimeofday() in
          match H.find_all self.timeline id |> L.rev |> L.filter (fun e -> match e with Asked _ -> true | _ -> false) with
            | [Marker t1 ; Goal t2]      -> t1 -. now
            | _                   as l   -> "Taille liste="^(L.length l |> string_of_int )^".TimeLine.age cas non géré"  |> failwith 

        let isReached self id = (*TODO*)
          let now  = Unix.gettimeofday() in
          let bornes = H.find_all self.timeline id in 
          match bornes |> L.rev with
          | [Marker t1 ; Goal t2] -> now > t1 && now > t2
          | _                     -> failwith "TimeLine.isReached cas non géré"


        let isInBound self id =
                let now  = Unix.gettimeofday() in
                let bornes = H.find_all self.timeline id in 
                match bornes |> L.rev with
                | [Marker t1 ; Goal t2] -> now > t1 && now < t2
                | _                     -> failwith "TimeLine.isInBound cas non géré"


        let each self ?jour:(jour=0) ?heure:(heure=0) ?minute:(minute=0) ?seconde:(seconde=0) ~goal:goal ~id:id ~dof:f () =
                let deja_existant =  (H.find_all self.timeline id |> L.filter (fun e -> match e with MarkerRule _ -> true | _ -> false) |> L.length) > 0 in
                let rythm         = float_of_int (jour*24*60*60 + heure*60*60 + minute*60 + seconde) in
                if not deja_existant then begin
                        H.add self.timeline id (MarkerRule(Unix.gettimeofday(), rythm, f));
                        H.add self.timeline id (Goal(Unix.gettimeofday()+.goal))
                end



       let verify_apply self id =
        let now  = Unix.gettimeofday() in
        let lst  = H.find_all self.timeline id  in
        let isFirst = L.exists (fun e -> match e with Asked t -> true | _ -> false) lst in
        let d,r,f = L.find_map (fun e -> match e with MarkerRule(d,r,f) -> Some(d,r,f) | _ -> None ) lst in
        let tempsEcoule = 
                match isFirst with
                | true ->
                        let filtered = lst |> L.filter_map (fun e -> match e with Asked t -> Some t | _ -> None) in
                        let last = L.fold_left max  9_000_000. filtered in
                        (*let _ = last |> string_of_float |> print_endline in*)
                let _ = H.add self.timeline id (Asked now) in
                now -. last
                | false ->  let _ = H.add self.timeline id (Asked now) in
                now -. d 
                in
        (*let _ = tempsEcoule |> string_of_float |> print_endline in*)
        f (tempsEcoule/.r);; (*Temps écoulé mais en fonction du rythme*)
                 

        let seconds_of ?jour:(jour=0) ?heure:(heure=0) ?minute:(minute=0) ?seconde:(seconde=0) () =
          float_of_int (jour*24*60*60 + heure*60*60 + minute*60 + seconde)
end


type 'event transition = 
  | Condition    of (int -> bool) 
  | Event        of ('event -> bool)
  | EventOr      of ('event -> bool) * 'event transition
  | EventAnd     of ('event -> bool) * 'event transition
  | EventXor     of ('event -> bool) * 'event transition
  | EventNot     of ('event -> bool)  
  | ConditionOr  of (int -> bool)   * 'event transition 
  | ConditionAnd of (int -> bool)   * 'event transition
  | ConditionXor of (int -> bool)   * 'event transition
  | ConditionNot of (int -> bool);;




(** TODO TODO 7/21014
 * On va coller l'uuid de l'agent à chaque state OK
 * On va mettre une mixtbl pour les event, pour chaque agent, vidée à chaque fois. Elle comportera qu'un seul évènement, l'event courant TODO
 * *)        



(** MÉMOIRE GLOBALE
      
 * 
 * *)

(* MIXTBL POUR LE SMA COMPLET*)




module type E = sig
        type event
end




module  type StateType =  
        sig

  (**Evènement, généralement un type somme*)

  (*type event = E.event *)


  type event 

  type state_t = {
    mutable nom : string;
    mutable parentstate : state_t option;
    mutable substate : state_t option;
    mutable transitions :
      (state_t option * event transition option) list;
    mutable begin_action : unit -> unit;
    mutable action : int -> unit; (*Temps depuis lequel on est coincé dans cet état*)
    mutable end_action : unit -> unit;
    mutable event_success : event option;
    mutable time          : int;
    mutable startTime     : int;
    mutable uuid_agent    : Uuidm.t;
  }
  val create : string -> state_t
  val get_uuid  : state_t -> Uuidm.t
  val set_uuid : state_t -> Uuidm.t -> unit
  val setBeginAction : state_t -> (unit -> unit) -> unit
  val setAction : state_t -> (int -> unit) -> unit
  val setEndAction : state_t -> (unit -> unit) -> unit
  val executeBeginAction : state_t -> unit
  val executeAction : state_t  -> unit
  val executeEndAction : state_t -> unit
  val getParent : state_t -> state_t option
  val getTransitions :
    state_t -> (state_t option * event transition option) list
  val setTransitions :
    state_t ->
    (state_t option * event transition option) list -> unit
  val isIn : state_t -> state_t -> unit
  val setNom : state_t -> string -> unit
  val getNom : state_t -> string
  val getFils : state_t -> state_t option
  val setFils : state_t -> state_t -> unit
  val get_event_success : state_t -> event option
  val set_event_success : state_t -> event option -> unit
  val vide_event_success : state_t -> unit
  val getParentPur : state_t -> state_t
  val setParent : state_t -> state_t -> unit
  val cherchePlusHautPere : state_t -> state_t
  val listPeres : state_t -> state_t list
  val ascendanceInterval : state_t -> state_t option -> state_t list
  val chercheDernierFils : state_t -> state_t

  val chercheTransition :
    state_t -> event option -> bool * state_t * state_t * state_t * state_t

  val has : state_t -> state_t -> unit
  val addTransition :
    state_t -> state_t -> event transition -> unit

  val setStartTime      : state_t -> unit 
  val updateTime        : state_t -> unit
  val getTime           : state_t -> int


end


module State (E : E)  : (StateType with type event = E.event) =
struct

  type event = E.event

  type  state_t = {  
    mutable nom : string;
    mutable parentstate   :   state_t option;
    mutable substate      :   state_t option;
    mutable transitions   : ( state_t option * E.event transition option) list; 

    mutable begin_action  : unit -> unit;
    mutable action        : int  -> unit;
    mutable end_action    : unit -> unit;
    mutable event_success : E.event option;
    mutable time          : int;(**En seconde*)
    mutable startTime     : int;
    mutable uuid_agent    : Uuidm.t;
  }
  

  let create  nom = { 
    nom           = nom ;
    parentstate   = None;
    substate      = None;
    transitions   = [];
    begin_action  = (fun () -> pdebug "begin_action vide";);
    action        = (fun i  -> pdebug "action vide";);
    end_action    = (fun () -> pdebug "end_action vide";);
    event_success = None;
    time          = 0;
    startTime     = 0;
    uuid_agent    = Uuidm.nil;
  }


  let get_uuid self = self.uuid_agent  

  let set_uuid self uuid = self.uuid_agent <- uuid 
  let getTime self              = self.time
  let updateTime self           = (*"updateTime (start,now):"^(string_of_int self.startTime)^","^(string_of_int self.time) |> print_endline;*)
                                         self.time <- ( (Unix.gettimeofday() |> int_of_float) - self.startTime)
  let setStartTime self         = self.time <- 0; self.startTime <- (Unix.gettimeofday() |> int_of_float)

  let setBeginAction self st        = (self.begin_action <- st;)

  let setAction self st             = (pdebug "Action Modifiée !!"); (self.action <- st;)

  let setEndAction self st          = (self.end_action <- st;)

  let executeBeginAction self       = self.begin_action ()

  let executeAction self            = self.action self.time
    
  let executeEndAction self          = self.end_action ()
    

    
  let getParent self = self.parentstate

  let getTransitions self = self.transitions

  let setTransitions self t         = (self.transitions <- t;)
    

    

  let isIn self a                   =  ( self.parentstate <- Some(a); )


  let setNom self s                 = (self.nom <- s;)
    
  let getNom self = self.nom
    
  let getFils self = self.substate
    
  let setFils self a                = (self.substate <- Some(a);)

  let get_event_success  s          =  s.event_success
  let set_event_success  s  e       =  s.event_success <- e

  let vide_event_success s          = ((s.event_success <- None);)



  let getParentPur self = 
    let rend = function 
      |None ->   self
      |Some(a) -> a
    in rend self.parentstate


  let setParent self a              = 
    ( self.parentstate <- Some(a);) 



  (*  Cherche l'état père de plus haut degré *)   
  let cherchePlusHautPere self = 
    let rec cherchePlusHaut cur = function
      | None -> cur
      | Some(parent) -> cherchePlusHaut parent (getParent parent)
    in cherchePlusHaut self self.parentstate


  (* Renvoi la liste de pères, du plus haut degré vers l'état self*)   
  let listPeres self =
    let rec listAscendants = function
      | None -> []
      | Some(parent) ->
          L.append (listAscendants(getParent parent)) (parent::[])
    in listAscendants self.parentstate


  (* Ascendance d'un state (self) jusqu'à orig On utilise des comparaisons de pointeur : normalement les objets  sont différents, donc ça suffit
  *)

  (*A partir de self jusqu'à l'état fin, on génère la liste des états asendants : peère de self -> pèere de père de self -> ... -> fin*)
  let ascendanceInterval self fin   =
    let rec ascendanceIntervalFunc = function
      | None, _ ->  Printexc.print_backtrace (Pervasives.stderr); raise (AscendanceInterval("Etat début intervalle non présent dans ascendanceInterval"))
      | _ , None ->  Printexc.print_backtrace (Pervasives.stderr);  raise (AscendanceInterval("Etat fin intervalle non présent dans ascendanceInterval"))
      | Some(parent), Some(orig) when orig == parent -> orig::[]

      | Some(parent), Some(orig) when orig != parent -> L.append
          (ascendanceIntervalFunc ( (getParent parent),Some(orig) ) )
        (parent::[])
      | Some _ , Some _ -> raise (AscendanceInterval("Cas de filtrage non prévu dans ascendanceInterval"))
    in ascendanceIntervalFunc (Some(self),fin)




  (*  Cherche l'état fils de plus haut degré *)
  (*TODO : Marche pas !!! Explore pas toutes les branches !!*)
  let chercheDernierFils self  = 
    let rec chercheDernierFilsFunc cur = function
      | None       -> cur
      | Some(fils)  -> chercheDernierFilsFunc fils (getFils fils)
    in chercheDernierFilsFunc self self.substate



  
  (* Cherche une transition valide parmi les pères
     Fais un L.map sur la liste des transition et testTransition pour renvoyer
     bool*self*etatpère transition*etat cible transition*son fils
     bool*state*state*state*state *)
  (*Le principe est simple : c'est le père de plus haut degré n qui a la priorité pour tester la transition, puis celui de n-1, jusqu'à n-k l'état de départ*)
  let chercheTransition self event_courant  =

    (* Renvoi la liste des ascendants, SELF non inclu*)
    let rec listAscendants = function
      | None -> []
      | Some(parent) -> parent::(listAscendants(getParent parent))
    in 
    let ouex a b = if a then not b else b
    (*C'est là qu'il faut récup tous les message qu'on trouve dans agent c'est
      là qu'on va lancer le nettoyage, mais _avant_ *)
    in 
    (*On construit la liste des messages sans options et sans None*)
    let rec getListEvents = function 
      | Some(mevt)::q -> mevt::getListEvents(q)
      | [] -> []
      | None::[] -> [] (*raise ErreurConstructionPileMessageInTestTransition*)
      | None::q -> [] 
    (*TODO : refaire L.filter func (getListEvents...)*)
    in
    (** Applique la fonction de test de transition*)
    (*  On applique le principe selon laquelle on ales exceptions listés ci-après, c'est que la transition n'est pas la bonne 
        Typiquement, cela s'applique  si on test une transition de pose d'objet alors que l'event est un déplacement : les objets/autres nains sont pas là, ce qui est logique*)
    let testFonctionTransition  func x = try func(x)
      with 
        | ErreurConstructionPileMessageInTestTransition -> pdebug "Exc:ErreurConstructionPileMessageInTestTransition"; false
        | PasDobjetJeuErreurgetCurrentObjet             -> pdebug "Exc:PasDobjetJeuErreurgetCurrentObjet";false
        | PasDobjetJeuErreurgetCurrentObjet1            -> pdebug "Exc:PasDobjetJeuErreurgetCurrentObjet1";false
        | PasDobjetJeuErreurgetCurrentObjet2            -> pdebug "Exc:PasDobjetJeuErreurgetCurrentObjet2";false 
        | ErreurQuiNormalementArrivePas___AgentNonExistantDansMasEvent -> pdebug "Exc:ErreurQuiNormalementArrivePas___AgentNonExistantDansMasEvent";false in

    (** On vérifie que la mini grammaire codant la transition s'applique.
        * On lui donne l'arbre syntaxique de la transition*)
    let rec valideTransition event_courant ast =
            let _ = updateTime self in
      (*  let match_event_et_denonce event list_event  =
          match L.mem event list_event with
          | true  -> (**)self.event_success  <- Some(event); true
          | false -> (**) self.event_success <- None;        false in*)
      (* On considère le test de l'event OK, si event_success, qui est considéré comme l'event courant ayant atteint l'agent est celui correspondant à la transition*)
      let testEvent optionV func = 
        match optionV with
          | Some e -> pdebug " on a un event"; func e
          | None   -> pdebug " trouve rien"; false in
      match ast with
        | Event eventFunc              -> testEvent event_courant eventFunc
        | Condition (func)             ->  func self.time
        | ConditionNot (func)          ->  not (func self.time) 
        | ConditionXor (func, expre)   ->  ouex (func self.time)( valideTransition event_courant expre )
        | ConditionAnd (func, expre)   ->  (func self.time) && ( valideTransition event_courant expre )
        | ConditionOr (func, expre)    ->  (func self.time) || ( valideTransition event_courant expre )
        | EventNot eventFunc           ->  let isOK = testEvent event_courant eventFunc in
                                           not (isOK)
        | EventXor (eventFunc, expre)  ->   let isOK = testEvent event_courant eventFunc in
                                            ouex ( isOK ) ( valideTransition event_courant expre )
        | EventAnd (eventFunc, expre)  ->   let isOK = testEvent event_courant eventFunc  in
                                            isOK  &&   ( valideTransition event_courant expre )
        | EventOr  (eventFunc, expre)  ->   let isOK = testEvent event_courant eventFunc in
                                            isOK  ||   ( valideTransition event_courant expre )

    in
    (** Supprime tous les none dans la liste de couples Etat Cible   *   Transition *)
    let rec getListTransitionsSansOption = function 
      | (Some(stateCible),Some(laTransition))::q  -> (stateCible,laTransition)::getListTransitionsSansOption(q)
      | []                                        -> [] 
      | (None,_)::[]                              -> []  (*raise ErreurConstructionPileMessageInTestTransition*)
      | (None,_)::q                               -> []  (*raise ErreurConstructionPileMessageInTestTransition*)
      | (_,None)::q                               -> [] (*raise ErreurConstructionPileMessageInTestTransition*)
    in
    (* pour un état donné, renvoi des transition de l'état avec leur résultat*)

    (*PREND  : un évènement, une liste de transition et un agent
      RENVOI : une liste  de bool * state -cible- * state origine transition list OU bool est VRAI *)
    let  chercheTransitionInState event_courant liste_ascendance pereCandidat = 
      L.map   ( function  elem    -> let (cible,tr) = elem in 
                                     let _ = pdebug ("[chercheTransitionInState] "^getNom cible) in
                                     ( valideTransition event_courant tr , cible, pereCandidat ))   liste_ascendance 
                  |> L.filter ( fun (b,_,_) -> b )
    (* c'est là qu'on peut les associer !! *)

    (* Cherche une transition valide parmi les pères
       Fais un L.map sur la liste des transition et testTransition pour renvoyer
       bool*self*etatpère transition*etat cible transition*son fils
       bool*state*state*state*state *)
    in 

    (*PREND : une liste de transition et un agent
      RENVOI : une liste  de bool * state -cible- list OU bool est VRAI *)
    (* CETTE FONCTION LANCE LES CALCULS DE TRANSITIONS VALIDES, elle remonte tout !*)
    let rec listTransitionCalculeeInListState event_courant transition_list =
            let _ = pdebug "<l>" ; L.iter (fun s -> pdebug ("[listTransitionCalculeeInListState] "^getNom s)) transition_list ;  pdebug "</l>" ;in
      match transition_list with
        | pereCandidat::q  -> 
            let res =  ( chercheTransitionInState event_courant (getListTransitionsSansOption (getTransitions pereCandidat) )  pereCandidat)
            in 
            L.append res (listTransitionCalculeeInListState event_courant q) (*On remonte au père si on a rien trouvé*)
        | []               ->  []
    in
    let write_infos = function (b,w,x,y,z) -> match b with
      | true  -> pdebug ("[TRANSITION OK]  ; "^(getNom w^"  --- Pere Transition orig: "^getNom x^"  --- Transition cible: "^getNom y^"  --- Nieme fils cible: "^getNom z))
      | false -> pdebug ("[TRANSITION NON VALIDE] ; "^(getNom w^" ---Pere Transition orig: "^getNom x^" ---Transition cible: "^getNom y^" ---Nieme fils cible: "^getNom z))

    in
    let rec  cherchTransitionParmisPeres event_courant ascendances   = 
            let _ = pdebug "<l>" ; L.iter (fun s -> pdebug ("[cherchTransitionParmisPeres] "^getNom s)) ascendances ;  pdebug "</l>" in
      (* On cherche la liste des transition valide parmi tous les états père, en commançant par le haut*)
      match listTransitionCalculeeInListState event_courant ascendances  with
        (* Pas de transitions !*)
        | []                  -> pdebug "Aucune transition trouvée"; (false,self,self ,self ,self )
        (* TODO : On a pas pensé au cas où ya PAS de transition dans
           l'état courant et qu'il faille aller voir le fils --> Normalement
           ça doit pas arriver !*)


        | laTransition  :: []  ->  let (boolres,etatPereNouvelEtat,etatpereEtatActuel) = laTransition in
                                   let result = (boolres,self ,etatpereEtatActuel,etatPereNouvelEtat,(chercheDernierFils etatPereNouvelEtat))
                                   in write_infos result; result

        | laTransition :: q     -> let (boolres,etatPereNouvelEtat,etatpereEtatActuel) = laTransition in
                                   let _ = pdebug "<l>" ; L.iter (fun (_,s,_) -> pdebug ("[cherchTransitionParmisPeres] "^getNom s)) (laTransition::q) ;  pdebug "</l>" ;in 
                                   pdebug ("[WARNING] : INDETERMINISME --> plus de deux transitions valide dans "^(getNom self));
                                   (*Dans ce cas, on doit les traiter
                                     à la suite, et gérer la suppression
                                     des mails 
                                     7/21014 que si elles sont au même niveau*)
                                   let result = (boolres,self ,etatpereEtatActuel,etatPereNouvelEtat,(chercheDernierFils etatPereNouvelEtat))
                                   in write_infos result; result
                                     

    in 
    let liste_ascendance = listAscendants (Some self) |> L.rev in
    let _ = L.iter (fun s -> pdebug ("[Etat pere] "^getNom s)) liste_ascendance in
    (* ON LANCE LA FONCTION PRINCIPALE DE LA FONCTION PUBLIQUE  : OUF !!! *)
    cherchTransitionParmisPeres event_courant liste_ascendance
  (*  RETURN :    bool  *  self  *  etatpère transition  *  etat cible transition  *  son père   *)

  (* Fonctionnement :
   *On commence par le père le plus haut
    L: On regarde toutes ses transition
       On filtre celles qui sont vrais
       Si > 1 warning -> non déterminisme
       Si une est vrai on arrête, sinon on recommence en L*)



      

  (* Défini un sous état rattaché à l'état  *)   
  let has self a             = (self.substate <- Some(a);)


  let addTransition self cible trstion =
    (self.transitions <- (Some(cible),Some(trstion))::self.transitions; )
end





module type  AgentType =  
sig


  type event 
  type state_t  
  (* Définition des données de l'agent*)
  type  agent_t = {
    mutable currentState     :  state_t option ;
    mutable birthtime        : float ; 
    mutable now              : float ; 
    mutable pileEvents       : event option list ;
    mutable historique_etat  : (string * float * string) list ; 
    mutable id               : int ;
    mutable clockForState    : TimeLine.intern;
    mutable uuid             : Uuidm.t;
  }


  val create                :  unit ->  agent_t
  val createState           :  agent_t -> string -> state_t
  val getCurrentState       :  agent_t -> state_t
  val getCurrentStateName   :  agent_t -> string
  val cycle                 :  agent_t  -> unit 

  val getPileEvent          :  agent_t ->  event option list
  val receiveEvent          :  agent_t ->  event  -> unit
  val videPileEvent         :  agent_t ->  unit
  val setStateAg            :  agent_t ->  state_t -> state_t -> state_t -> unit


  val startClockForCurState :  agent_t -> float -> unit 
  val startClockForState    :  agent_t -> state_t option -> float -> unit
  val checkClockForState    :  agent_t -> state_t option -> bool
  val checkClockForCurState :  agent_t -> bool

  val setStartState         :  agent_t ->   state_t -> unit

  val set_uuid : agent_t -> Uuidm.t -> unit
  val get_uuid : agent_t -> Uuidm.t

  val waitTransition : agent_t -> from:state_t ->
                     tos :state_t ->
                     ?action:(int -> unit) option ->
                     wait:float -> 
                     pere:state_t -> unit -> unit

  val creationTransitionSimplePreCurPost :
    from:state_t ->
    tos:state_t  ->
    conditionTransition:event transition ->
    preAction:(unit -> unit) ->
    action:(int -> unit) ->
    postAction:(unit -> unit) -> pere:state_t -> unit

  val creationTransitionSimplePreCur :
    from:state_t ->
    tos:state_t  ->
    conditionTransition:event transition ->
    preAction:(unit -> unit) ->
    action:(int -> unit) -> pere:state_t -> unit
    
  val creationTransitionSimplePre :
    from:state_t ->
    tos:state_t  ->
    conditionTransition:event transition ->
    preAction:(unit -> unit) -> pere:state_t -> unit

  val creationTransitionSimplePost :
    from:state_t ->
    tos:state_t  ->
    conditionTransition:event transition ->
    postAction:(unit -> unit) -> pere:state_t -> unit

    
  val creationTransitionSimpleCurPost :
    from:state_t ->
    tos:state_t  ->
    conditionTransition:event transition ->
    action:(int -> unit) ->
    postAction:(unit -> unit) -> pere:state_t -> unit
    
  val creationTransitionSimpleAction :
    from:state_t ->
    tos:state_t  ->
    conditionTransition:event transition ->
    action:(int -> unit) -> pere:state_t -> unit
    
  val creationTransitionSimple :
    from:state_t ->
    tos:state_t   ->
    conditionTransition:event transition -> pere:state_t -> unit



  val printCurState : agent_t -> unit

end
(**module Agent (E : E) (S : StateType  with type event = E.event) : (AgentType  with  type state_t = S.state_t)  =*)
module Agent  (S : StateType  ) : (AgentType  with  type event = S.event)  =
        struct
          type event = S.event
          type state_t = S.state_t

          type  agent_t = { 
            mutable currentState     : state_t option ;
            mutable birthtime        : float ; 
            mutable now              : float ; 
            mutable pileEvents       : event option list ;
            mutable historique_etat  : (string * float * string) list ; 
            mutable id               : int ;
            mutable clockForState    : TimeLine.intern; (*Start, goal*)
            mutable uuid             : Uuidm.t;
          }
        

          (*
           * Politique des évents :
                   * Entre chaque cycle, SMA stocke les events pour chaque agent (codé par leur UUID)
                   * A la fin de chaque cycle, les évènements sont distribués à tous les agents
                   * Le cycle général est lancé. Les évènement sont traités.
                   * A la fin du cycle de chaque nain, la pile est vidée*)


          (* Créer un agent avec agent d'état*)
          let create  () = { 

            currentState    = None;
            birthtime       = Unix.gettimeofday();
            now             = Unix.gettimeofday();
            pileEvents      = [];
            historique_etat = [];
            id              = 0;
            clockForState   = TimeLine.create();
            uuid            = Uuidm.create `V4;
          }



          let set_uuid self uuid       = self.uuid <- uuid
          let get_uuid self            = self.uuid



          let createState self nom      = let s = S.create nom in
                                          let _ = S.set_uuid s self.uuid in
                                          s

          let updateMainClock self      = self.now <- Unix.gettimeofday()


          

          let startClockForState self state goal = match state with (*Nombre de secondes *)
                                             | Some s -> TimeLine.addGoal self.clockForState (S.get_uuid s |> Uuidm.to_string)  goal
                                             | None   -> ()
          (*Renvoi vrai si on est APRÈS le goal*)
          let checkClockForState self state = pdebug "check clock"; match state with
                                             | Some s -> (try 
                                                                let sid = S.get_uuid s |> Uuidm.to_string in
                                                                let _   = sid  |> pdebug in
                                                                TimeLine.isReached self.clockForState sid 
                                                          with Not_found -> false)
                                             | None   -> false

          let startClockForCurState self goal   = startClockForState self self.currentState goal
          let checkClockForCurState self        = checkClockForState self self.currentState 


          let getCurrentState self = 
            let getCurrentStatewWithoutOption = function
              | None -> raise AucunEtatDisponiblePourLAgent (*TODO : à revoir ; mais normalement, on ne doit pas se servir de l'agent avant de lui avoir défini une HFSM*)
              | Some(st) -> st
            in getCurrentStatewWithoutOption self.currentState

          let getCurrentStateName self =
                  let st = getCurrentState self in
                  S.getNom st

         
          let getPileEvent self         = self.pileEvents

          let videPileEvent self        = self.pileEvents <- []


          let removeEmail self e        = (self.pileEvents <- (L.remove self.pileEvents (Some(e)));)


          let setPileEmail self e       = (self.pileEvents <- e;)


          let receiveEvent self e       = (self.pileEvents <- (Some(e)::self.pileEvents);) (*Recoit un event*)




          let getMail self e            =  print_string "RECUPERATION EMAILS" (*Récupère un Email à partir du module*)


          let setStartState self stat   = (self.currentState <- Some(S.chercheDernierFils stat);) 





                          (*état actuel (qui va changer)
                           * nouvel état dans lequel l'agent va se trouver
                           * Le père de l'état actuel (qui va changer) au niveau duquel on a changé d'état
                           * Le père du nouvel état par lequel on est venu ou nouvel état*)
          let setStateAg self nvstat pereCurrentOrigTransition pereNvState   =
            let intervAscendanceNvlEtat = S.ascendanceInterval nvstat (Some(pereNvState))
            in let getCurrentStateWithoutOption = function
              | None -> raise ErreurConstructionPileMessageInTestTransition
              | Some(st) -> st
               in let intervCurrentPereOrigTransition = S.ascendanceInterval (getCurrentStateWithoutOption self.currentState) (Some(pereCurrentOrigTransition))
                  in
                  let _ = TimeLine.addMarker self.clockForState (S.get_uuid nvstat |> Uuidm.to_string) in (*Nouvel état, on réinitialise le compteur*)
                  let _ = S.setStartTime nvstat in
                  (*   1.  On exécute tous les end_action de current au père responsable de la transition  *)
                  L.iter (fun elt -> S.executeEndAction elt ) intervCurrentPereOrigTransition;
                  (* 2.  On exécute tous les end_action du nouvel état à son
                     père cible de la transition *)
                  L.iter (fun elt -> S.executeBeginAction elt ) intervAscendanceNvlEtat;
                  (* 3.  On exécute le code de l'état !!*)
                  S.executeAction nvstat ;
                  self.currentState <- Some(nvstat);
          ;;


  

          let getNomEtatCourant self     = S.getNom (getCurrentState self)


          let cycle self  = (*Exécute un cycle
                              TODO : gérer le event_success à nettoyer à chaque cycle*)
            let current_state = getCurrentState self in
            let premierEvent = 
              try
                (getPileEvent self |> L.hd) (*TODO dangereux ! Et qd on gèrera le multi-event (père de degré plus haut prioritaire), prendre la liste*)
              with e -> None 
            in
            (*let _,s = Mixtbl.access() in
              let _   = let u = Uuidm.to_string self.uuid in pdebug ("set event:"^u) in
              let _   = s !(globalMemory.hEvents) self.uuid premierEvent in*)
            let _ = updateMainClock self in
            (*   1.    Cherche une transition pour current*)
            (*TODO : recup l'event qui a fait marcher la transition pour le supprimer de la liste*)
            let b,etatcourant,etatpereEtatActuel,etatPereNouvelEtat,nouvelEtat =  ( (S.chercheTransition current_state premierEvent) ) in
            (*   1a. Si aucune transition valide, on reste sur l'état et on réexécute l'état courant    *)
            match b with
              | false -> pdebug "ageEtat" ;
                              (*let ageEtat = TimeLine.age self.clockForState (S.get_uuid current_state |> Uuidm.to_string ) in (*On va chercher l'âge de l'état
                               * pour le donner à exécute action*)*)
                         pdebug "Aucune transition" ;
                         videPileEvent self;
                         pdebug "vidé";
                         S.executeAction current_state  
              | true  -> (*TODO 11/6 : démarrer un clock*)
                  let _ = TimeLine.addMarker self.clockForState (S.get_uuid nouvelEtat |> Uuidm.to_string ) in (*On défini, ou remet à 0*)
                  setStateAg self nouvelEtat etatpereEtatActuel etatPereNouvelEtat;    (*    1b. Sinon on appelle setState avec le nouvel état   *)
                  videPileEvent self;(* On vide la pile d'évènement, elle a été traité, elle est maintenant périmée
                                        Pour les cas limites où plusieurs états arrive en même temps, c'est un pb de discrétisation du temps.
                                        ie. La constante de temps de l'agent doit être assez fine pour qu'il prenne un agent à la fois.*)
                  pdebug ("[nom etat courrant après la transition] "^(S.getNom nouvelEtat))  (*    2. on vide de la liste les Email vieux de plus de 5s *)

  

         (*TODO : gérer, dans les transitions d'attentes les paramètres fonctions du temps. Ou par exemple les params fonction du temps écoulé depuis
           * le début de l'état
           * Ce serait pas mal d'avoir un param int -> unit, qui éxécute des trucs en fonction du nombre de secondes depuis le passage dans l'état
           * A la limite, on peut la coller dans le setAction, normalement, ça la déclenche à chaque cycle*)


         let waitTransition self ~from:fromState  ~tos:targetState ?action:(action=None)  ~wait:time  ~pere:pere () = 
                 (*1. C4est là qu'on se pose des question sur l'accès en mémoire de ce truc *)
                 let clockStartFun () = startClockForState self (Some(fromState)) time in
                 (match action with
                 | None -> ()
                 | Some a -> S.setAction fromState a);
                 S.setBeginAction fromState clockStartFun;
                 S.setParent targetState pere;
                 S.addTransition fromState targetState (Condition( fun i -> checkClockForState self (Some(fromState)) ))


          let creationTransitionSimplePreCurPost  ~from:fromState ~tos:nouvelEtat
                                                  ~conditionTransition:cond ~preAction:pre ~action:action ~postAction:post  ~pere:pere =
            S.setParent nouvelEtat pere;
            S.setBeginAction nouvelEtat pre;
            S.setAction nouvelEtat action;
            S.setEndAction nouvelEtat post;
            S.addTransition fromState nouvelEtat cond;;

          
          (*TODO : 10/6 : éviter le produit cartésien en tranformant les params d'actions en facultatifs*)

          let creationTransitionSimplePreCur  ~from:fromState  ~tos:nouvelEtat ~conditionTransition:cond ~preAction:pre ~action:action  ~pere:pere =
            S.setParent nouvelEtat pere;
            S.setBeginAction nouvelEtat pre;
            S.setAction nouvelEtat action;
            S.addTransition fromState nouvelEtat cond;;


          let creationTransitionSimplePre  ~from:fromState ~tos:nouvelEtat ~conditionTransition:cond ~preAction:pre  ~pere:pere =
            S.setParent nouvelEtat pere;
            S.setBeginAction nouvelEtat pre;
            S.addTransition fromState nouvelEtat cond;;

           let creationTransitionSimplePost  ~from:fromState ~tos:nouvelEtat ~conditionTransition:cond ~postAction:post  ~pere:pere =
            S.setParent nouvelEtat pere;
            S.setEndAction nouvelEtat post;
            S.addTransition fromState nouvelEtat cond;;




          let creationTransitionSimpleCurPost  ~from:fromState ~tos:nouvelEtat ~conditionTransition:cond ~action:action ~postAction:post  ~pere:pere =
            S.setParent nouvelEtat pere;
            S.setAction nouvelEtat action;
            S.setEndAction nouvelEtat post;
            S.addTransition fromState nouvelEtat cond;;


          let creationTransitionSimpleAction  ~from:fromState ~tos:nouvelEtat ~conditionTransition:cond ~action:action  ~pere:pere =
                  S.setParent fromState pere; (*TODO : revoir ça, le père doit être défini indépendament pour chaque état*)
                  S.setParent nouvelEtat pere;
                  S.setFils   pere fromState;
                  S.setFils   pere nouvelEtat;
                  S.setAction nouvelEtat action;
                  S.addTransition fromState nouvelEtat cond;;


          let creationTransitionSimple  ~from:fromState ~tos:destState ~conditionTransition:cond ~pere:pere =
            (*let _ = S.setNom destState nom in*)
            let _ = S.setParent destState pere in
            let _ = S.setParent fromState pere in
            S.addTransition fromState destState cond;;

          let printCurState self =  pdebug (getNomEtatCourant self)
end


(*

module type SMAType =
sig
        type event
        type agent_t
        type sma_t = {
          uuidArray             : Uuidm.t BatDynArray.t;
          last_cycle_duration   : float;
          last_cycle_time       : float;
          globalMemory          : globalMemoryType ref;
        }


        val create              : globalMemoryType -> sma_t
        val cycle_all           : sma_t -> unit
        val giveEventTo         : sma_t -> Uuidm.t -> event -> unit
        val addAgentToSMA       : sma_t -> agent_t -> unit
end

module SMA  (A : AgentType  ) : (SMAType  with  type event = A.event and type agent_t = A.agent_t) = struct
        (* La mixtbl se trouvera à l'extérieur, car on ne peut pas la typer
         * les UUID pour chaque agents
         * *)

          type event = A.event
          type agent_t = A.agent_t
          type sma_t = {
                  uuidArray             : Uuidm.t BatDynArray.t;
                  last_cycle_duration   : float;
                  last_cycle_time       : float;
                  globalMemory          : globalMemoryType ref;
          }

          let create globalMemo = {
                  uuidArray             = BatDynArray.create();
                  last_cycle_duration   = 0.;
                  last_cycle_time       = 0.;
                  globalMemory          = ref globalMemo;
          }

          let cycle_all self =
            BatDynArray.iter (fun e -> let g,_ = Mixtbl.access() in
                                       let agent = g !(!(self.globalMemory).hMain) e in
                                       match agent with
                                         | None   -> (Uuidm.to_string e)^" n'existe pas dans la MixTbl" |> print_endline ; ()
                                         | Some a -> a#cycle;
            )
              self.uuidArray



          let giveEventTo self uuidAgent event =
            let g,_ = Mixtbl.access() in
            let agent = g !(!(self.globalMemory).hMain) uuidAgent in
            match agent with
              | None   -> (Uuidm.to_string uuidAgent)^" n'existe pas dans la MixTbl" |> print_endline ; ()
              | Some a -> let ag = a#getAgent in
                          A.receiveEvent ag event(* C'est là qu'il va falloir lui donner le type de l'agent*)


          let addAgentToSMA self agent =
            let newUUID = Uuidm.create `V4 in
            let _ = BatDynArray.add self.uuidArray newUUID in
            let _,set = Mixtbl.access() in
            set !(!(self.globalMemory).hMain) newUUID agent               (*Add agent*)


end

*)

(* Questions *)

(*
 * 1. Comment gère t-on la pile d'évènement ?
 *  - Est-ce qu'on la vide à chaque cycle ?
 *  - Ou est-ce qu'on cherche ce qui nous intéresse et on laisse le reste un
 *  temps fixe ?
 *
 *
 *
 *
 *
 *
 *
 *
 *
 * *)



(*   4. Préparation du nouvel état   *)

(** Exemple d'utilisation :*)  
(*
 type event1 = Event1 | Event2;;
module E = struct type event = event1 end;;
module StateObj = State(E);;
module Ag = Agent(StateObj);;


class  objetSpaceChampion = object (self :'self)
 val mutable position        = (0,0)
 val mutable currentState    = Ag.create()
 method getPosition          = position
 
end;;*)
