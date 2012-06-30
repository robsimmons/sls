#| Independent processes |#

terminate: dest -> prop lin.

term/retn:  retn _ D * terminate D >-> {1}.
term/error: error _ D * terminate D >-> {1}.


#| Parallel evaluation, errors propogated eagerly |#

cont2: frame -> dest -> dest -> dest -> prop lin. 

ev/letpar:  eval (letpar E1 E2 \x. \y. E x y) D
             >-> {Exists d1. eval E1 d1 *
                  Exists d2. eval E2 d2 * 
                  cont2 (letpar1 \x. \y. E x y) d1 d2 D}.

ev/letpar1: retn V1 D1 * retn V2 D2 *
            cont2 (letpar1 \x. \y. E x y) d1 d2 D
             >-> {eval (E V1 V2) D}.

ev/errorL:  error V D1 * cont2 D1 D2 D 
             >-> {error V D * terminate D2}.

ev/errorR:  error V D2 * cont2 D1 D2 D
             >-> {error V D * terminate D1}.


#| Concurrent ML primitives that use concurrency |#

synch: exp -> dest -> prop lin. 

ev/spawn:   eval (spawn E) D 
             >-> {retn unit D *
                  Exists d'. eval E d' * terminate d'}.

ev/newch:   eval newch D >-> {Exists c. retn (chan c) D}.

ev/sync:    eval (sync E1) D
             >-> {Exists d1. eval E1 d1 * cont sync1 d1 D}.

ev/sync1:   retn W D1 * cont sync1 D >-> {synch W D}.


#| Synchronization in Concurrent ML |#

action: exp -> exp -> (exp -> exp) -> prop.

act/t: action (always V) (always V) (\x. x).
act/!: action (send (chan C) V) (send (chan C) V) (\x. x).
act/?: action (recv (chan C)) (recv (chan C)) (\x. x).
act/l: action (choose Event1 Event2) V (\x. E x)
        <- action Event1 Lab (\x. E x).
act/r: action (choose V1 V2) Lab (\x. E x)
        <- action Event2 Lab (\x. E x).
act/w: action (wrap Event1 \x. E2 x) Lab (\x. app (lam (\x. E2 x)) (E x))
        <- action Event1 Lab (\x. E x). 

synch/always: 
  synch Event D *  
  !action Event (always V') (\x. E x)
   >-> {eval (E V') D}.

synch/communicate:   
  synch Event1 D1 * 
  !action Event1 (send (chan C) V) (\x. E1 x) *
  synch Event2 D2 * 
  !action Event2 (send (chan C) V) (\x. E2 x) 
   >-> {eval (E1 unit) D1 * eval (E2 V) D2}.