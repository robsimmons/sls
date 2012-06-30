(* Front End Interface *)
(* Author: Frank Pfenning *)


structure ReconConDec =
  ReconConDec (structure Global = Global
               structure Names = Names
               structure Abstract = Abstract
               structure ReconTerm' = ReconTerm
               structure Constraints = Constraints
               structure Strict = Strict
               structure TypeCheck = TypeCheck
               structure Timers = Timers
               structure Print = Print
	       structure Msg = Msg);
                                                        
