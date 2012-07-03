CM.make "../../sources.cm";
fun HEADING s = print ("\n\n== "^s^" ==\n\n");
Frontend.init ();

HEADING "NATURAL SEMANTICS";
Frontend.reset ();
Frontend.load "types.sls";
Frontend.read "#operationalize \"natsem.auto.sls\" (ev ~> eval retn).";
Frontend.load "pure-natsem.sls";
Frontend.load "concur-natsem.sls";
Frontend.read "#operationalize stop.";

HEADING "ORDERED ABSTRACT MACHINES (nested)";
Frontend.reset ();
Frontend.load "types.sls";
Frontend.read "#defunctionalize \"ord-nested.auto.sls\" (cont frame : ord).";
Frontend.load "natsem.auto.sls";
Frontend.load "imp-ordmachine.sls";
Frontend.read "#defunctionalize stop.";

HEADING "ORDERED ABSTRACT MACHINES (flat)";
Frontend.reset ();
Frontend.load "types.sls";
Frontend.load "ord-nested.auto.sls";
Frontend.load "control-ordmachine.sls";

HEADING "DESTINATION-PASSING";
Frontend.reset ();
