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
Frontend.load "natsem.auto.sls";
Frontend.load "imp-ordmachine.sls";

HEADING "ORDERED ABSTRACT MACHINES (flat)";

HEADING "DESTINATION-PASSING";
