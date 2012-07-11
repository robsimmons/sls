CM.make "../../sources.cm";
fun HEADING s = print ("\n\n== "^s^" ==\n\n");
Frontend.init ();

HEADING "ADDITION: BACKWARDS CHAINING";
Frontend.reset ();
Frontend.load "nat.sls";
Frontend.load "plus.sls";

HEADING "ADDITION: FORWARD CHAINING";
Frontend.reset ();
Frontend.load "nat.sls";
Frontend.read "#defunctionalize \"plus-defun.auto.sls\" (cont frame : ord).";
Frontend.load "plus.auto.sls";
Frontend.read "#defunctionalize stop.";
