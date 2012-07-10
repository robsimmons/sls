CM.make "../../sources.cm";
fun HEADING s = print ("\n\n== "^s^" ==\n\n");
Frontend.init ();

HEADING "Natural semantics";
Frontend.reset ();
Frontend.load "exp.sls";
Frontend.load "ev.sls";

HEADING "Nested ordered abstract machine";
Frontend.reset ();
Frontend.load "exp.sls";
Frontend.read "#defunctionalize \"ev-defun.auto.sls\" (cont frame : ord).";
Frontend.load "ev.auto.sls";
Frontend.read "#defunctionalize stop.";

HEADING "Flat ordered abstract machine";
Frontend.reset ();
Frontend.load "exp.sls";
Frontend.load "ev-defun.auto.sls";
