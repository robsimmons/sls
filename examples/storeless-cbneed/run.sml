CM.make "../../sources.cm";
fun HEADING s = print ("\n\n== "^s^" ==\n\n");
Frontend.init ();

HEADING "STORELESS CALL BY NEED";
Frontend.reset ();
Frontend.load "cbneed.sls";

Frontend.reset ();
Frontend.read "#defunctionalize \"cbneed-defun.auto.sls\" (cont frame : ord).";
Frontend.load "cbneed.auto.sls";
Frontend.read "#defunctionalize stop.";

Frontend.reset ();
Frontend.load "cbneed-ssos.0.sls";

Frontend.reset ();
Frontend.load "cbneed-ssos.1.sls";

Frontend.reset ();
Frontend.load "cbneed-ssos.2.sls";

Frontend.reset ();
Frontend.load "cbneed-ssos.3.sls";
