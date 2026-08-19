\\ ShenLogic script launcher. Preserve argv before nested loads because Shen
\\ hosts may reset the script arguments while loading implementation modules.
\\
\\ `load` prints the value of every top-level form in Shen 41.2.  That is
\\ useful at a REPL but makes this program's stdout non-deterministic and
\\ corrupts machine-readable backend output.  Route the loader's chatter to a
\\ sink, restoring the real stream before dispatching the command.  Keep the
\\ stream in globals rather than relying on a host-specific dynamic binding.
(set *shenlogic-cli-argv* (value *argv*))
(set *shenlogic-cli-output* (stoutput))
(set *shenlogic-cli-sink* (open "/dev/null" out))
(set *stoutput* (value *shenlogic-cli-sink*))
(load "shenlogic.shen")
(load "shen/cli.shen")
(set *stoutput* (value *shenlogic-cli-output*))
(close (value *shenlogic-cli-sink*))
(shenlogic.cli.main (value *shenlogic-cli-argv*))
