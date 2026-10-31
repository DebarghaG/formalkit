$c ( ) -> wff |- $.
$v p q $.
wp $f wff p $.
wq $f wff q $.
wi $a wff ( p -> q ) $.
${
  min $e |- p $.
  maj $e |- ( p -> q ) $.
  mp $a |- q $.
$}
${
  h1 $e |- p $.
  h2 $e |- ( p -> q ) $.
  $( The floating hypotheses are given in the wrong order. $)
  th $p |- q $= wq wp h1 h2 mp $.
$}
