BEGIN { FS = "\t" }
NR == 1 { for (i = 1; i <= NF; i++) h[$i] = i; next }
NF == 0 { next }
{
  n++
  origin[$h["origin"]]++
  if ($h["class"] != "") labeled++
  if ($h["inversion"] == "yes") inv++
  w = $h["witness"]
  if (w ~ /edited-equation|whole-definition|preserves-declared|preserves-wildcard/) rec++
}
END {
  printf "tasks\t%d\n", n
  printf "origin=neither\t%d\n", origin["neither"] + 0
  printf "origin=mutation\t%d\n", origin["mutation"] + 0
  printf "origin=human\t%d\n", origin["human"] + 0
  printf "origin=history\t%d\n", origin["history"] + 0
  printf "class_labeled\t%d\n", labeled + 0
  printf "inversion_witnessed\t%d\n", inv + 0
  printf "positive_recovery_witness\t%d\n", rec + 0
  printf "distance_to_30\t%d\n", (n >= 30 ? 0 : 30 - n)
}
