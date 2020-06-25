# This is the source for the proof of close_computation_from_gappa
@rnd = float< ieee_32, ne >;
{s in [1, 2] /\ e in [-32b-23,3] ->
 ( rnd (rnd ( (s + e) + rnd ((s * s) / (s + e))) / 2)
   -
   ( ((s + e) + ((s * s) / (s + e))) / 2)

    ) in [-5b-24,5b-24]}

