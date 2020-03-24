# This is the source for the proof of close_computation_from_gappa
@rnd = float< ieee_32, ne >;
{b in [1, 2] /\ e in [-16b-23,3] ->
 ( rnd (rnd ( (b + e) + rnd ((b * b) / (b + e))) / 2)
   -
   ( ((b + e) + ((b * b) / (b + e))) / 2)

    ) in [-9b-24,9b-24]}

