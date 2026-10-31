/* The LTL property holds, but the process blocks forever on the channel:
   safety (invalid end states) is always checked too. Label intended waits with end:. */
chan c = [0] of {bit};
byte x = 0;
active proctype A() { x = 1; c?1 }
ltl bounded { [] (x <= 1) }
