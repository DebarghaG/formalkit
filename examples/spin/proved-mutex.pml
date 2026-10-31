/* Peterson's mutual exclusion for two processes. */
bool flag[2];
byte turn;
byte critical = 0;

active [2] proctype P() {
  byte me = _pid;
  do
  :: flag[me] = true;
     turn = 1 - me;
     (flag[1 - me] == false || turn == me);
     critical++;
     critical--;
     flag[me] = false
  od
}

ltl mutex { [] (critical <= 1) }
