/* No turn variable: both processes can enter the critical section. */
bool flag[2];
byte critical = 0;

active [2] proctype P() {
  byte me = _pid;
  do
  :: (flag[1 - me] == false);
     flag[me] = true;
     critical++;
     critical--;
     flag[me] = false
  od
}

ltl mutex { [] (critical <= 1) }
