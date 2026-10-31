/* A never claim describes BAD behaviour: here, x eventually becomes 2 and stays. */
byte x = 0;
active proctype A() { x = 1; x = 2 }
never { do :: x == 2 -> break :: else od; accept: do :: true od }
