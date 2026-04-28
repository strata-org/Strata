# Test: If/else, undef at join points

cond: bool = True

# Both branches assign
if cond:
    x = 1
else:
    x = 2
use_x = x

# Only one branch assigns (undef on else path)
if cond:
    y = 10
use_y = y  # NameError if cond is False

# Elif chain
if cond:
    z = "a"
elif not cond:
    z = "b"
else:
    z = "c"
