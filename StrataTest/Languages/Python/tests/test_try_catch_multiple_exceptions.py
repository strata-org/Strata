branch = 0
value = 4
intlist = [1, 2, 3, 4, 5]

try:
    sum = 10 + value
    elem = intlist[value]

except IndexError as e:
    branch = 1

except TypeError as e:
    branch = 2

except Exception as e:
    branch = 3

assert branch == 0

try:
    sum = "abc" + value
    elem = intlist[value]

except ZeroDivisionError:
    branch = 1

except IndexError as e:
    branch = 2

except TypeError as e:
    branch = 3

except Exception as e:
    branch = 4


assert branch == 3

try:
    sum = "abc" + value
    elem = intlist[value]

except IndexError as e:
    branch = 1

