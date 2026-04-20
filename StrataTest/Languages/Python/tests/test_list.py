numbers = [10, 20, 30, 40, 50]

assert 40 in numbers 

n = numbers[2]

assert n == 30

assert numbers[-2] == 40

assert numbers[-5] == 10

numbers[-1] = 99 

assert numbers[-1] == 99 

words = ["apple", "pencil", "wood"]

sumlist = numbers + words 

assert sumlist[6] == "pencil"

sumlist[1] = 5 

assert sumlist[1] + sumlist[2] == 35
