from random import randint

size = 1_000_000
nb_o = 10

with open("rd_data.csv", "w", encoding="utf-8") as f:
    for i in range(size+1):
        f.write(str(randint(0, nb_o) % nb_o)+"\n")

