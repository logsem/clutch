#!/usr/bin/python3

from random import randint


if __name__ == "__main__":
    size = 1_000_000
    nb_o = 13
    
    with open("rd_data.csv", "w", encoding="utf-8") as f:
        for i in range(size):
            token = True
            count = 0
            while token and count < nb_o:
                if randint(0, 3) == 0:
                    f.write(str(count)+"\n")
                    token = False
                count += 1
            if token:
                f.write(str(nb_o)+"\n")

