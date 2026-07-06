from random import randint

size = 1_000_000
nb_o = 10



with open("rd_data.csv", "w", encoding="utf-8") as f:
    for i in range(size):
        token = True
        count = 0
        while token and count <= 12:
            if randint(0, 3) == 0:
                f.write(str(count)+"\n")
                token = False
            count += 1


#        if randint(0, 3) == 0:
#            f.write(str(0)+"\n")
#        elif randint(0, 3) == 0:
#            f.write(str(1)+"\n")
#        elif randint(0, 3) == 0:
#            f.write(str(2)+"\n")
#        elif randint(0, 3) == 0:
#            f.write(str(3)+"\n")
#        elif randint(0, 3) == 0:
#            f.write(str(4)+"\n")
#        elif randint(0, 3) == 0:
#            f.write(str(5)+"\n")
#        elif randint(0, 3) == 0:
#            f.write(str(6)+"\n")
#        elif randint(0, 3) == 0:
#            f.write(str(7)+"\n")
#        elif randint(0, 3) == 0:
#            f.write(str(8)+"\n")
#        elif randint(0, 3) == 0:
#            f.write(str(9)+"\n")
#        elif randint(0, 3) == 0:
#            f.write(str(10)+"\n")
#        elif randint(0, 3) == 0:
#            f.write(str(10)+"\n")


