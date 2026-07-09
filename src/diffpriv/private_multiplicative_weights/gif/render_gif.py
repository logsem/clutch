#!/usr/bin/python3

import csv
import matplotlib.pyplot as plt
from PIL import Image
import io

def max_l(l):
    a = 0
    for x in l:
        if a < x:
            a = x
    return a


if __name__ == "__main__":
    images = []
    
    with open("data/len.csv", "r") as flen:
        datalen = csv.reader(flen)
        nb_images = 0
        for row in datalen:
            nb_images = int(row[0])
        with open("data/gif0.csv", "r") as f0:
            data0 = csv.reader(f0)
            x0 = []
            y0 = []
            max_d = 0
            for row in data0:
                x0.append(row[0])
                y0.append(float(row[1]))
                if max_d < float(row[1]):
                    max_d = float(row[1])
            for i in range(nb_images):
                if i % int(nb_images / 100) == 0:
                    print(str(int(1000*i/nb_images)/10) + "%", "\r", end="")
                with open(f"data/gif{i+1}.csv", "r") as f:
                    data = csv.reader(f)
                    x = []
                    y = []
                    for row in data:
                        x.append(row[0])
                        y.append(float(row[1]))
                    fig, ax = plt.subplots()
                    ax.bar(x0, y0, color='yellow', alpha=0.8, label='DB')
                    ax.bar(x, y, color='cyan', alpha=0.5, label='sDB')
                    ax.set_ylim(0, max_d+max_d/10)
                    plt.legend(loc='upper left')
    
                    buf = io.BytesIO()
                    fig.savefig(buf, format='png')
                    buf.seek(0)
                    images.append(Image.open(buf))
                    plt.close()
    print("exporting")
    images[0].save('evolution_distrib.gif',
                   save_all=True, append_images=images[1:],
                   optimize=True, duration=15)
