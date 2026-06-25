import csv
import matplotlib.pyplot as plt
from PIL import Image
import io

images = []

nb_images = int (input ("nb_updates: "))


with open("data/0gif0.csv", "r") as f0:
    data0 = csv.reader(f0)
    x0 = []
    y0 = []
    for row in data0:
        x0.append(int(row[0]))
        y0.append(float(row[1]))
    for i in range(nb_images):
        with open(f"data/0gif{i+1}.csv", "r") as f:
            data = csv.reader(f)
            x = []
            y = []
            for row in data:
                x.append(int(row[0]))
                y.append(float(row[1]))
            fig, ax = plt.subplots()
            ax.bar(x0, y0, color='red', alpha=0.8)
            ax.bar(x, y, color='green', alpha=0.4)
            
            buf = io.BytesIO()
            fig.savefig(buf, format='png')
            # Convert the BytesIO object to a PIL Image
            buf.seek(0)
            images.append(Image.open(buf))
            plt.close()

images[0].save('evolution_distrib.gif',
               save_all = True, append_images = images[1:], 
               optimize = False, duration = 30)

#plt.savefig(f"output/0gif{i+1}.jpg")

