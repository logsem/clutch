import csv
import matplotlib.pyplot as plt
from PIL import Image
import io

images = []

nb_images = int (input ("nb_updates: "))


for i in range(nb_images):
    with open(f"data/0gif{i+1}.csv", "r") as f:
        data = csv.reader(f)
        x = []
        y = []
        for row in data:
            x.append(int(row[0]))
            y.append(float(row[1]))
        fig, ax = plt.subplots()
        ax.bar(x, y)
        
        buf = io.BytesIO()
        fig.savefig(buf, format='png')
        # Convert the BytesIO object to a PIL Image
        buf.seek(0)
        images.append(Image.open(buf))

images[0].save('evolution_distrib.gif',
               save_all = True, append_images = images[1:], 
               optimize = False, duration = 30)

#plt.savefig(f"output/0gif{i+1}.jpg")

