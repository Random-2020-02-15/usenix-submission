import os,zipfile
import sys

for i in os.listdir("./"):
    if os.path.isdir(i):
        for j in os.listdir("./"+i):
            if j == "Cov.zip":
                if os.path.exists("./"+i+"/Cov"):
                    os.system("rm -r "+"./"+i+"/Cov.zip")
                    os.system("zip -r "+"./"+i+"/Cov.zip "+"./"+i+"/Cov")
                    os.system("rm -r "+"./"+i+"/Cov")
                # else:
                #     os.system("unzip "+"./"+i+"/Cov.zip -d "+"./"+i)
                # for k in os.walk("./"+i+"/Cov/objects"):
                #     for l in range(len(k[2])):
                #         if k[2][l].endswith("ethz.o"):
                #             os.system("rm "+k[0]+"/"+k[2][l])
                
