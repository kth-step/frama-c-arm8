from os import system
import os
import time
folder = "stats/"
dir_list = sorted(os.listdir(folder))

total = 0
hol_error = 0
translate_error = 0

translation_time = 0
hol_time = 0
no_error = 0

for file_name in dir_list:
    if not file_name.endswith(".txt"):
        continue
    file = open(folder + file_name, "r")
    [t0,t1,s0,s1] = file.read().split()
    (t0,t1,s0,s1) = (float(t0),float(t1),int(s0),int(s1))
    total += 1
    if s1 != -1 and s1 != 0:
        print(file_name)

    if s1 != -1 and s1 != 0:
        hol_error += 1
    if s0 != -1 and s0 != 0:
        translate_error += 1
    
    if s0 == 0 and s1 == 0:
        no_error += 1
        translation_time += t0
        hol_time += t1

avg_translation_time = translation_time / no_error
avg_hol_time = hol_time / no_error

print("translate_error =", translate_error, "hol_error =", hol_error, "total =", total, "avg_translation_time =", avg_translation_time, "avg_hol_time =", avg_hol_time)