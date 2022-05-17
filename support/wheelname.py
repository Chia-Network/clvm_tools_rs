import os
import subprocess

wheels_files = os.listdir('target/wheels')
wheelname = list(filter(lambda x: x.endswith('whl') and 'musl' not in x, wheels_files))[0]
filename = "target/wheels/%s" % wheelname
print(filename)
subprocess.check_call(["pip", "install", filename])
