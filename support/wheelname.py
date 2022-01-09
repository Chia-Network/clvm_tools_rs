import os

with open('usewheel.ps1', 'w') as f:
    wheels_files = os.listdir('target/wheels')
    wheelname = list(filter(lambda x: x.endswith('whl'), wheels_files))[0]
    f.write('$env:WHEEL_PATH="target/wheels/%s"\n' % wheelname)
