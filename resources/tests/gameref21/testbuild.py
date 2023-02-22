import traceback
from steprun import compile_module_with_symbols

programs = [
    'rockpaperscissorsd.clsp',
    'rockpaperscissorsc.clsp',
    'rockpaperscissorsb.clsp',
    'rockpaperscissorsa.clsp',
    'referee_accuse.clsp',
    'referee.clsp'
]

for p in programs:
    print(p)
    try:
        compile_module_with_symbols(['.'],p)
    except:
        print(f'error compiling {p}')
        traceback.print_exc()
