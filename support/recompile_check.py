import os
from pathlib import Path
import subprocess
import traceback

FULL_NODE='chia/full_node/puzzles'
CAT_WALLET='chia/wallet/cat_wallet/puzzles'
DID_WALLET='chia/wallet/did_wallet/puzzles'
NFT_WALLET='chia/wallet/nft_wallet/puzzles'
POOLS='chia/pools/puzzles'
CONSENSUS='chia/consensus/puzzles'
GENTEST='tests/generator/puzzles'

def full_node(x):
    return {'fname': x, 'dirname': FULL_NODE}

def cat_wallet(x):
    return {'fname': x, 'dirname': CAT_WALLET}

def did_wallet(x):
    return {'fname': x, 'dirname': DID_WALLET}

def nft_wallet(x):
    return {'fname': x, 'dirname': NFT_WALLET}

def pools(x):
    return {'fname': x, 'dirname': POOLS}

def consensus(x):
    return {'fname': x, 'dirname': CONSENSUS}

def gentest(x):
    return {'fname': x, 'dirname': GENTEST}

recompile_list = [
    full_node('block_program_zero.clsp'),
    full_node('decompress_coin_spend_entry.clsp'),
    full_node('decompress_coin_spend_entry_with_prefix.clsp'),
    full_node('decompress_puzzle.clsp'),
    cat_wallet('delegated_tail.clsp'),
    cat_wallet('everything_with_signature.clsp'),
    cat_wallet('genesis_by_coin_id.clsp'),
    cat_wallet('genesis_by_puzzle_hash.clsp'),
    did_wallet('did_innerpuz.clsp'),
    nft_wallet('nft_metadata_updater_default.clsp'),
    nft_wallet('nft_metadata_updater_updateable.clsp'),
    nft_wallet('nft_ownership_layer.clsp'),
    nft_wallet('nft_ownership_transfer_program_one_way_claim_with_royalties.clsp'),
    nft_wallet('nft_state_layer.clsp'),
    pools('pool_member_innerpuz.clsp'),
    pools('pool_waitingroom_innerpuz.clsp'),
    consensus('rom_bootstrap_generator.clsp'),
    'p2_conditions.clsp',
    'p2_delegated_conditions.clsp',
    'p2_delegated_puzzle.clsp',
    'p2_delegated_puzzle_or_hidden_puzzle.clsp',
    'p2_m_of_n_delegate_direct.clsp',
    'p2_puzzle_hash.clsp',
    'p2_singleton.clsp',
    'p2_singleton_or_delayed_puzhash.clsp',
    'settlement_payments.clsp',
    'singleton_launcher.clsp',
    'singleton_top_layer.clsp',
    'singleton_top_layer_v1_1.clsp',
    gentest('test_generator_deserialize.clsp'),
    gentest('test_multiple_generator_input_arguments.clsp')
]

for recompile_entry in recompile_list:
    if 'dirname' in recompile_entry and 'fname' in recompile_entry:
        dirname = recompile_entry['dirname']
        filename = recompile_entry['fname']
    else:
        filename = recompile_entry
        dirname = 'chia/wallet/puzzles'

    srcfile = str(Path(dirname) / Path(filename))
    hexfile = f'{str(srcfile)}.hex'
    hexdata = open(hexfile).read().strip()
    os.unlink(hexfile)
    try:
        compiled = subprocess.check_output(['../target/release/run', '-i', dirname, '-i', 'chia/wallet/puzzles', srcfile]).strip()
        recompile = subprocess.check_output(['../target/release/opc', compiled]).decode('utf8').strip()
    except:
        print(f'compiling {fname}')
        traceback.print_exc()

    if hexdata != recompile:
        print(f'*** COMPILE RESULTED IN DIFFERENT OUTPUT FOR FILE {fname}')
        assert hexdata == recompile
