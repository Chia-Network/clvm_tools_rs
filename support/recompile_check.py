import os
import subprocess
import traceback
import binascii

recompile_list = [
    'block_program_zero.clvm',
    'calculate_synthetic_public_key.clvm',
    'chialisp_deserialisation.clvm',
    'decompress_coin_spend_entry.clvm',
    'decompress_coin_spend_entry_with_prefix.clvm',
    'decompress_puzzle.clvm',
    'delegated_tail.clvm',
    'did_innerpuz.clvm',
    'everything_with_signature.clvm',
    'generator_for_single_coin.clvm',
    'genesis_by_coin_id.clvm',
    'genesis_by_puzzle_hash.clvm',
    'lock.inner.puzzle.clvm',
    'nft_metadata_updater_default.clvm',
    'nft_metadata_updater_updateable.clvm',
    'nft_ownership_layer.clvm',
    'nft_ownership_transfer_program_one_way_claim_with_royalties.clvm',
    'nft_state_layer.clvm',
    'p2_conditions.clvm',
    'p2_delegated_conditions.clvm',
    'p2_delegated_puzzle.clvm',
    'p2_delegated_puzzle_or_hidden_puzzle.clvm',
    'p2_m_of_n_delegate_direct.clvm',
    'p2_puzzle_hash.clvm',
    'p2_singleton.clvm',
    'p2_singleton_or_delayed_puzhash.clvm',
    'pool_member_innerpuz.clvm',
    'pool_waitingroom_innerpuz.clvm',
    'rl_aggregation.clvm',
    'rl.clvm',
    'rom_bootstrap_generator.clvm',
    'settlement_payments.clvm',
    'sha256tree_module.clvm',
    'singleton_launcher.clvm',
    'singleton_top_layer.clvm',
    'singleton_top_layer_v1_1.clvm',
    'test_generator_deserialize.clvm',
    'test_multiple_generator_input_arguments.clvm'
]

def pad(n,v):
    if len(v) < n:
        return ('0' * (n - len(v))) + v
    else:
        return v

for fname in recompile_list:
    hexfile = f'./chia/wallet/puzzles/{fname}.hex'
    hexdata = open(hexfile).read().strip()
    try:
        compiled = subprocess.check_output(['../target/release/run', '-i', 'chia/wallet/puzzles/', f'chia/wallet/puzzles/{fname}']).strip()
        print('compiled', compiled)
        recompile = subprocess.check_output(['../target/release/opc', compiled]).decode('utf8').strip()
        print('recompile', recompile)
    except:
        print(f'compiling {fname}')
        traceback.print_exc()

    if hexdata != recompile:
        print(f'*** COMPILE RESULTED IN DIFFERENT OUTPUT FOR FILE {fname}')
        print(hexdata)
        print(recompile)
        hd = binascii.unhexlify(hexdata)
        rc = binascii.unhexlify(recompile)

        for (i,b) in enumerate(hd):
            if i < len(rc) and b != rc[i]:
                print(f'{pad(4,hex(i)[2:])}: new {pad(2,hex(b)[2:])} old {pad(2,hex(rc[i])[2:])}')
        assert hd == rc
