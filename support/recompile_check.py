import os
import subprocess
import traceback

recompile_list = [
    'block_program_zero.clsp',
    'calculate_synthetic_public_key.clsp',
    'chialisp_deserialisation.clsp',
    'decompress_coin_spend_entry.clsp',
    'decompress_coin_spend_entry_with_prefix.clsp',
    'decompress_puzzle.clsp',
    'delegated_tail.clsp',
    'did_innerpuz.clsp',
    'everything_with_signature.clsp',
    'genesis_by_coin_id.clsp',
    'genesis_by_puzzle_hash.clsp',
    'nft_metadata_updater_default.clsp',
    'nft_metadata_updater_updateable.clsp',
    'nft_ownership_layer.clsp',
    'nft_ownership_transfer_program_one_way_claim_with_royalties.clsp',
    'nft_state_layer.clsp',
    'p2_conditions.clsp',
    'p2_delegated_conditions.clsp',
    'p2_delegated_puzzle.clsp',
    'p2_delegated_puzzle_or_hidden_puzzle.clsp',
    'p2_m_of_n_delegate_direct.clsp',
    'p2_puzzle_hash.clsp',
    'p2_singleton.clsp',
    'p2_singleton_or_delayed_puzhash.clsp',
    'pool_member_innerpuz.clsp',
    'pool_waitingroom_innerpuz.clsp',
    'rom_bootstrap_generator.clsp',
    'settlement_payments.clsp',
    'sha256tree_module.clsp',
    'singleton_launcher.clsp',
    'singleton_top_layer.clsp',
    'singleton_top_layer_v1_1.clsp',
    'test_generator_deserialize.clsp',
    'test_multiple_generator_input_arguments.clsp'
]

for fname in recompile_list:
    hexfile = f'./chia/wallet/puzzles/{fname}.hex'
    hexdata = open(hexfile).read().strip()
    os.unlink(hexfile)
    try:
        compiled = subprocess.check_output(['../target/release/run', '-i', 'chia/wallet/puzzles/', f'chia/wallet/puzzles/{fname}']).strip()
        recompile = subprocess.check_output(['../target/release/opc', compiled]).decode('utf8').strip()
    except:
        print(f'compiling {fname}')
        traceback.print_exc()

    if hexdata != recompile:
        print(f'*** COMPILE RESULTED IN DIFFERENT OUTPUT FOR FILE {fname}')
        assert hexdata == recompile
