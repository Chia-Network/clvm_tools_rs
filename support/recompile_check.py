import os
import subprocess
import traceback

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
