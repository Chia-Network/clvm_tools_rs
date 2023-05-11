;; Absorb for pool reward
(
  ;; Hash of pool puzzle
  0x9dcf97a184f32623d11a73124ceb99a5709b083721e878a16d78f596718ba7b2 ;; 1
  ;; Hash of singleton puzzle (here just skip the truths)
  0xc79b932e1e1da3c0e098e5ad2c422937eb904a76cf61d83975a74a68fbb04b99 ;; 3
  ;; Owner pubkey
  0xadc901ba437279de09ae97c2147f586f668001e88315920a92627c9083e449c0b21da6c1c864db9d7257dcdb9e389c5d
  ;; Pool reward prefix
  0x333333
  ;; Waiting room puzzlehash
  0x9dcf97a184f32623d11a73124ceb99a5709b083721e878a16d78f596718ba7b2 ;; 1
  ;; Truths
  (
    ("my_id_truth" . "my_full_puzzle_hash_truth")
    (
      0x9dcf97a184f32623d11a73124ceb99a5709b083721e878a16d78f596718ba7b2 ;; my_inner_puzzle_hash_truth
      .
      250000000000 ;; my_amount_truth
    )
  )
  ;; p1 - reward
  250000000000
  ;; reward height
  8472
)
