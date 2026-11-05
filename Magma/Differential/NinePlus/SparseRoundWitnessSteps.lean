module
import all Init.Data.Range.Basic
public import Magma.Differential.FiveRounds.FiveRoundCoreDefect

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

@[expose] public section

namespace Magma.DiffanSparseRoundSteps

open Magma
open Magma.MultiRoundDDT
open Magma.DiffanFiveRoundCoreDefect

private theorem w0_base_step0 :
    G (0x00000000#32) (0x9d651eb2#32, 0x17714960#32) = (0x17714960#32, 0xe3effd57#32) := by
  decide +kernel

private theorem w0_base_step1 :
    G (0xb3900250#32) (0x17714960#32, 0xe3effd57#32) = (0xe3effd57#32, 0x72f30685#32) := by
  decide +kernel

private theorem w0_base_step2 :
    G (0xddfc38c3#32) (0xe3effd57#32, 0x72f30685#32) = (0x72f30685#32, 0x836b0f90#32) := by
  decide +kernel

private theorem w0_base_step3 :
    G (0xca24f050#32) (0x72f30685#32, 0x836b0f90#32) = (0x836b0f90#32, 0x977366d0#32) := by
  decide +kernel

private theorem w0_base_step4 :
    G (0x00000000#32) (0x836b0f90#32, 0x977366d0#32) = (0x977366d0#32, 0xd4bde875#32) := by
  decide +kernel

theorem w0_base_five :
    iterateG 5
        (fiveRoundKeys (0x00000000#32) (0xb3900250#32) (0xddfc38c3#32) (0xca24f050#32)
          (0x00000000#32))
        (0x9d651eb2#32, 0x17714960#32) =
      (0x977366d0#32, 0xd4bde875#32) := by
  change
    G (0x00000000#32)
        (G (0xca24f050#32)
          (G (0xddfc38c3#32)
            (G (0xb3900250#32) (G (0x00000000#32) ((0x9d651eb2#32, 0x17714960#32)))))) =
      (0x977366d0#32, 0xd4bde875#32)
  rw [w0_base_step0, w0_base_step1, w0_base_step2, w0_base_step3, w0_base_step4]

private theorem w0_xor_step0 :
    G (0x00000000#32) (0x1d651e32#32, 0x17714960#32) = (0x17714960#32, 0x63effdd7#32) := by
  decide +kernel

private theorem w0_xor_step1 :
    G (0xb3900250#32) (0x17714960#32, 0x63effdd7#32) = (0x63effdd7#32, 0xa9280285#32) := by
  decide +kernel

private theorem w0_xor_step2 :
    G (0xddfc38c3#32) (0x63effdd7#32, 0xa9280285#32) = (0xa9280285#32, 0xa34b0fb0#32) := by
  decide +kernel

private theorem w0_xor_step3 :
    G (0xca24f050#32) (0xa9280285#32, 0xa34b0fb0#32) = (0xa34b0fb0#32, 0x977366d0#32) := by
  decide +kernel

private theorem w0_xor_step4 :
    G (0x00000000#32) (0xa34b0fb0#32, 0x977366d0#32) = (0x977366d0#32, 0xf49de855#32) := by
  decide +kernel

theorem w0_xor_five :
    iterateG 5
        (fiveRoundKeys (0x00000000#32) (0xb3900250#32) (0xddfc38c3#32) (0xca24f050#32)
          (0x00000000#32))
        (0x1d651e32#32, 0x17714960#32) =
      (0x977366d0#32, 0xf49de855#32) := by
  change
    G (0x00000000#32)
        (G (0xca24f050#32)
          (G (0xddfc38c3#32)
            (G (0xb3900250#32) (G (0x00000000#32) ((0x1d651e32#32, 0x17714960#32)))))) =
      (0x977366d0#32, 0xf49de855#32)
  rw [w0_xor_step0, w0_xor_step1, w0_xor_step2, w0_xor_step3, w0_xor_step4]

private theorem w1_base_step0 :
    G (0x00000000#32) (0x5ecd63c0#32, 0xc5b62afe#32) = (0xc5b62afe#32, 0xeff29f08#32) := by
  decide +kernel

private theorem w1_base_step1 :
    G (0x298d60a0#32) (0xc5b62afe#32, 0xeff29f08#32) = (0xeff29f08#32, 0xa034595b#32) := by
  decide +kernel

private theorem w1_base_step2 :
    G (0xe12d7fef#32) (0xeff29f08#32, 0xa034595b#32) = (0xa034595b#32, 0x90fe757e#32) := by
  decide +kernel

private theorem w1_base_step3 :
    G (0xae618a91#32) (0xa034595b#32, 0x90fe757e#32) = (0x90fe757e#32, 0x9e6f57e5#32) := by
  decide +kernel

private theorem w1_base_step4 :
    G (0x00000000#32) (0x90fe757e#32, 0x9e6f57e5#32) = (0x9e6f57e5#32, 0xf2965ae0#32) := by
  decide +kernel

theorem w1_base_five :
    iterateG 5
        (fiveRoundKeys (0x00000000#32) (0x298d60a0#32) (0xe12d7fef#32) (0xae618a91#32)
          (0x00000000#32))
        (0x5ecd63c0#32, 0xc5b62afe#32) =
      (0x9e6f57e5#32, 0xf2965ae0#32) := by
  change
    G (0x00000000#32)
        (G (0xae618a91#32)
          (G (0xe12d7fef#32)
            (G (0x298d60a0#32) (G (0x00000000#32) ((0x5ecd63c0#32, 0xc5b62afe#32)))))) =
      (0x9e6f57e5#32, 0xf2965ae0#32)
  rw [w1_base_step0, w1_base_step1, w1_base_step2, w1_base_step3, w1_base_step4]

private theorem w1_xor_step0 :
    G (0x00000000#32) (0xdecd6340#32, 0xc5b62afe#32) = (0xc5b62afe#32, 0x6ff29f88#32) := by
  decide +kernel

private theorem w1_xor_step1 :
    G (0x298d60a0#32) (0xc5b62afe#32, 0x6ff29f88#32) = (0x6ff29f88#32, 0x7bef5d5b#32) := by
  decide +kernel

private theorem w1_xor_step2 :
    G (0xe12d7fef#32) (0x6ff29f88#32, 0x7bef5d5b#32) = (0x7bef5d5b#32, 0xb0be755e#32) := by
  decide +kernel

private theorem w1_xor_step3 :
    G (0xae618a91#32) (0x7bef5d5b#32, 0xb0be755e#32) = (0xb0be755e#32, 0x9e6f57e5#32) := by
  decide +kernel

private theorem w1_xor_step4 :
    G (0x00000000#32) (0xb0be755e#32, 0x9e6f57e5#32) = (0x9e6f57e5#32, 0xd2d65ac0#32) := by
  decide +kernel

theorem w1_xor_five :
    iterateG 5
        (fiveRoundKeys (0x00000000#32) (0x298d60a0#32) (0xe12d7fef#32) (0xae618a91#32)
          (0x00000000#32))
        (0xdecd6340#32, 0xc5b62afe#32) =
      (0x9e6f57e5#32, 0xd2d65ac0#32) := by
  change
    G (0x00000000#32)
        (G (0xae618a91#32)
          (G (0xe12d7fef#32)
            (G (0x298d60a0#32) (G (0x00000000#32) ((0xdecd6340#32, 0xc5b62afe#32)))))) =
      (0x9e6f57e5#32, 0xd2d65ac0#32)
  rw [w1_xor_step0, w1_xor_step1, w1_xor_step2, w1_xor_step3, w1_xor_step4]

end Magma.DiffanSparseRoundSteps
