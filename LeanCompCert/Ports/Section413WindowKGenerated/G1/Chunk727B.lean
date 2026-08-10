import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk727A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk727B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk727A

def state06 : KState := ⟨⟨362480353253728685, 362480432058191095⟩, ⟨349196941305074445, 353069184040090317⟩, true⟩

def words05 : List Nat := [371285284755384539, 371285284804021077, 371285284852476004, 371285284854991129, 371285284733907759, 371285284671434013, 371285284700196510, 371285284702738395, 371285284639694420, 371285284575838705]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 72750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 72700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489733558783914, 362489812385597205⟩, ⟨(-333350317446174276), (-329476448347873208)⟩, true⟩

def words06 : List Nat := [371285284531374899, 371285284534128511, 371285284599794905, 371285284728799959, 371285284787288866, 371285284789787487, 371285284596385386, 371285284592968017, 371285284741829543, 371285284806639271]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 72760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 72700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480966795995959, 362481045645580951⟩, ⟨304710530149746332, 308586056459357796⟩, true⟩

def words07 : List Nat := [371285284867328234, 371285284928887734, 371285285150416807, 371285285301589928, 371285285472864861, 371285285645130209, 371285285789671797, 371285285792170832, 371285285685059662, 371285285629868659]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 72770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 72700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472313063435560, 362472391935272099⟩, ⟨934601003186782403, 938478149081045595⟩, true⟩

def words08 : List Nat := [371285285683526730, 371285285686026074, 371285285564785425, 371285285443271351, 371285285320770328, 371285285256697928, 371285285124110289, 371285285048778062, 371285284972628427, 371285284889648814]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 72780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 72700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493397949972387, 362493476844485403⟩, ⟨(-600286829436207877), (-596408032813022803)⟩, true⟩

def words09 : List Nat := [371285284714221491, 371285284710480511, 371285284777795786, 371285284780302387, 371285284660820817, 371285284495952489, 371285284351024368, 371285284353797829, 371285284423540739, 371285284538983927]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 72790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 72700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 72700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk727B
