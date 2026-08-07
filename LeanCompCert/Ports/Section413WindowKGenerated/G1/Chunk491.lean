import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk491

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362484727266822713, 362484762050922984⟩, ⟨9589390452023190, 10743260421013728⟩, true⟩

def state01 : KState := ⟨⟨362467834231640122, 362467869030500737⟩, ⟨839046731591731532, 840201326367774820⟩, true⟩

def words00 : List Nat := [371284980851370789, 371284980841757107, 371284980279518448, 371284980131683934, 371284979983014549, 371284979806722402, 371284979147715411, 371284978490629685, 371284977832920711, 371284977589376074]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 49100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 49100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362455317918365251, 362455352732000689⟩, ⟨1453875317003018955, 1455030637446690277⟩, true⟩

def words01 : List Nat := [371284977244963451, 371284977249625976, 371284977250865929, 371284977197840846, 371284976747660332, 371284976297424242, 371284975846377372, 371284975809114610, 371284975292435120, 371284974691232096]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 49110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 49100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362495194484145463, 362495229312435745⟩, ⟨(-505012491764142831), (-503856451399872177)⟩, true⟩

def words02 : List Nat := [371284974089302663, 371284973901317601, 371284973524117084, 371284973543326896, 371284973544595741, 371284973491353493, 371284973285799055, 371284973321982520, 371284973734685043, 371284973945123868]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 49120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 49100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492081197749863, 362492116040983710⟩, ⟨(-352035176512990709), (-350878401900190827)⟩, true⟩

def words03 : List Nat := [371284974139941948, 371284974335277895, 371284974704729688, 371284974917277367, 371284975231050031, 371284975545457645, 371284975775854801, 371284975777492693, 371284975656290368, 371284975803668634]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 49130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 49100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362467810061347571, 362467844919144558⟩, ⟨840835087210365343, 841992577533271295⟩, true⟩

def words04 : List Nat := [371284976322792511, 371284976324430297, 371284976292431145, 371284976262417350, 371284976328620280, 371284976330424702, 371284976220986904, 371284976154029273, 371284976086537108, 371284975999053679]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 49140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 49100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488880167374388, 362488915039993503⟩, ⟨(-194839973076666569), (-193681754171055407)⟩, true⟩

def words05 : List Nat := [371284975651627134, 371284975601002334, 371284975696621970, 371284975698288460, 371284975501532753, 371284975254979523, 371284975172079804, 371284975173901403, 371284975214010194, 371284975296005972]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 49150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 49100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487873795659987, 362487908683084334⟩, ⟨(-145462832793799061), (-144303885987602699)⟩, true⟩

def words06 : List Nat := [371284975297252355, 371284975294140020, 371284974816567305, 371284974709924647, 371284974622609612, 371284974624257522, 371284974340857796, 371284974052569379, 371284973885880919, 371284973947447728]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 49160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 49100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480328293759331, 362480363195905752⟩, ⟨225680681563559503, 226840352330907853⟩, true⟩

def words07 : List Nat := [371284974420634067, 371284974894455892, 371284975331759914, 371284975333401339, 371284975343308556, 371284975363357428, 371284975794854973, 371284975796494387, 371284975739116504, 371284975647152823]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 49170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 49100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478402551484848, 362478437468313252⟩, ⟨320452000472457009, 321612393375656501⟩, true⟩

def words08 : List Nat := [371284975554490696, 371284975550599142, 371284975609896147, 371284975823574917, 371284975977916387, 371284975979555850, 371284975583470728, 371284975542682397, 371284975632775427, 371284975634472546]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 49180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 49100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492552313638261, 362492587245436657⟩, ⟨(-375634743908935401), (-374473614559919575)⟩, true⟩

def words09 : List Nat := [371284975502787357, 371284975358488115, 371284975479450172, 371284975541983427, 371284975732392743, 371284975923437556, 371284976090870810, 371284976092515008, 371284975991052371, 371284976147805310]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 49190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 49100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 49100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk491
