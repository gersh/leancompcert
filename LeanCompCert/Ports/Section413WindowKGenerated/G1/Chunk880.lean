import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk880

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478325413197498, 362478442391074593⟩, ⟨587476342578676914, 594426852503106088⟩, true⟩

def state01 : KState := ⟨⟨362491226276876600, 362491343282174967⟩, ⟨(-547819876039306547), (-540866952901662425)⟩, true⟩

def words00 : List Nat := [371285197219252995, 371285197222663058, 371285197329142046, 371285197449205437, 371285197547669995, 371285197550735941, 371285197560363600, 371285197632347225, 371285197761966158, 371285197834981984]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 88000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 88000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362496305091855800, 362496422125096280⟩, ⟨(-994850971699623515), (-987895589233080241)⟩, true⟩

def words01 : List Nat := [371285197863574523, 371285197893096449, 371285198042820258, 371285198129357758, 371285198237320996, 371285198346495179, 371285198454611794, 371285198457731373, 371285198585855279, 371285198717168251]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 88010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 88000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485016468014987, 362485133528540744⟩, ⟨(-1153394652876484), 5804389606915340⟩, true⟩

def words02 : List Nat := [371285198913032887, 371285198994194542, 371285199057462432, 371285199121779611, 371285199192004318, 371285199210048378, 371285199293402266, 371285199377970293, 371285199461860442, 371285199465035200]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 88020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 88000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362493393003005960, 362493510091327378⟩, ⟨(-738579761693703655), (-731619530446821147)⟩, true⟩

def words03 : List Nat := [371285199574701470, 371285199686814183, 371285199846285373, 371285199849352084, 371285199837149076, 371285199805345540, 371285199866123518, 371285199910352395, 371285200006859287, 371285200104725150]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 88030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 88000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486096218822755, 362486213334818939⟩, ⟨(-96175536776275549), (-89212868901978835)⟩, true⟩

def words04 : List Nat := [371285200201420246, 371285200204487132, 371285200133206284, 371285200141028067, 371285200186825351, 371285200189952858, 371285200152585826, 371285200117122692, 371285200124400025, 371285200139410574]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 88040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 88000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362474870830873612, 362474987974481438⟩, ⟨892321279508992737, 899286378729381819⟩, true⟩

def words05 : List Nat := [371285200274084152, 371285200409975977, 371285200516848987, 371285200519916324, 371285200454755984, 371285200397042240, 371285200395830433, 371285200398897879, 371285200287493348, 371285200175012092]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 88050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 88000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486497882931463, 362486615053978563⟩, ⟨(-131573262186587092), (-124605746524693568)⟩, true⟩

def words06 : List Nat := [371285200061124840, 371285200064216121, 371285200086439785, 371285200158609272, 371285200215102034, 371285200218190837, 371285200158842252, 371285200131972510, 371285200201857898, 371285200221099129]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 88060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 88000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487577088925592, 362487694287962197⟩, ⟨(-226612999028551002), (-219643018192093080)⟩, true⟩

def words07 : List Nat := [371285200239476631, 371285200258916642, 371285200373615232, 371285200441552165, 371285200532548528, 371285200624678478, 371285200674733992, 371285200677803390, 371285200607707388, 371285200639863378]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 88070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 88000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478198225238707, 362478315451635047⟩, ⟨599510706005309699, 606483096826375167⟩, true⟩

def words08 : List Nat := [371285200723854017, 371285200726922504, 371285200639353373, 371285200553147225, 371285200465787233, 371285200407591396, 371285200291930384, 371285200282997718, 371285200272902592, 371285200263722985]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 88080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 88000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494374976186242, 362494492230268767⟩, ⟨(-825554561155644656), (-818579731314570798)⟩, true⟩

def words09 : List Nat := [371285200225916005, 371285200267856730, 371285200436950385, 371285200475178543, 371285200480596979, 371285200486973353, 371285200592713874, 371285200635386704, 371285200742948371, 371285200851835894]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 88090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 88000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 88000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk880
