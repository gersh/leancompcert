import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk059

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362685269513553167, 362685269930196557⟩, ⟨(-1217453172980080292), (-1217451507746268116)⟩, true⟩

def state01 : KState := ⟨⟨362537168450051012, 362537168868178546⟩, ⟨(-343147831287652955), (-343146157289794199)⟩, true⟩

def words00 : List Nat := [371278986800370623, 371278989919913267, 371279021710720957, 371279053490849224, 371279093842805756, 371279096060368929, 371279096060492737, 371279092941272029, 371279106912443334, 371279116735326272]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 5900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 5900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362406966544512146, 362406966964122737⟩, ⟨427434060461714645, 427435743231960999⟩, true⟩

def words01 : List Nat := [371279145895031896, 371279175044942222, 371279204688508815, 371279204688673443, 371279196312318693, 371279188369101818, 371279193095017686, 371279193095183544, 371279181145931259, 371279168947776785]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 5910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 5900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362496091243737058, 362496091664825131⟩, ⟨(-99567960750292554), (-99566269225845190)⟩, true⟩

def words02 : List Nat := [371279167508650143, 371279169587081933, 371279200096838086, 371279230596360685, 371279257326286136, 371279257326451058, 371279263478166131, 371279280748689029, 371279301400029595, 371279304231133369]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 5920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 5900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362525519084426082, 362525519507017754⟩, ⟨(-274077388968525525), (-274075688520191775)⟩, true⟩

def words03 : List Nat := [371279307433605707, 371279310635051397, 371279330667267671, 371279339500146584, 371279356933196585, 371279374360441876, 371279391549172253, 371279391549337516, 371279378818509409, 371279386585199846]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 5930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 5900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362374448909564921, 362374449333630522⟩, ⟨623859435004272107, 623861144215453835⟩, true⟩

def words04 : List Nat := [371279412778166434, 371279412778331770, 371279401329873618, 371279384847670889, 371279368370948994, 371279353571849268, 371279324914490839, 371279316437668530, 371279307963643143, 371279299946103708]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 5940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 5900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362501132383637795, 362501132809201194⟩, ⟨(-130307321384125588), (-130305603253411948)⟩, true⟩

def words05 : List Nat := [371279282327226609, 371279278550981694, 371279299126608818, 371279299126775187, 371279297290201346, 371279290764710933, 371279284241348192, 371279282095308663, 371279269452763353, 371279273120683595]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 5950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 5900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362443527185053112, 362443527612113717⟩, ⟨213001977688752340, 213003704750604530⟩, true⟩

def words06 : List Nat := [371279276516835959, 371279276517002872, 371279256155238453, 371279256723327226, 371279265772401490, 371279265772567878, 371279246903269327, 371279226208445261, 371279206624445797, 371279206624634757]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 5960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 5900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362357029117072043, 362357029545630466⟩, ⟨729991985622083402, 729993721633527068⟩, true⟩

def words07 : List Nat := [371279205927796920, 371279211204638486, 371279211522538312, 371279211522704830, 371279183108800034, 371279162300417923, 371279142682817938, 371279142682987205, 371279122491026069, 371279102074331725]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 5970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 5900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362570549703137805, 362570550133186404⟩, ⟨(-547418450069889560), (-547416705139581366)⟩, true⟩

def words08 : List Nat := [371279089105391503, 371279089105574675, 371279099351540051, 371279115862890773, 371279127454523640, 371279127454690400, 371279119191758030, 371279128959896760, 371279161701437986, 371279176955897207]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 5980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 5900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362451475653568713, 362451476085140535⟩, ⟨166960048117545325, 166961802179621285⟩, true⟩

def words09 : List Nat := [371279191960602862, 371279206960361620, 371279240124277344, 371279260132711538, 371279281364337745, 371279302588944520, 371279323591276661, 371279323591443665, 371279307690562994, 371279303052170472]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 5990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 5900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 5900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk059
