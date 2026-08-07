import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk309

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362474800624900746, 362474813888101022⟩, ⟨327894789234511477, 328171808450017725⟩, true⟩

def state01 : KState := ⟨⟨362456182474983024, 362456195747021058⟩, ⟨903263704499837312, 903540996848720334⟩, true⟩

def words00 : List Nat := [371285434339648104, 371285434340641218, 371285433295618745, 371285432255628482, 371285431215329638, 371285430218652373, 371285428788169581, 371285428222615084, 371285427656771860, 371285427095997077]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 30900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 30900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362507618774447278, 362507632055486250⟩, ⟨(-686790864827845201), (-686513294215989027)⟩, true⟩

def words01 : List Nat := [371285426248703371, 371285426347614786, 371285427224393143, 371285427400360722, 371285427401137716, 371285427365116981, 371285428150222400, 371285428447665499, 371285429166450690, 371285429885627061]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 30910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 30900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482335618934304, 362482348908936104⟩, ⟨94919970022057099, 95197817811618969⟩, true⟩

def words02 : List Nat := [371285430381087984, 371285430382081760, 371285429485900441, 371285429188190937, 371285428906136790, 371285428907148012, 371285428172399604, 371285427383798203, 371285426755130030, 371285426756262701]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 30920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 30900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362465497060075112, 362465510359033239⟩, ⟨615937839929376292, 616215964783056782⟩, true⟩

def words03 : List Nat := [371285427599713700, 371285428543014886, 371285429297513987, 371285429298508059, 371285428662434787, 371285428138661086, 371285428130951908, 371285428131946843, 371285427484011235, 371285426841411490]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 30930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 30900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362465690309994272, 362465703617842097⟩, ⟨610042232250016026, 610320632197103058⟩, true⟩

def words04 : List Nat := [371285426595990425, 371285426597096888, 371285426603604386, 371285426715829283, 371285426716598989, 371285426653054196, 371285425199664705, 371285424181645109, 371285423184895552, 371285423185926010]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 30940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 30900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362471975764684783, 362471989081618721⟩, ⟨415506408931686046, 415785090138203232⟩, true⟩

def words05 : List Nat := [371285422549556292, 371285421898461822, 371285421286014744, 371285421287136834, 371285421063351077, 371285420965524630, 371285420867380221, 371285420625237868, 371285419265127119, 371285418832592178]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 30950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 30900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362447487640662767, 362447500966469123⟩, ⟨1173759945780672926, 1174038901723075230⟩, true⟩

def words06 : List Nat := [371285418400357663, 371285418401352965, 371285417173798973, 371285415951393542, 371285414728700498, 371285413522935116, 371285411935068272, 371285411275855995, 371285410616331880, 371285409875146007]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 30960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 30900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362502309772781025, 362502323107576221⟩, ⟨(-524307445982243138), (-524028211610449590)⟩, true⟩

def words07 : List Nat := [371285408651808953, 371285408468313946, 371285408985780792, 371285408986779243, 371285408627891717, 371285407957771944, 371285407655035033, 371285407656141917, 371285408057674556, 371285408604764484]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 30970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 30900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362465965863077851, 362465979206857102⟩, ⟨601847499953173510, 602127012698289204⟩, true⟩

def words08 : List Nat := [371285409075322096, 371285409076335225, 371285409326484268, 371285409971685951, 371285410933342907, 371285410934338973, 371285410510086225, 371285409901361823, 371285409292294467, 371285408926531136]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 30980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 30900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362452407271997486, 362452420624763488⟩, ⟨1022165175326793268, 1022444966615744328⟩, true⟩

def words09 : List Nat := [371285408330574128, 371285408361982757, 371285408398256880, 371285408399253259, 371285407050329288, 371285406019424090, 371285404988048699, 371285404852115350, 371285403783303921, 371285402720460771]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 30990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 30900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 30900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk309
