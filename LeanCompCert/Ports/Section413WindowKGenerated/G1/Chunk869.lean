import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk869

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488979942188964, 362489093903242061⟩, ⟨(-345110926185557184), (-338424241476507802)⟩, true⟩

def state01 : KState := ⟨⟨362476526483386310, 362476640471682933⟩, ⟨737110134308279413, 743799186618630245⟩, true⟩

def words00 : List Nat := [371285199581946556, 371285199584970395, 371285199452353714, 371285199415078903, 371285199376284867, 371285199340543432, 371285199166905932, 371285198985225400, 371285198802345279, 371285198741003134]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 86900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 86900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362463781688115515, 362463895703703396⟩, ⟨1844851584993660262, 1851543009324257386⟩, true⟩

def words01 : List Nat := [371285198644596275, 371285198617578561, 371285198589464792, 371285198540399011, 371285198314044657, 371285198129696049, 371285197943818969, 371285197853936766, 371285197636667889, 371285197395020979]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 86910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 86900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483039734961619, 362483153777622939⟩, ⟨170860866936569607, 177554644629687439⟩, true⟩

def words02 : List Nat := [371285197152007994, 371285196994139457, 371285196788851047, 371285196716979401, 371285196644200484, 371285196553345784, 371285196351886331, 371285196284237760, 371285196275867821, 371285196278999101]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 86920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 86900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362481935558570355, 362482049628815990⟩, ⟨266836369680025931, 273532545412785543⟩, true⟩

def words03 : List Nat := [371285196257796305, 371285196237040469, 371285196215130945, 371285196211102975, 371285196139745764, 371285196110081808, 371285196079369546, 371285196049546577, 371285195883236516, 371285195850870428]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 86930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 86900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477130887404275, 362477244984584771⟩, ⟨684602141596349037, 691300659181858905⟩, true⟩

def words04 : List Nat := [371285195897209247, 371285195900236952, 371285195839270482, 371285195779059076, 371285195717601233, 371285195697864150, 371285195616294824, 371285195590673441, 371285195564079279, 371285195538456903]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 86940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 86900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362498739131708557, 362498853256259174⟩, ⟨(-1194332565681231166), (-1187631668122449886)⟩, true⟩

def words05 : List Nat := [371285195489765792, 371285195534107147, 371285195692530251, 371285195742196806, 371285195747827303, 371285195754348514, 371285195847504882, 371285195875818666, 371285196034923992, 371285196195414400]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 86950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 86900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489633661354759, 362489747813228337⟩, ⟨(-402553108741196031), (-395849835037023655)⟩, true⟩

def words06 : List Nat := [371285196312096616, 371285196315122361, 371285196259867990, 371285196267957499, 371285196315072716, 371285196318120346, 371285196267277223, 371285196216437581, 371285196242149497, 371285196297952705]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 86960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 86900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474287220787039, 362474401399864604⟩, ⟨932250586299720004, 938956226072354508⟩, true⟩

def words07 : List Nat := [371285196451342664, 371285196605940885, 371285196753696048, 371285196756722501, 371285196728231809, 371285196704279227, 371285196719009669, 371285196722036296, 371285196602531614, 371285196481792316]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 86970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 86900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481764648464424, 362481878854667205⟩, ⟨281900530256408737, 288608529518561251⟩, true⟩

def words08 : List Nat := [371285196367670197, 371285196371071440, 371285196409670010, 371285196475147937, 371285196518557776, 371285196521592136, 371285196487150120, 371285196524053495, 371285196572300161, 371285196575434174]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 86980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 86900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479862341604641, 362479976575421199⟩, ⟨447429447205600396, 454139848725125638⟩, true⟩

def words09 : List Nat := [371285196539558332, 371285196501456211, 371285196552660872, 371285196583249738, 371285196640738961, 371285196699432141, 371285196751275566, 371285196754303128, 371285196629896276, 371285196573682408]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 86990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 86900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 86900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk869
