import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk329

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362498211187812600, 362498226302172168⟩, ⟨(-444411191314713649), (-444075099202936753)⟩, true⟩

def state01 : KState := ⟨⟨362457213889714294, 362457229013646606⟩, ⟨904468113480186767, 904804520585373737⟩, true⟩

def words00 : List Nat := [371284729213971885, 371284729215034162, 371284728210122517, 371284727814127738, 371284727417612438, 371284727305998085, 371284725964751408, 371284724440830187, 371284722916577637, 371284722314180954]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 32900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 32900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362458067958562085, 362458083092073359⟩, ⟨876494317133638463, 876831039530601653⟩, true⟩

def words01 : List Nat := [371284721565380931, 371284721652414938, 371284721661523894, 371284721662604885, 371284720906428507, 371284720269793595, 371284719915823911, 371284719916886875, 371284719107746121, 371284718299835528]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 32910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 32900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362443167061369244, 362443182204415007⟩, ⟨1367162614352675503, 1367499650671812695⟩, true⟩

def words02 : List Nat := [371284717491505309, 371284717066113608, 371284716252001863, 371284715705549567, 371284715158810675, 371284714476707346, 371284712682479441, 371284711569454935, 371284710455916516, 371284709676345521]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 32920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 32900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362459340736606300, 362459355889323432⟩, ⟨834516175297206931, 834853530143056477⟩, true⟩

def words03 : List Nat := [371284708416103179, 371284707155655853, 371284705894863172, 371284705554755452, 371284704895586738, 371284704269989054, 371284703644060132, 371284703019199694, 371284701330494944, 371284700562369670]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 32930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 32900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362463917908345649, 362463933070552979⟩, ⟨683868931980981377, 684206599482836255⟩, true⟩

def words04 : List Nat := [371284699944172465, 371284699945259650, 371284699569438858, 371284699201715501, 371284698833598199, 371284698484045910, 371284697978312276, 371284698113092461, 371284698113909439, 371284698065984932]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 32940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 32900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362509224977462881, 362509240149299375⟩, ⟨(-809208724337311581), (-808870739506253951)⟩, true⟩

def words05 : List Nat := [371284697618143792, 371284697801028408, 371284698752897188, 371284698753961156, 371284698479876917, 371284698120895210, 371284698320216801, 371284698421600160, 371284699166914859, 371284699912671049]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 32950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 32900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362460391553468167, 362460406734913684⟩, ⟨800436375228828593, 800774676822441643⟩, true⟩

def words06 : List Nat := [371284700658953741, 371284700660017889, 371284700180818006, 371284699857085552, 371284699532860681, 371284699391205301, 371284698171744003, 371284696713191546, 371284695254280763, 371284694714192497]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 32960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 32900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362442346627323021, 362442361818339726⟩, ⟨1395598650260552932, 1395937267465368286⟩, true⟩

def words07 : List Nat := [371284694159853634, 371284694342573036, 371284694444882563, 371284694445947369, 371284693323554761, 371284692475590475, 371284691627114253, 371284691165999479, 371284689882509582, 371284688600251957]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 32970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 32900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362454449274510931, 362454464475053819⟩, ⟨996481295973492097, 996820227400950885⟩, true⟩

def words08 : List Nat := [371284687317610162, 371284686434511228, 371284685162996995, 371284684809618437, 371284684455905103, 371284683959867582, 371284682239718486, 371284681437602024, 371284680635000242, 371284680304923506]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 32980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 32900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362479921296401245, 362479936506679679⟩, ⟨156019915840331672, 156359168491279450⟩, true⟩

def words09 : List Nat := [371284679389853017, 371284678294318546, 371284677198403264, 371284677020150319, 371284676546698483, 371284676355686207, 371284676164338063, 371284675865348277, 371284674805547068, 371284674663300627]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 32990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 32900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 32900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk329
