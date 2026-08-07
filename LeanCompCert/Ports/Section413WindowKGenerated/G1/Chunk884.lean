import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk884

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489513757521566, 362489631842606032⟩, ⟨(-400059900088701612), (-393011734193609090)⟩, true⟩

def state01 : KState := ⟨⟨362471966571186908, 362472084684058302⟩, ⟨1151148909767467880, 1158199532169765110⟩, true⟩

def words00 : List Nat := [371285186109097673, 371285186112177802, 371285185991826010, 371285185916401390, 371285185839486668, 371285185802624561, 371285185594572994, 371285185360278205, 371285185124705551, 371285185006783896]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 88400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 88400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362463310922711897, 362463429063288087⟩, ⟨1916491789392750474, 1923544861317977162⟩, true⟩

def words01 : List Nat := [371285184860697459, 371285184843613092, 371285184825519865, 371285184806032367, 371285184615201269, 371285184465113049, 371285184313392089, 371285184185067541, 371285183941287242, 371285183698679605]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 88410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 88400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478414723094916, 362478532891230134⟩, ⟨580968313281321140, 588023822118511844⟩, true⟩

def words02 : List Nat := [371285183454735808, 371285183307796524, 371285183095649559, 371285183012579637, 371285182928493259, 371285182822763693, 371285182626148912, 371285182558824653, 371285182489951104, 371285182487771111]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 88420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 88400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480658252722193, 362480776449007616⟩, ⟨382567324427413836, 389625322726662630⟩, true⟩

def words03 : List Nat := [371285182414919088, 371285182318324241, 371285182240901949, 371285182244339269, 371285182214200155, 371285182200577673, 371285182185943300, 371285182160536348, 371285182027770013, 371285181981829040]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 88430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 88400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475077713984530, 362475195937668493⟩, ⟨876138412980362459, 883198834549083517⟩, true⟩

def words04 : List Nat := [371285181989129137, 371285181992210855, 371285181879244145, 371285181769158359, 371285181657965164, 371285181553389521, 371285181383644683, 371285181331817376, 371285181278905493, 371285181226922864]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 88440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 88400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362482632736542098, 362482750988095052⟩, ⟨207847796661443123, 214910683378649599⟩, true⟩

def words05 : List Nat := [371285181116142911, 371285181026536498, 371285180964618280, 371285180967701203, 371285180852260289, 371285180717633960, 371285180581728686, 371285180557948417, 371285180479493277, 371285180455463113]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 88450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 88400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485105637313880, 362485223916708219⟩, ⟨(-10948328910066917), (-3882979203243087)⟩, true⟩

def words06 : List Nat := [371285180430324780, 371285180406454583, 371285180266979296, 371285180256762129, 371285180253682947, 371285180256819919, 371285180176507614, 371285180084262311, 371285180022808900, 371285180026855011]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 88460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 88400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484006389470288, 362484124696688146⟩, ⟨86337291501725920, 93405102894685226⟩, true⟩

def words07 : List Nat := [371285180157032234, 371285180288489410, 371285180374690495, 371285180377775648, 371285180318989440, 371285180300071656, 371285180370212923, 371285180373312332, 371285180368508278, 371285180360147625]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 88470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 88400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485373674128769, 362485492008912896⟩, ⟨(-34617368058162067), (-27547117457787471)⟩, true⟩

def words08 : List Nat := [371285180430076134, 371285180449426590, 371285180561706263, 371285180675229114, 371285180751070311, 371285180754153746, 371285180673051993, 371285180646699651, 371285180703681367, 371285180710391490]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 88480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 88400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489416108544265, 362489534471372526⟩, ⟨(-392337220366784441), (-385264487998993285)⟩, true⟩

def words09 : List Nat := [371285180714144342, 371285180718900013, 371285180849948227, 371285180938357645, 371285181031765351, 371285181126378530, 371285181220483613, 371285181223567223, 371285181196530337, 371285181249510638]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 88490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 88400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 88400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk884
