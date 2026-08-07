import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk910

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482886573467413, 362483011986795633⟩, ⟨183435752155690685, 191141311668235043⟩, true⟩

def state01 : KState := ⟨⟨362482703415380266, 362482828857135469⟩, ⟨200106663299071274, 207814809810113868⟩, true⟩

def words00 : List Nat := [371285112449296256, 371285112452801757, 371285112478306249, 371285112524264471, 371285112549909782, 371285112553087880, 371285112417584303, 371285112334096304, 371285112282140502, 371285112285437965]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 91000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 91000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488753679102105, 362488879149773766⟩, ⟨(-350562455737569719), (-342851677395481079)⟩, true⟩

def words01 : List Nat := [371285112262727327, 371285112231355483, 371285112244520192, 371285112262636764, 371285112310095228, 371285112358801582, 371285112405382891, 371285112408570347, 371285112372878902, 371285112418169022]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 91010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 91000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478532252333167, 362478657751357810⟩, ⟨579840053996612617, 587553413176080543⟩, true⟩

def words02 : List Nat := [371285112512050687, 371285112515230186, 371285112464060842, 371285112413944851, 371285112362587902, 371285112314845389, 371285112229735867, 371285112242618789, 371285112251122269, 371285112254413683]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 91020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 91000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488585913853148, 362488711441634445⟩, ⟨(-335385990573775350), (-327670013530548212)⟩, true⟩

def words03 : List Nat := [371285112185668033, 371285112185173802, 371285112299254668, 371285112302438672, 371285112290786030, 371285112237378225, 371285112224200625, 371285112227704747, 371285112250696693, 371285112293849046]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 91030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 91000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477894703967127, 362478020260446802⟩, ⟨637999591778267015, 645718181667613743⟩, true⟩

def words04 : List Nat := [371285112335681894, 371285112338917952, 371285112334901930, 371285112392124632, 371285112476014244, 371285112479193951, 371285112402502213, 371285112307943903, 371285112212094906, 371285112167988457]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 91040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 91000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362472036301884857, 362472161886983817⟩, ⟨1171479801389279801, 1179200997207195319⟩, true⟩

def words05 : List Nat := [371285112125294923, 371285112161781804, 371285112184346672, 371285112187527463, 371285112066536490, 371285111984134943, 371285111899979817, 371285111874468458, 371285111740093030, 371285111601427121]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 91050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 91000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470154978135770, 362470280591717968⟩, ⟨1342836608008123129, 1350560397659628787⟩, true⟩

def words06 : List Nat := [371285111461375225, 371285111413719542, 371285111304362843, 371285111246599045, 371285111187829452, 371285111121422307, 371285110893333337, 371285110755282984, 371285110615640995, 371285110507141924]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 91060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 91000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478401722904624, 362478527365524931⟩, ⟨591760081496032262, 599486515787587110⟩, true⟩

def words07 : List Nat := [371285110346704719, 371285110186414006, 371285110024786490, 371285109967010083, 371285109853595513, 371285109777976412, 371285109701354737, 371285109601865870, 371285109411306671, 371285109343080790]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 91070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 91000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476278294862575, 362476403965788039⟩, ⟨785190178716196346, 792919191189934052⟩, true⟩

def words08 : List Nat := [371285109321151801, 371285109324332947, 371285109214278238, 371285109095118391, 371285108974711316, 371285108892495166, 371285108778326933, 371285108774557000, 371285108769695151, 371285108754361867]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 91080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 91000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489475396725456, 362489601096399527⟩, ⟨(-417048785629820444), (-409317154298554668)⟩, true⟩

def words09 : List Nat := [371285108661021820, 371285108571931934, 371285108493326025, 371285108496509492, 371285108371066523, 371285108227363607, 371285108082339284, 371285108059167128, 371285108039565084, 371285108092433615]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 91090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 91000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 91000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk910
