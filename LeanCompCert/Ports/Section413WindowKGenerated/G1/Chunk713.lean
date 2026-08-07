import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk713

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483139204170525, 362483214758198796⟩, ⟨140529898423418746, 144168003437110728⟩, true⟩

def state01 : KState := ⟨⟨362474261000732707, 362474336576818523⟩, ⟨773611147501877999, 777250825334112073⟩, true⟩

def words00 : List Nat := [371285236723300185, 371285236697853579, 371285236610963620, 371285236661290843, 371285236749705736, 371285236752149765, 371285236597419090, 371285236440125813, 371285236281894097, 371285236181717333]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 71300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 71300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362467070306034058, 362467145904155848⟩, ⟨1286444021027082536, 1290085270357636444⟩, true⟩

def words01 : List Nat := [371285236030530774, 371285236028186790, 371285236024997975, 371285235983572407, 371285235699645150, 371285235433537141, 371285235166118420, 371285235095829224, 371285234843609753, 371285234592747515]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 71310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 71300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481632122866351, 362481707742892817⟩, ⟨247817513985379786, 251460325670700030⟩, true⟩

def words02 : List Nat := [371285234340782345, 371285234265208711, 371285234090239525, 371285233968393276, 371285233845813880, 371285233693220914, 371285233336170326, 371285233176708389, 371285233049804605, 371285233052379299]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 71320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 71300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483523853193288, 362483599495452732⟩, ⟨112886817527637814, 116531215202721054⟩, true⟩

def words03 : List Nat := [371285233004795781, 371285232949488848, 371285233031509309, 371285233075427977, 371285233126009753, 371285233177538121, 371285233192874247, 371285233195319940, 371285232977851083, 371285232957959078]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 71330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 71300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481852903226992, 362481928567280607⟩, ⟨232126910200877065, 235772862783145753⟩, true⟩

def words04 : List Nat := [371285233110044249, 371285233112489589, 371285233025943073, 371285232939905137, 371285232852844082, 371285232812265565, 371285232830000473, 371285232938765922, 371285233019725329, 371285233022260049]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 71340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 71300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362493300316366116, 362493376002579214⟩, ⟨(-584721270710282721), (-581073736935806617)⟩, true⟩

def words05 : List Nat := [371285233013508069, 371285233052355718, 371285233286051347, 371285233288497163, 371285233260789070, 371285233193616629, 371285233125492379, 371285233116596963, 371285233150342425, 371285233267234477]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 71350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 71300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481228136639802, 362481303844934453⟩, ⟨276791646306419179, 280440755932271637⟩, true⟩

def words06 : List Nat := [371285233382578949, 371285233385027012, 371285233366932752, 371285233458022283, 371285233556680829, 371285233559133890, 371285233456741553, 371285233355597380, 371285233253424769, 371285233237619507]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 71360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 71300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362469721833341156, 362469797563657979⟩, ⟨1098128992370573077, 1101779673831429893⟩, true⟩

def words07 : List Nat := [371285233304012362, 371285233426476826, 371285233529552851, 371285233531999619, 371285233397684904, 371285233317552277, 371285233328940494, 371285233331387452, 371285233188690198, 371285232975171449]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 71370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 71300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486388297958494, 362486464050171686⟩, ⟨(-91625037902327323), (-87972793365406303)⟩, true⟩

def words08 : List Nat := [371285232760592208, 371285232697441251, 371285232535067733, 371285232429376731, 371285232322905080, 371285232185596778, 371285231884050178, 371285231779791015, 371285231763080043, 371285231782891982]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 71380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 71300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486740428317188, 362486816202884577⟩, ⟨(-116775513765125941), (-113121673256515179)⟩, true⟩

def words09 : List Nat := [371285231799683356, 371285231817338718, 371285231893351021, 371285231896048123, 371285231926577461, 371285231968883490, 371285232010081818, 371285232012531421, 371285231862604904, 371285231887913407]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 71390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 71300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 71300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk713
