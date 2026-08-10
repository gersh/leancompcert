import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk541A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360562829752027083, 360562848231254341⟩, ⟨1028136889086125181, 1028812361822995175⟩, true⟩

def state01 : KState := ⟨⟨360594790302771781, 360594808789097488⟩, ⟨(-701087355251085591), (-700411498452804521)⟩, true⟩

def words00 : List Nat := [360581864744714009, 360581864932727584, 360581865034562245, 360581865136526331, 360581865137219031, 360581864948263742, 360581864662126679, 360581864615781695, 360581864572847989, 360581864812855083]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 54100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 54100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360562875063534644, 360562893557014738⟩, ⟨1026086159384653506, 1026762403341656858⟩, true⟩

def words01 : List Nat := [360581864815602116, 360581864818430977, 360581865055870246, 360581865507347822, 360581865813930105, 360581866120623674, 360581866163071814, 360581866163823317, 360581865865383981, 360581865515686979]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 54110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 54100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360570828235889624, 360570846736438169⟩, ⟨595591520752952561, 596268147290400693⟩, true⟩

def words02 : List Nat := [360581865165747557, 360581865156717050, 360581864806820048, 360581864286208393, 360581863765481164, 360581863149018416, 360581862751366977, 360581862631308669, 360581862511170754, 360581862220408064]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 54120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 54100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360584045602689832, 360584064110342958⟩, ⟨(-120114687206630355), (-119437676063675881)⟩, true⟩

def words03 : List Nat := [360581862017535421, 360581861527943034, 360581861038144503, 360581860889080883, 360581860399333303, 360581859620490797, 360581858841533254, 360581858278643330, 360581858020239677, 360581858061764918]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 54130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 54100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360574380310174445, 360574398824986782⟩, ⟨403111987896078323, 403789386673002655⟩, true⟩

def words04 : List Nat := [360581858062434659, 360581857933311468, 360581858048993890, 360581858198663251, 360581858199308343, 360581858018022661, 360581857496110961, 360581856803758600, 360581856111287899, 360581855692700042]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 54140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 54100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk541A
