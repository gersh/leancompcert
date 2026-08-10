import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk819A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483262762872871, 362483363526016328⟩, ⟨146623534374406309, 152195962868075517⟩, true⟩

def state01 : KState := ⟨⟨362478492534976901, 362478593323361222⟩, ⟨537365755331063306, 542940251184585874⟩, true⟩

def words00 : List Nat := [371285221946189128, 371285221949027659, 371285221909838663, 371285221860952244, 371285221810942942, 371285221807824577, 371285221781954785, 371285221801798232, 371285221818180389, 371285221821117108]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 81900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 81900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362498264727003236, 362498365541054479⟩, ⟨(-1082273649940208595), (-1076697051579682043)⟩, true⟩

def words01 : List Nat := [371285221788001882, 371285221837305276, 371285221984024955, 371285222008072400, 371285222010268719, 371285222011107300, 371285222086295067, 371285222100902875, 371285222263269305, 371285222426937468]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 81910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 81900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488005606114378, 362488106445798569⟩, ⟨(-241867976406188712), (-236289278065350428)⟩, true⟩

def words02 : List Nat := [371285222562033487, 371285222564870668, 371285222504697231, 371285222511603361, 371285222549002824, 371285222551858023, 371285222478232931, 371285222405322358, 371285222404015603, 371285222442453494]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 81920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 81900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482040092386893, 362482140957584298⟩, ⟨246975456370347516, 252556245140189580⟩, true⟩

def words03 : List Nat := [371285222628533219, 371285222815737791, 371285223003923792, 371285223013344071, 371285223028898309, 371285223045891934, 371285223210287582, 371285223213126116, 371285223201514076, 371285223167068558]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 81930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 81900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488500893465646, 362488601784076524⟩, ⟨(-282394021883491080), (-276811150601208594)⟩, true⟩

def words04 : List Nat := [371285223220298923, 371285223258127535, 371285223443619531, 371285223630287693, 371285223790672048, 371285223793510281, 371285223813641711, 371285223875521315, 371285223975738205, 371285224019917439]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 81940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 81900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk819A
