import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk723A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483769642769661, 362483847415557173⟩, ⟨98547569915348625, 102344984883827487⟩, true⟩

def state01 : KState := ⟨⟨362476928193580731, 362477005988503508⟩, ⟨593194678196351539, 596993693660138129⟩, true⟩

def words00 : List Nat := [371285263059952388, 371285263062433738, 371285262911820086, 371285262701583524, 371285262490369721, 371285262338143628, 371285262114828462, 371285262083568558, 371285262051494186, 371285262020776502]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 72300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 72300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362501517592255571, 362501595409627192⟩, ⟨(-1184952748221487233), (-1181152109370476583)⟩, true⟩

def words01 : List Nat := [371285261966029185, 371285262026767083, 371285262277214026, 371285262403360575, 371285262500187954, 371285262597745187, 371285262774622365, 371285262876876111, 371285263104404682, 371285263333060628]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 72310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 72300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490655949823683, 362490733789571052⟩, ⟨(-399437398795957989), (-395635141617214563)⟩, true⟩

def words02 : List Nat := [371285263561384738, 371285263563866868, 371285263668341586, 371285263802376322, 371285263938530280, 371285263941015634, 371285263893460353, 371285263847433107, 371285263924419598, 371285264002873548]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 72320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 72300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479465580640021, 362479543442755054⟩, ⟨410028047998040375, 413831923142116151⟩, true⟩

def words03 : List Nat := [371285264160521540, 371285264319136315, 371285264465199357, 371285264467682267, 371285264384148239, 371285264275890422, 371285264245876493, 371285264248402352, 371285264170482686, 371285264094167027]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 72330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 72300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490437317672066, 362490515201979203⟩, ⟨(-383666325668640611), (-379860845031862361)⟩, true⟩

def words04 : List Nat := [371285264128536572, 371285264148186184, 371285264337308045, 371285264527456864, 371285264686884083, 371285264689367491, 371285264649194029, 371285264680660165, 371285264876737847, 371285264951878557]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 72340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 72300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk723A
