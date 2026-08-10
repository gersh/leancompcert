import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk634A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk634B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk634A

def state06 : KState := ⟨⟨362469628032100245, 362469687341034640⟩, ⟨995586609254733851, 998128791296443453⟩, true⟩

def words05 : List Nat := [371285415392957294, 371285415739132168, 371285416085926731, 371285416102302752, 371285416109073486, 371285416116913604, 371285416251659095, 371285416253815231, 371285416057821163, 371285415812375587]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 63450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 63400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488390677017989, 362488450005275459⟩, ⟨(-195143877985904320), (-192600469601835044)⟩, true⟩

def words06 : List Nat := [371285415565997550, 371285415478153532, 371285415365729887, 371285415435300280, 371285415465935795, 371285415468102582, 371285415302780126, 371285415346119017, 371285415491138978, 371285415541195772]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 63460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 63400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362492595024911006, 362492654372827419⟩, ⟨(-461972581702534073), (-459427925465861337)⟩, true⟩

def words07 : List Nat := [371285415589813411, 371285415639185980, 371285415935889060, 371285416118672583, 371285416375229390, 371285416632623238, 371285416887962672, 371285416890125478, 371285417005206987, 371285417121910360]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 63470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 63400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479800855378316, 362479860222524487⟩, ⟨350226682666250038, 352772559708578554⟩, true⟩

def words08 : List Nat := [371285417321712089, 371285417323869180, 371285417193159039, 371285417015669124, 371285416837377828, 371285416735312336, 371285416527038981, 371285416548619534, 371285416568649300, 371285416570921221]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 63480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 63400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502624745160899, 362502684131774360⟩, ⟨(-1098962887034464751), (-1096415773917089957)⟩, true⟩

def words09 : List Nat := [371285416621145889, 371285416760005555, 371285417145823330, 371285417239620302, 371285417278064294, 371285417317177863, 371285417439605079, 371285417465847801, 371285417739227444, 371285418013541308]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 63490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 63400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 63400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk634B
