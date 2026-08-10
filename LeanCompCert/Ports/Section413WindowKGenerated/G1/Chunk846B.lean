import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk846A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk846B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk846A

def state06 : KState := ⟨⟨362488684767820466, 362488792711931381⟩, ⟨(-300507950840219440), (-294337431428849266)⟩, true⟩

def words05 : List Nat := [371285316163829172, 371285316071872794, 371285316023124495, 371285316026394471, 371285316020481336, 371285316041091806, 371285316060555598, 371285316063546643, 371285316008200687, 371285316052886144]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 84650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 84600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470715665263025, 362470823635522728⟩, ⟨1220870802034765725, 1227043535339093019⟩, true⟩

def words06 : List Nat := [371285316213514463, 371285316216454511, 371285316191362739, 371285316155445315, 371285316118406553, 371285316059042345, 371285315933246013, 371285315859252652, 371285315784304507, 371285315705149977]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 84660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 84600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483689222621239, 362483797219541387⟩, ⟨122360024819205663, 128535015589566951⟩, true⟩

def words07 : List Nat := [371285315535986641, 371285315491201016, 371285315535721405, 371285315538661913, 371285315446021817, 371285315334556806, 371285315221929533, 371285315198637327, 371285315125199687, 371285315110608813]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 84670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 84600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478912239746218, 362479020263211823⟩, ⟨526874571042476678, 533051809820635594⟩, true⟩

def words08 : List Nat := [371285315094902858, 371285315067775089, 371285314906283187, 371285314849101865, 371285314790499137, 371285314775498651, 371285314667226673, 371285314559950749, 371285314451454169, 371285314416120321]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 84680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 84600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476491654433562, 362476599704390321⟩, ⟨731939357912069460, 738118840358895440⟩, true⟩

def words09 : List Nat := [371285314408825717, 371285314477021789, 371285314508244201, 371285314511195252, 371285314431640511, 371285314379397161, 371285314409145367, 371285314412086789, 371285314312068102, 371285314212540958]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 84690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 84600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 84600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk846B
