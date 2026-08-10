import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk295A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk295B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk295A

def state06 : KState := ⟨⟨360541515677597300, 360541520926335773⟩, ⟨1240111812663457514, 1240216742226291258⟩, true⟩

def words05 : List Nat := [360583474696402038, 360583476145131617, 360583477024780287, 360583477941089901, 360583478220367518, 360583478499733082, 360583478947573202, 360583478947964743, 360583478256768137, 360583476837777800]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 29550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 29500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360558321673318075, 360558326925760109⟩, ⟨743033366960520476, 743138406018894182⟩, true⟩

def words06 : List Nat := [360583475418800796, 360583473560710319, 360583472440809264, 360583471128920087, 360583469817091993, 360583467537045683, 360583464118396332, 360583461840193634, 360583459562020463, 360583458424103664]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 29560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 29500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360541147903837110, 360541153160008517⟩, ⟨1251026899446768188, 1251132048800814450⟩, true⟩

def words07 : List Nat := [360583457574582988, 360583456156709428, 360583454738857008, 360583454881785210, 360583454882120766, 360583454357926760, 360583453833725560, 360583452741554498, 360583451142886661, 360583449713382446]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 29570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 29500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585826042748951, 360585831302614940⟩, ⟨(-70772922960173790), (-70667664301796206)⟩, true⟩

def words08 : List Nat := [360583448283844057, 360583447993540890, 360583447738855038, 360583446787259741, 360583445835664969, 360583444318490933, 360583443577133632, 360583443776076021, 360583443776431240, 360583443155397821]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 29580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 29500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360634602005743222, 360634607269305375⟩, ⟨(-1514390845339315940), (-1514285477292708392)⟩, true⟩

def words09 : List Nat := [360583444081200557, 360583445007059552, 360583446760436128, 360583447377495395, 360583447377856834, 360583447009878922, 360583446655962777, 360583447247050861, 360583448975747240, 360583450704415922]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 29590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 29500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 29500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk295B
