import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk200A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk200B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk200A

def state06 : KState := ⟨⟨360623034660487458, 360623036996826911⟩, ⟨(-823523009340972249), (-823491292052856421)⟩, true⟩

def words05 : List Nat := [360581979786178369, 360581981666709712, 360581983908778741, 360581984877867341, 360581984878108169, 360581983497945320, 360581982194896346, 360581983539446329, 360581985586188603, 360581987632784598]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 20050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 20000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360610325365367203, 360610327704159550⟩, ⟨(-568585905112605849), (-568554138607318753)⟩, true⟩

def words06 : List Nat := [360581988427159570, 360581989340565908, 360581992727121453, 360581996113416850, 360581998869256225, 360582000065331348, 360582000065560424, 360582000017617370, 360581999969633406, 360582000558595935]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 20060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 20000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360481590785066113, 360481593126280744⟩, ⟨2016117815117313956, 2016149630250089954⟩, true⟩

def words07 : List Nat := [360582004441467590, 360582008324002709, 360582010963365842, 360582011130703934, 360582011130921021, 360582009561562396, 360582007992280900, 360582007224082640, 360582003984635449, 360581998984360928]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 20070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 20000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596425222295079, 360596427565943109⟩, ⟨(-290640376443916712), (-290608512436862542)⟩, true⟩

def words08 : List Nat := [360581993984526513, 360581990529588404, 360581988336795572, 360581985159956220, 360581981983414134, 360581976634516717, 360581971209925950, 360581967395583655, 360581963581543030, 360581962954304223]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 20080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 20000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592363364178471, 360592365710278315⟩, ⟨(-209045518879604647), (-209013605603558127)⟩, true⟩

def words09 : List Nat := [360581962954533772, 360581962076587914, 360581962024497570, 360581964537027161, 360581966424283831, 360581968311394676, 360581968311631918, 360581967745420759, 360581967023138591, 360581967540754234]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 20090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 20000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 20000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk200B
