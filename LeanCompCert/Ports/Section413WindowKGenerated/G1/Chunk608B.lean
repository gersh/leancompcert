import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk608A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk608B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk608A

def state06 : KState := ⟨⟨362505021681193830, 362505076049983707⟩, ⟨(-1206846986446559394), (-1204611932123923156)⟩, true⟩

def words05 : List Nat := [371285281931773879, 371285282140307253, 371285282485368081, 371285282487429915, 371285282472676684, 371285282417401571, 371285282500210224, 371285282557527703, 371285282884156167, 371285283211677996]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 60850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 60800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487047885672635, 362487102273043542⟩, ⟨(-112951395783900260), (-110715210522730606)⟩, true⟩

def words06 : List Nat := [371285283537579824, 371285283539641882, 371285283606244888, 371285283709480717, 371285283797145333, 371285283799217356, 371285283629288406, 371285283460792773, 371285283390939325, 371285283423172130]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 60860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 60800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476900643856856, 362476955049851337⟩, ⟨504846663561145972, 507083982533277548⟩, true⟩

def words07 : List Nat := [371285283654767195, 371285283887249843, 371285284120832626, 371285284122909067, 371285284185006686, 371285284257676598, 371285284498732600, 371285284500795595, 371285284421881221, 371285284287409374]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 60870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 60800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362498262718445491, 362498317142880417⟩, ⟨(-795764017805470327), (-793525576085145487)⟩, true⟩

def words08 : List Nat := [371285284205503458, 371285284207776734, 371285284312599047, 371285284484655271, 371285284555126058, 371285284557224966, 371285284519494252, 371285284637408174, 371285285024205612, 371285285240364690]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 60880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 60800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496364195575228, 362496418638829094⟩, ⟨(-680147133140567356), (-677907545443726512)⟩, true⟩

def words09 : List Nat := [371285285455105156, 371285285670527009, 371285285995812316, 371285286214258663, 371285286494927421, 371285286776418223, 371285287050321256, 371285287052384582, 371285287149459272, 371285287334820232]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 60890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 60800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 60800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk608B
