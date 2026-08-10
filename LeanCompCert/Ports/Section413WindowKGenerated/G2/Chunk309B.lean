import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk309A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk309B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk309A

def state06 : KState := ⟨⟨360551058021571010, 360551063802281958⟩, ⟨989650745601320323, 989771775703257879⟩, true⟩

def words05 : List Nat := [360583042466851918, 360583041066086914, 360583039665335323, 360583038570734366, 360583038518637040, 360583037930088172, 360583037341533432, 360583036009355472, 360583034207044817, 360583033174882193]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 30950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 30900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360529662453028124, 360529668237618482⟩, ⟨1651994516035826728, 1652115666263637678⟩, true⟩

def words06 : List Nat := [360583032142651622, 360583031083497714, 360583029284401055, 360583026967199459, 360583024650082805, 360583021630914801, 360583019279614784, 360583017728869339, 360583016178176170, 360583013916219181]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 30960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 30900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360599291034394008, 360599296822868390⟩, ⟨(-504739809400919783), (-504618538865393251)⟩, true⟩

def words07 : List Nat := [360583012194112465, 360583011510678928, 360583010842923287, 360583010843335980, 360583010531487052, 360583009191807341, 360583007852132772, 360583007770206149, 360583008296333199, 360583008822517679]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 30970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 30900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360562108839119889, 360562114631516290⟩, ⟨647327991008194101, 647449383067811545⟩, true⟩

def words08 : List Nat := [360583008822884961, 360583008677281323, 360583009497709461, 360583010426999720, 360583011091433303, 360583011091845037, 360583010717467698, 360583009553328636, 360583008389192424, 360583006834906668]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 30980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 30900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360519882021505222, 360519887817780987⟩, ⟨1956155930248652190, 1956277442548875722⟩, true⟩

def words09 : List Nat := [360583006161102915, 360583005833300164, 360583005505471756, 360583004660597264, 360583002777232069, 360583000629976834, 360582998482727213, 360582997095887597, 360582995577041326, 360582993541734177]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 30990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 30900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 30900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk309B
