import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk271A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk271B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk271A

def state06 : KState := ⟨⟨360554927086861569, 360554931485738091⟩, ⟨755038946229071553, 755119758188763307⟩, true⟩

def words05 : List Nat := [360582727829389388, 360582730938803590, 360582732987416457, 360582733686729493, 360582734037992466, 360582734389324096, 360582735130314435, 360582735150795293, 360582735151115535, 360582734127792170]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 27150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 27100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360639150620612260, 360639155022859216⟩, ⟨(-1532955355158054680), (-1532874451640789586)⟩, true⟩

def words06 : List Nat := [360582733104457433, 360582733750364287, 360582735031436903, 360582736312482926, 360582736444217568, 360582736444575707, 360582736406327306, 360582736331897732, 360582737118486222, 360582739195262117]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 27160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 27100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360651696485242171, 360651700890889037⟩, ⟨(-1873930904197309817), (-1873849908287448997)⟩, true⟩

def words07 : List Nat := [360582740593098388, 360582741990867755, 360582744095744053, 360582747240609657, 360582750031753491, 360582752822749900, 360582754933402517, 360582756120025261, 360582758656913681, 360582761193737077]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 27170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 27100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585627729511974, 360585632138529249⟩, ⟨(-78120238731916501), (-78039151197464381)⟩, true⟩

def words08 : List Nat := [360582762990340413, 360582763440665283, 360582763440986187, 360582762783992844, 360582762126989722, 360582761123049085, 360582761599903089, 360582762233305758, 360582762233628257, 360582762102443873]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 27180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 27100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360653012051342514, 360653016463734094⟩, ⟨(-1910701597854243165), (-1910620418555707215)⟩, true⟩

def words09 : List Nat := [360582763557445771, 360582765012447668, 360582767388220935, 360582768418692374, 360582768419027893, 360582768089357616, 360582768778232805, 360582770482759590, 360582773065621767, 360582775648375993]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 27190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 27100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 27100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk271B
