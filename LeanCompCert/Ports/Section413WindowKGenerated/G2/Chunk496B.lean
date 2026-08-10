import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk496A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk496B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk496A

def state06 : KState := ⟨⟨360564453321666548, 360564468783913585⟩, ⟨864202740862304197, 864721589854062809⟩, true⟩

def words05 : List Nat := [360581882454260466, 360581882555307916, 360581882555924260, 360581882458007013, 360581882458580188, 360581882369764528, 360581882280754030, 360581882120775442, 360581881972952425, 360581881623016567]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 49650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 49600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360625332539500662, 360625348008208945⟩, ⟨(-2159370531398481044), (-2158851361509438412)⟩, true⟩

def words06 : List Nat := [360581881272936457, 360581881366491025, 360581881938198065, 360581882510013327, 360581882647983446, 360581882648670127, 360581882979122857, 360581883346895878, 360581884118602770, 360581884994347549]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 49660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 49600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360598915721672619, 360598931196922885⟩, ⟨(-847045590102136139), (-846526095240794067)⟩, true⟩

def words07 : List Nat := [360581885665739910, 360581886337186261, 360581887128963006, 360581888200526266, 360581889162055734, 360581890123662215, 360581890828585922, 360581891277388901, 360581891620946378, 360581891964716593]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 49670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 49600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593598613005511, 360593614094707720⟩, ⟨(-582873126155356854), (-582353310728620818)⟩, true⟩

def words08 : List Nat := [360581892712217794, 360581893055645747, 360581893196856424, 360581893338136302, 360581893338711206, 360581893559193102, 360581893895879451, 360581894232679786, 360581894365466720, 360581894602028390]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 49680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 49600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589740158165834, 360589755646349456⟩, ⟨(-391280717949533789), (-390760580430332429)⟩, true⟩

def words09 : List Nat := [360581894786610795, 360581894971385247, 360581895041165781, 360581895041851398, 360581894707712257, 360581894024960042, 360581893342104074, 360581893100945270, 360581893259702420, 360581893418619022]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 49690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 49600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 49600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk496B
