import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk444A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk444B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk444A

def state06 : KState := ⟨⟨360549400126036495, 360549412407567423⟩, ⟨1502373110132893998, 1502742110568789140⟩, true⟩

def words05 : List Nat := [360583215543204178, 360583214988956461, 360583214434617382, 360583214628426215, 360583214628936097, 360583214572049355, 360583214515108733, 360583214027357710, 360583213034645604, 360583212275101584]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 44450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 44400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575074052983484, 360575086340232032⟩, ⟨360828673993751416, 361197928664297318⟩, true⟩

def words06 : List Nat := [360583211515379190, 360583211152268913, 360583210919192694, 360583210432465518, 360583209945650657, 360583209330254084, 360583208970191390, 360583208952505831, 360583208934760362, 360583208623314207]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 44460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 44400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360578671004760907, 360578683297756690⟩, ⟨200699720966310169, 201069231244841805⟩, true⟩

def words07 : List Nat := [360583208441171972, 360583208247029627, 360583208052721785, 360583207685948923, 360583207044979477, 360583205961720654, 360583204878394220, 360583204159586447, 360583203840108202, 360583203739106619]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 44470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 44400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580366590427030, 360580378889210736⟩, ⟨125133358801002551, 125503126555095051⟩, true⟩

def words08 : List Nat := [360583203638021884, 360583203283608497, 360583202704532084, 360583202630228315, 360583202555771996, 360583202039882980, 360583201634056661, 360583200973118342, 360583200312094500, 360583199818106108]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 44480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 44400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360548159437647598, 360548171742167216⟩, ⟨1558294949171269776, 1558664972144754084⟩, true⟩

def words09 : List Nat := [360583200196159909, 360583200637725495, 360583200825941088, 360583200826549343, 360583200510682267, 360583199861000620, 360583199211163143, 360583199065727792, 360583198707808863, 360583197921316537]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 44490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 44400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 44400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk444B
