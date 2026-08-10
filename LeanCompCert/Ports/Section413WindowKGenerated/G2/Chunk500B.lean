import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk500A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk500B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk500A

def state06 : KState := ⟨⟨360621948197450236, 360621963920085541⟩, ⟨(-2005829489359337735), (-2005297657355647241)⟩, true⟩

def words05 : List Nat := [360581902070208285, 360581902503571426, 360581903334980514, 360581903957301489, 360581904226609514, 360581904495960511, 360581904755694688, 360581905234911840, 360581906035683813, 360581906836580305]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 50050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 50000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580374739424353, 360580390468637860⟩, ⟨75298690155719138, 75830851496733698⟩, true⟩

def words06 : List Nat := [360581907263202550, 360581907291953265, 360581907438592202, 360581907585438323, 360581907586019831, 360581907420921762, 360581906857866914, 360581906094366215, 360581905330763717, 360581904965372367]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 50060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 50000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360551140631338166, 360551156367067929⟩, ⟨1539119691233542499, 1539652178875995557⟩, true⟩

def words07 : List Nat := [360581904935694615, 360581904767224319, 360581904598680642, 360581904230911874, 360581903465227493, 360581902593515570, 360581901721625215, 360581901247755860, 360581900833671668, 360581900220479990]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 50070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 50000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360571660746126520, 360571676488378659⟩, ⟨511380994180659930, 511913808495392454⟩, true⟩

def words08 : List Nat := [360581899607156365, 360581899268465216, 360581899204208677, 360581899041810807, 360581898879381775, 360581898342313504, 360581897521014213, 360581897097635471, 360581896674073688, 360581896368763874]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 50080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 50000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360557048758626793, 360557064507470354⟩, ⟨1243466943426177943, 1244000087936491869⟩, true⟩

def words09 : List Nat := [360581896165353525, 360581895724219405, 360581895282958608, 360581895527189181, 360581895637368854, 360581895747657282, 360581895748273186, 360581895659456125, 360581895343383091, 360581894848546931]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 50090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 50000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 50000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk500B
