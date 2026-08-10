import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk352A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk352B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk352A

def state06 : KState := ⟨⟨360519988034500575, 360519995614096938⟩, ⟨2184037618640127538, 2184218299825173770⟩, true⟩

def words05 : List Nat := [360581950848652322, 360581950802165622, 360581950755625675, 360581950307226606, 360581949056874262, 360581947277204359, 360581945497494580, 360581944521257065, 360581943436852862, 360581941680456132]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 35250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 35200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360608221515537183, 360608229099598675⟩, ⟨(-927507664840481537), (-927326826192443589)⟩, true⟩

def words06 : List Nat := [360581939924051948, 360581938619667960, 360581937717451399, 360581937451138867, 360581937184803091, 360581936233956107, 360581936033978482, 360581936335706787, 360581936872678807, 360581937618603171]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 35260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 35200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360581127888295173, 360581135476871689⟩, ⟨28153067560014267, 28334065475293553⟩, true⟩

def words07 : List Nat := [360581937963332236, 360581938308089549, 360581938630954005, 360581939355422471, 360581939585460915, 360581939815561996, 360581939815986427, 360581939443510131, 360581938618852359, 360581938596641397]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 35270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 35200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595195423420812, 360595203016452286⟩, ⟨(-468101999290326540), (-467920844181138744)⟩, true⟩

def words08 : List Nat := [360581939353682052, 360581940351030774, 360581940862882243, 360581941374755557, 360581941685426403, 360581942397142922, 360581942970398174, 360581943543708014, 360581943711791747, 360581944087995141]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 35280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 35200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360657718695116936, 360657726292617446⟩, ⟨(-2674828966256110423), (-2674647653412643915)⟩, true⟩

def words09 : List Nat := [360581945265839233, 360581946443756545, 360581948044330496, 360581949671768197, 360581950622912755, 360581951574038516, 360581953058694065, 360581955089910735, 360581957236789304, 360581959383651337]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 35290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 35200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 35200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk352B
