import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk352

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360538074219979604, 360538081772746093⟩, ⟨1545309888410944353, 1545489624381697675⟩, true⟩

def state01 : KState := ⟨⟨360571575746068437, 360571583303296368⟩, ⟨365870287424899975, 366050180460731209⟩, true⟩

def words00 : List Nat := [360581986481073213, 360581986040240742, 360581986002897197, 360581985762250420, 360581985521578185, 360581984593234888, 360581983256824028, 360581981804038682, 360581980351192427, 360581979502684631]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 35200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 35200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360532163993838477, 360532171555560771⟩, ⟨1753766644012467713, 1753946695317070067⟩, true⟩

def words01 : List Nat := [360581979207853938, 360581978235941837, 360581977263995126, 360581976660874480, 360581976460692402, 360581976058667329, 360581975656626449, 360581974582493520, 360581972704836860, 360581971291373295]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 35210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 35200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580129403080211, 360580136969252539⟩, ⟨64154917785844729, 64335125842694651⟩, true⟩

def words02 : List Nat := [360581969877833683, 360581969269404507, 360581968543931392, 360581967347428976, 360581966150908221, 360581964731080964, 360581963825089917, 360581963723982502, 360581963622829251, 360581963115316766]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 35220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 35200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360604436155691488, 360604443726327365⟩, ⟨(-792503057518335819), (-792322692188848109)⟩, true⟩

def words03 : List Nat := [360581963063872125, 360581962976511614, 360581962917645811, 360581962918118479, 360581962419913962, 360581961218292864, 360581960016648909, 360581959469597770, 360581960108012237, 360581960746497371]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 35230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 35200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360551963553950258, 360551971129087096⟩, ⟨1056634556947307917, 1056815080911935483⟩, true⟩

def words04 : List Nat := [360581960829502062, 360581960829974871, 360581960389620390, 360581960184623969, 360581959979513610, 360581959127398489, 360581957473103473, 360581955359184589, 360581953245295222, 360581951698758357]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 35240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 35200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk352
