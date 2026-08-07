import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk212

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362540922180753874, 362540928228470264⟩, ⟨(-1199017874069970835), (-1198931167982684181)⟩, true⟩

def state01 : KState := ⟨⟨362477496257596657, 362477502311282284⟩, ⟨145688728349976735, 145775561015208431⟩, true⟩

def words00 : List Nat := [371284380016306761, 371284380016967602, 371284379535622557, 371284379515002774, 371284380158589638, 371284380159251518, 371284378460284602, 371284376771487516, 371284375274260364, 371284375275026519]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 21200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 21200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362426614688821581, 362426620748450914⟩, ⟨1225442690883065380, 1225529649644516732⟩, true⟩

def words01 : List Nat := [371284376842059737, 371284378733204837, 371284380615831580, 371284380616492938, 371284379543952704, 371284379157874006, 371284379273090034, 371284379273751471, 371284376987389142, 371284374266341797]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 21210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 21200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362463614567150098, 362463620632699380⟩, ⟨440298983500988186, 440386067913944096⟩, true⟩

def words02 : List Nat := [371284371545264432, 371284371037292463, 371284369550771306, 371284369632857620, 371284369633370238, 371284369421052955, 371284366256941735, 371284365304646440, 371284364352109077, 371284364206317560]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 21220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 21200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362478231198394634, 362478237269986368⟩, ⟨129845822618785519, 129933035343478117⟩, true⟩

def words03 : List Nat := [371284363229783970, 371284361791129097, 371284360352334446, 371284360307674737, 371284359150774899, 371284358456240810, 371284357761555506, 371284357076274238, 371284354931725279, 371284354644531730]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 21230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 21200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362470421077750328, 362470427155239625⟩, ⟨295817416913945897, 295904754933205837⟩, true⟩

def words04 : List Nat := [371284355201131470, 371284355201798514, 371284354638320703, 371284353913880970, 371284353189270604, 371284352535345500, 371284351212231631, 371284351654720806, 371284352084195398, 371284352084883541]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 21240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 21200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362516714622223272, 362516720705702795⟩, ⟨(-688050815442061048), (-687963350100303828)⟩, true⟩

def words05 : List Nat := [371284352697052902, 371284353964717158, 371284357076256453, 371284357243942573, 371284357306195287, 371284357368651312, 371284359063678136, 371284359664472396, 371284361187086578, 371284362709837112]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 21250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 21200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487039797356700, 362487045886815981⟩, ⟨(-57252120563467434), (-57164528060982796)⟩, true⟩

def words06 : List Nat := [371284364114537198, 371284364115200284, 371284362578402810, 371284362174659037, 371284362051010864, 371284362051686107, 371284360752000208, 371284359207799431, 371284358320096065, 371284358447200496]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 21260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 21200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362456405497155644, 362456411592602928⟩, ⟨594702570750034435, 594790290647117587⟩, true⟩

def words07 : List Nat := [371284360438751722, 371284362430390189, 371284363963934720, 371284363964602542, 371284363531967279, 371284363177737239, 371284364668010695, 371284364668674199, 371284363576920748, 371284362264155895]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 21270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 21200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474344859406366, 362474350960784791⟩, ⟨213019785025869256, 213107631168613470⟩, true⟩

def words08 : List Nat := [371284361119293310, 371284361120024013, 371284361441510893, 371284362702000645, 371284363276808553, 371284363277472865, 371284361495572027, 371284360634132224, 371284360712618789, 371284360713305628]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 21280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 21200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362491408526531732, 362491414633954318⟩, ⟨(-150248970021857229), (-150160995168932199)⟩, true⟩

def words09 : List Nat := [371284360243662265, 371284359609153940, 371284360347809618, 371284361127099079, 371284362590380388, 371284364053790907, 371284365442419075, 371284365443084092, 371284364821160155, 371284365152936107]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 21290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 21200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 21200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk212
