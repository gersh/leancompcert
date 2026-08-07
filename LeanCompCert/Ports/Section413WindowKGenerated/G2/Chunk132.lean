import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk132

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360566846175838679, 360566847149237491⟩, ⟨188344230284739742, 188352932906888434⟩, true⟩

def state01 : KState := ⟨⟨360610360799194696, 360610361774131263⟩, ⟨(-386005266754543891), (-385996543826432401)⟩, true⟩

def words00 : List Nat := [360581117465780549, 360581122687155032, 360581124718350113, 360581126749253900, 360581126749390755, 360581128489237358, 360581134753240030, 360581141016326057, 360581141747934676, 360581143959898697]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 13200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 13200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360721515164246569, 360721516140723196⟩, ⟨(-1855409927701257287), (-1855401184420967187)⟩, true⟩

def words01 : List Nat := [360581146946324851, 360581149932347188, 360581156794516380, 360581157970373724, 360581157970524228, 360581154265560333, 360581152560645325, 360581157476043255, 360581168093321151, 360581178709029605]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 13210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 13200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360710960703141010, 360710961681178240⟩, ⟨(-1716605603394072703), (-1716596839475183881)⟩, true⟩

def words02 : List Nat := [360581185777030489, 360581192191331987, 360581198425161696, 360581204658094479, 360581207945030121, 360581209528305262, 360581209528450913, 360581208238660674, 360581211352984590, 360581221159715374]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 13220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 13200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360522069005902964, 360522069985478884⟩, ⟨783864369537445652, 783873153821137870⟩, true⟩

def words03 : List Nat := [360581234601184873, 360581248040653996, 360581257132182389, 360581264696407837, 360581270758748902, 360581276820217025, 360581280929651244, 360581280929814885, 360581279378301669, 360581274906462354]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 13230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 13200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360633875477697065, 360633876458818593⟩, ⟨(-697089588488493559), (-697080783733283691)⟩, true⟩

def words04 : List Nat := [360581271648410151, 360581275759521335, 360581278035172777, 360581280310514965, 360581280310665823, 360581277738768653, 360581272347584484, 360581268534518308, 360581266588178558, 360581270558604777]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 13240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 13200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360646553725794913, 360646554708478630⟩, ⟨(-865489581746950153), (-865480756285055181)⟩, true⟩

def words05 : List Nat := [360581270558753200, 360581270121068353, 360581272115864480, 360581277767460449, 360581279626826030, 360581281485936882, 360581281486084408, 360581280491906043, 360581284666338736, 360581289588481266]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 13250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 13200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360694538487029143, 360694539471255909⟩, ⟨(-1502132468720850269), (-1502123622790245133)⟩, true⟩

def words06 : List Nat := [360581298158473062, 360581304576854232, 360581308129746187, 360581311682120343, 360581311682260004, 360581315549688910, 360581325492704651, 360581335434253024, 360581342513830023, 360581351043647572]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 13260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 13200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604796970132879, 360604797955910609⟩, ⟨(-310744929984565805), (-310736063464964967)⟩, true⟩

def words07 : List Nat := [360581362002345662, 360581372959442956, 360581385496442955, 360581392407676989, 360581394138972389, 360581395870018340, 360581395870152512, 360581397393555372, 360581399155781130, 360581400917776059]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 13270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 13200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360644013720084437, 360644014707426189⟩, ⟨(-832400752054375250), (-832391864756915236)⟩, true⟩

def words08 : List Nat := [360581400917922688, 360581399142742577, 360581394785975890, 360581393424908046, 360581392064000144, 360581389206824561, 360581389134099216, 360581385507446826, 360581381881307998, 360581386472924879]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 13280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 13200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360613570788825890, 360613571777718556⟩, ⟨(-427243263534724836), (-427234355617984052)⟩, true⟩

def words09 : List Nat := [360581396826668783, 360581407178886188, 360581413133570562, 360581419422617454, 360581424220164455, 360581429017033076, 360581439450071408, 360581446478079655, 360581448893664011, 360581451308910348]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 13290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 13200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 13200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk132
