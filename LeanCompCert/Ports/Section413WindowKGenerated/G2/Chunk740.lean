import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk740

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360587052086291921, 360587087535775849⟩, ⟨(-350168587710836218), (-348396750674912176)⟩, true⟩

def state01 : KState := ⟨⟨360563100102083829, 360563135561589121⟩, ⟨1422300966539771663, 1424073545206651117⟩, true⟩

def words00 : List Nat := [360582379536139331, 360582379471895651, 360582379274915552, 360582379195850885, 360582379116491697, 360582378922511977, 360582378546002234, 360582378078750891, 360582377611306797, 360582377198465309]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 74000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 74000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360550877599682338, 360550913069107253⟩, ⟨2326911585946771662, 2328684898815868354⟩, true⟩

def words01 : List Nat := [360582376939347647, 360582376634360063, 360582376329266150, 360582375933183866, 360582375452221978, 360582374904172037, 360582374355817298, 360582373989918478, 360582373705135482, 360582373281196093]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 74010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 74000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590445118285810, 360590480597644036⟩, ⟨(-602076191968888157), (-600302143789833819)⟩, true⟩

def words02 : List Nat := [360582372857029719, 360582372615396322, 360582372502059599, 360582372514103517, 360582372515101972, 360582372357216738, 360582372016787808, 360582371858855368, 360582371700617517, 360582371803439044]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 74020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 74000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360564159665334797, 360564195154726733⟩, ⟨1344031922938551290, 1345806713962080986⟩, true⟩

def words03 : List Nat := [360582371822833900, 360582371842361239, 360582371997758775, 360582372246358522, 360582372344807180, 360582372443418194, 360582372444358993, 360582372388910642, 360582372150972621, 360582371906671116]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 74030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 74000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360557324519173161, 360557360018479336⟩, ⟨1850045894961842049, 1851821420084811971⟩, true⟩

def words04 : List Nat := [360582371662032681, 360582371396173660, 360582370947923103, 360582370388117570, 360582369828155730, 360582369184706401, 360582368708365003, 360582368414315310, 360582368120153825, 360582367735158402]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 74040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 74000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360571864008196483, 360571899517455721⟩, ⟨773286763573284816, 775063025768748106⟩, true⟩

def words05 : List Nat := [360582367398300461, 360582367243836252, 360582367089060350, 360582366885353928, 360582366557930335, 360582366074854700, 360582365591590613, 360582365248437789, 360582364996918177, 360582364856718059]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 74050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 74000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360554714491717338, 360554750011013175⟩, ⟨2043367883077274085, 2045144888633286737⟩, true⟩

def words06 : List Nat := [360582364716363701, 360582364457184983, 360582364120057588, 360582363811574955, 360582363502821658, 360582363148280273, 360582362697985011, 360582362106453165, 360582361514738020, 360582360985613328]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 74060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 74000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360563139495385720, 360563175024596646⟩, ⟨1419378145003153393, 1421155885019893379⟩, true⟩

def words07 : List Nat := [360582360613701394, 360582360423949456, 360582360234087626, 360582359953437213, 360582359833436062, 360582359667837763, 360582359517104531, 360582359518157924, 360582359352196149, 360582359094318837]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 74070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 74000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360567334610205876, 360567370149381208⟩, ⟨1108538159424733071, 1110316637652937783⟩, true⟩

def words08 : List Nat := [360582358836226583, 360582358513631938, 360582358282550809, 360582358136494891, 360582357990367783, 360582357665829282, 360582357281015451, 360582356882304156, 360582356483262236, 360582356201988213]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 74080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 74000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360563717157356388, 360563752706562316⟩, ⟨1376580648804540735, 1378359870248322175⟩, true⟩

def words09 : List Nat := [360582356000661628, 360582355708571735, 360582355416288042, 360582355306160284, 360582355301751207, 360582355143922754, 360582354985985473, 360582354736164941, 360582354304161002, 360582354054338947]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 74090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 74000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 74000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk740
