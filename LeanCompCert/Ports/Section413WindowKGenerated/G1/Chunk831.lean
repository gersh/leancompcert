import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk831

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362490747006848635, 362490850860628623⟩, ⟨(-466111802198121671), (-460284390914479933)⟩, true⟩

def state01 : KState := ⟨⟨362485995322722924, 362486099202173242⟩, ⟨(-71193350419234738), (-65363805801928238)⟩, true⟩

def words00 : List Nat := [371285312219058111, 371285312266134468, 371285312312243612, 371285312359422432, 371285312411641207, 371285312414856580, 371285312514847940, 371285312621816177, 371285312725771974, 371285312738217786]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 83100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 83100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362500273504467573, 362500377410016447⟩, ⟨(-1257958563675708156), (-1252126849872819830)⟩, true⟩

def words01 : List Nat := [371285312799969734, 371285312863204804, 371285313015506238, 371285313018390280, 371285313013444909, 371285312986301505, 371285313072522698, 371285313137289991, 371285313320480308, 371285313504987961]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 83110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 83100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362491886639194869, 362491990570725646⟩, ⟨(-560818770986743305), (-554984897436417957)⟩, true⟩

def words02 : List Nat := [371285313683527242, 371285313754419641, 371285313947414868, 371285314141900822, 371285314341140091, 371285314365784088, 371285314367953336, 371285314359480282, 371285314458954538, 371285314542560023]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 83120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 83100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486803983090722, 362486907940581395⟩, ⟨(-138228821899260513), (-132392790168815211)⟩, true⟩

def words03 : List Nat := [371285314741083046, 371285314940802132, 371285315139439848, 371285315160604792, 371285315206974663, 371285315254802846, 371285315445815587, 371285315508154100, 371285315529501546, 371285315551866215]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 83130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 83100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489516671926723, 362489620655223846⟩, ⟨(-363726691118599620), (-357888513709981926)⟩, true⟩

def words04 : List Nat := [371285315699256939, 371285315785153243, 371285315944071883, 371285316104190040, 371285316228200354, 371285316232944261, 371285316303791933, 371285316376113753, 371285316520982426, 371285316575733402]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 83140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 83100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362486706764232473, 362486810773885635⟩, ⟨(-130061294122077922), (-124220925085359684)⟩, true⟩

def words05 : List Nat := [371285316629634211, 371285316684524916, 371285316798950075, 371285316842427747, 371285316928912590, 371285317016473750, 371285317100314039, 371285317103197214, 371285317012043628, 371285317033729969]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 83150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 83100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475563762665693, 362475667797969251⟩, ⟨796667871686212965, 802510373944376907⟩, true⟩

def words06 : List Nat := [371285317149941347, 371285317152825743, 371285317100801149, 371285317044509504, 371285316987132360, 371285316975079419, 371285316897643421, 371285316877010705, 371285316855379616, 371285316834568318]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 83160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 83100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499610819750682, 362499714881076892⟩, ⟨(-1203458795712714999), (-1197614129016708633)⟩, true⟩

def words07 : List Nat := [371285316720523000, 371285316681955486, 371285316720210318, 371285316723158480, 371285316719621618, 371285316696844932, 371285316791508498, 371285316841199427, 371285317016250325, 371285317192554072]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 83170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 83100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362492245398562624, 362492349485953149⟩, ⟨(-590794204322173034), (-584947369464392050)⟩, true⟩

def words08 : List Nat := [371285317320620698, 371285317352526161, 371285317518630252, 371285317686265403, 371285317884977144, 371285317891929534, 371285317897863999, 371285317904766997, 371285318020111416, 371285318107925906]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 83180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 83100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481803841776690, 362481907955163502⟩, ⟨277917553227743603, 283766550846933099⟩, true⟩

def words09 : List Nat := [371285318297656630, 371285318488579935, 371285318650721434, 371285318653606201, 371285318623060004, 371285318601042951, 371285318684213478, 371285318687106272, 371285318648512823, 371285318610822720]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 83190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 83100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 83100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk831
