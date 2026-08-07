import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk781

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362467561679120016, 362467652975035800⟩, ⟨1368106509398018681, 1372921405383759335⟩, true⟩

def state01 : KState := ⟨⟨362484652413812393, 362484743733828104⟩, ⟨33274644088543225, 38091422401975935⟩, true⟩

def words00 : List Nat := [371285231771058283, 371285231712835183, 371285231576882833, 371285231584615686, 371285231586702489, 371285231556402025, 371285231390342172, 371285231352951572, 371285231394875317, 371285231397666307]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 78100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 78100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478997828964819, 362479089173632159⟩, ⟨474975668339838173, 479794372308835567⟩, true⟩

def words01 : List Nat := [371285231393472752, 371285231355684888, 371285231344160993, 371285231347132418, 371285231310045702, 371285231286984712, 371285231263047466, 371285231237478144, 371285231009833384, 371285230934670419]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 78110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 78100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480870202913952, 362480961571579182⟩, ⟨328741090123359146, 333561668933579254⟩, true⟩

def words02 : List Nat := [371285230943020188, 371285230945735601, 371285230913817023, 371285230882814788, 371285230866967105, 371285230869940790, 371285230842186643, 371285230864407700, 371285230884900596, 371285230887705300]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 78120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 78100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362500735735630156, 362500827128621154⟩, ⟨(-1223481891507587822), (-1218659411998014094)⟩, true⟩

def words03 : List Nat := [371285230867313855, 371285230902938351, 371285231021851879, 371285231024595473, 371285231007535974, 371285230964889252, 371285231039212267, 371285231078125602, 371285231279545725, 371285231482135980]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 78130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 78100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484350101159220, 362484441518526336⟩, ⟨56929572715723178, 61753957095446312⟩, true⟩

def words04 : List Nat := [371285231646127709, 371285231648824739, 371285231685331912, 371285231760085380, 371285231883614648, 371285231886312719, 371285231819675483, 371285231751034141, 371285231713233687, 371285231716313866]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 78140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 78100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362474159527682112, 362474250969343664⟩, ⟨853425965594687232, 858252248708576574⟩, true⟩

def words05 : List Nat := [371285231834473208, 371285231963860774, 371285232089376751, 371285232092077781, 371285232041404730, 371285231958619739, 371285231952003881, 371285231954701055, 371285231816194422, 371285231678769312]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 78150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 78100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492522516073963, 362492613981904784⟩, ⟨(-581854059060279966), (-577025886750724914)⟩, true⟩

def words06 : List Nat := [371285231540110953, 371285231541910856, 371285231586232236, 371285231692165516, 371285231776546402, 371285231779275551, 371285231936198366, 371285232098773118, 371285232299609194, 371285232396831666]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 78160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 78100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362493070346638483, 362493161837007784⟩, ⟨(-624658664021253282), (-619828573414221914)⟩, true⟩

def words07 : List Nat := [371285232485066933, 371285232574186302, 371285232825778233, 371285233004068645, 371285233205315901, 371285233407677958, 371285233565599772, 371285233568297489, 371285233609426364, 371285233714146549]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 78170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 78100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490086697557243, 362490178211988381⟩, ⟨(-391363326810422832), (-386531354924725722)⟩, true⟩

def words08 : List Nat := [371285233944585392, 371285234050065709, 371285234110411127, 371285234171632473, 371285234267771404, 371285234291194981, 371285234438316755, 371285234586527383, 371285234720785530, 371285234786850901]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 78180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 78100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502921503369566, 362503013042214146⟩, ⟨(-1394941117991291108), (-1390107237098793372)⟩, true⟩

def words09 : List Nat := [371285235015370107, 371285235245352833, 371285235637323626, 371285235812238135, 371285235970927622, 371285236130419073, 371285236356847268, 371285236502596938, 371285236731761264, 371285236962149968]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 78190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 78100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 78100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk781
