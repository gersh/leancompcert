import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk928A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360583223507289569, 360583280249638322⟩, ⟨(-122004355306942035), (-118448613662473715)⟩, true⟩

def state01 : KState := ⟨⟨360597956890907745, 360598013645925199⟩, ⟨(-1489325300442383052), (-1485768383078573648)⟩, true⟩

def words00 : List Nat := [360582004008324364, 360582004197479520, 360582004384655283, 360582004572081144, 360582004650069622, 360582004733199531, 360582004761489315, 360582004790173923, 360582004934449286, 360582005108326439]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 92800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 92800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360594329282093475, 360594386049918395⟩, ⟨(-1152662625554614627), (-1149104519469249585)⟩, true⟩

def words01 : List Nat := [360582005223724091, 360582005339265854, 360582005451995548, 360582005630319074, 360582005753503652, 360582005876902316, 360582005942488926, 360582005990168171, 360582006124630618, 360582006259574947]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 92810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 92800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360579939270790385, 360579996051248941⟩, ⟨183114409324805582, 186673688127929272⟩, true⟩

def words02 : List Nat := [360582006509999162, 360582006644934443, 360582006721455432, 360582006798121970, 360582006821339969, 360582006906035961, 360582006962606205, 360582007019415557, 360582007020621150, 360582006971082270]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 92820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 92800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360598494956077955, 360598551749210771⟩, ⟨(-1539509385285363000), (-1535948929867112422)⟩, true⟩

def words03 : List Nat := [360582007044787657, 360582007140547669, 360582007227049625, 360582007356402385, 360582007386028041, 360582007415745892, 360582007441629293, 360582007525763498, 360582007705050572, 360582007884648056]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 92830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 92800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360598083428864699, 360598140234796149⟩, ⟨(-1501415486776243269), (-1497853843068690821)⟩, true⟩

def words04 : List Nat := [360582007974710899, 360582007983892227, 360582008086688208, 360582008189890428, 360582008242626823, 360582008261425995, 360582008262622650, 360582008223211297, 360582008258646203, 360582008433920890]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 92840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 92800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk928A
