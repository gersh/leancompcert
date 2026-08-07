import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk717

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360579993869353517, 360580027066207243⟩, ⟨163738899171806426, 165346617603475704⟩, true⟩

def state01 : KState := ⟨⟨360574808693449529, 360574841899899004⟩, ⟨535457102850038004, 537065509343303740⟩, true⟩

def words00 : List Nat := [360582333124387947, 360582333089047881, 360582332859544490, 360582332518119155, 360582332176537589, 360582331786031505, 360582331562628881, 360582331533563534, 360582331504372307, 360582331308758903]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 71700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 71700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360611783389494579, 360611816605542740⟩, ⟨(-2116198778394648800), (-2114589683530822888)⟩, true⟩

def words01 : List Nat := [360582331294800814, 360582331385589140, 360582331670153215, 360582331865103380, 360582331879130606, 360582331893220188, 360582332013368535, 360582332231546817, 360582332643473629, 360582333055626665]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 71710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 71700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594497096208993, 360594530321966178⟩, ⟨(-876387155645920973), (-874777364403688641)⟩, true⟩

def words02 : List Nat := [360582333342906614, 360582333676987625, 360582334077396106, 360582334478090283, 360582334777004076, 360582334882136471, 360582334890240323, 360582334898454852, 360582334902358575, 360582335073546336]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 71720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 71700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360573131504199664, 360573164739542695⟩, ⟨656326265979599640, 657936744862000456⟩, true⟩

def words03 : List Nat := [360582335274514923, 360582335475667340, 360582335579828164, 360582335704449587, 360582335779802073, 360582335855442193, 360582336021431720, 360582336022449648, 360582335994634982, 360582335867851338]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 71730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 71700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360600985398566921, 360601018643535127⟩, ⟨(-1342076721689764783), (-1340465552250612813)⟩, true⟩

def words04 : List Nat := [360582335806911589, 360582336020911841, 360582336176527141, 360582336332320613, 360582336333259600, 360582336323270485, 360582336209494724, 360582336153623581, 360582336195739927, 360582336457192768]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 71740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 71700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360580390856639413, 360580424111298692⟩, ⟨135693618244807808, 137305483066479968⟩, true⟩

def words05 : List Nat := [360582336621655451, 360582336786224505, 360582336971659614, 360582337255019567, 360582337467603999, 360582337680348415, 360582337704306524, 360582337705324715, 360582337535387841, 360582337509892150]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 71750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 71700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360582165784963298, 360582199049207417⟩, ⟨8314156316942979, 9926708994719097⟩, true⟩

def words06 : List Nat := [360582337651186088, 360582337685829650, 360582337686738935, 360582337602389548, 360582337517852534, 360582337353735267, 360582337349640650, 360582337411094232, 360582337412001980, 360582337361998204]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 71760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 71700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360603556346652656, 360603589620524286⟩, ⟨(-1527097247185121139), (-1525484003494122709)⟩, true⟩

def words07 : List Nat := [360582337360908887, 360582337355991229, 360582337402366603, 360582337403387815, 360582337391457294, 360582337186724479, 360582336981802432, 360582337107417002, 360582337404318999, 360582337701444110]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 71770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 71700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360609852400837393, 360609885684405157⟩, ⟨(-1979204636736699579), (-1977590697008798457)⟩, true⟩

def words08 : List Nat := [360582337881408234, 360582337976977669, 360582338163021212, 360582338349367738, 360582338403796947, 360582338527266624, 360582338553858691, 360582338580561097, 360582338800710779, 360582339185582063]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 71780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 71700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360555026810575199, 360555060103750182⟩, ⟨1957054620499780597, 1958669249977677083⟩, true⟩

def words09 : List Nat := [360582339548994084, 360582339912606159, 360582340177243947, 360582340248393243, 360582340249246032, 360582340248468606, 360582340247397249, 360582340219856372, 360582339998653494, 360582339619766585]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 71790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 71700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 71700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk717
