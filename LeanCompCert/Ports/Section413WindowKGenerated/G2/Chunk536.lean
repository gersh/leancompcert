import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk536

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360579411035132188, 360579429160690531⟩, ⟨135289719869074791, 135946147410074421⟩, true⟩

def state01 : KState := ⟨⟨360567222872351021, 360567241004986439⟩, ⟨788399934734414271, 789056741642589069⟩, true⟩

def words00 : List Nat := [360581965422756909, 360581965136063091, 360581964501891964, 360581963911781715, 360581963321489043, 360581962581225313, 360581961863552184, 360581960948853376, 360581960034046239, 360581959466871211]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 53600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 53600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360572736006934763, 360572754146588204⟩, ⟨492848099048907743, 493505282227947867⟩, true⟩

def words01 : List Nat := [360581959265737574, 360581959339289061, 360581959339970835, 360581959105121975, 360581958817650880, 360581958442776290, 360581958067697537, 360581958070657497, 360581958071320423, 360581957900452955]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 53610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 53600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591356922017192, 360591375068691023⟩, ⟨(-505699091033610161), (-505041531387796423)⟩, true⟩

def words02 : List Nat := [360581957729410740, 360581957755215000, 360581958207663803, 360581958660238285, 360581958775882718, 360581958776626873, 360581958545104375, 360581958222045975, 360581957922080362, 360581958098442701]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 53620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 53600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360602952219869018, 360602970373637863⟩, ⟨(-1127646790470106012), (-1126988850284011904)⟩, true⟩

def words03 : List Nat := [360581958099111941, 360581958044672268, 360581958282027283, 360581958844517876, 360581959201838242, 360581959559271356, 360581959702997541, 360581959748374320, 360581960140673052, 360581960533211995]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 53630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 53600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579148710860283, 360579166871642399⟩, ⟨149162026784699366, 149820343198174898⟩, true⟩

def words04 : List Nat := [360581960827193185, 360581960827937611, 360581960775045770, 360581960547794680, 360581960320430607, 360581960005682617, 360581959865857516, 360581959777614270, 360581959689286865, 360581959422307790]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 53640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 53600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360613518966659303, 360613537134468645⟩, ⟨(-1695044023912917960), (-1694385330454629484)⟩, true⟩

def words05 : List Nat := [360581959421871559, 360581959473701388, 360581959872177052, 360581960009792028, 360581960010490577, 360581959823505955, 360581959795496843, 360581960224646379, 360581960813711893, 360581961402923303]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 53650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 53600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580439822091242, 360580457996998430⟩, ⟨80168400185547130, 80827474549982530⟩, true⟩

def words06 : List Nat := [360581961793328280, 360581962193190032, 360581962853411003, 360581963513829869, 360581964086574608, 360581964312858675, 360581964318652349, 360581964324520877, 360581964325139473, 360581964005467780]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 53660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 53600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360540384779303897, 360540402961225757⟩, ⟨2230242554690390806, 2230902005566894308⟩, true⟩

def words07 : List Nat := [360581964229798436, 360581964482322362, 360581964560587846, 360581964561332937, 360581964415033891, 360581964099407685, 360581963783554948, 360581963571010196, 360581963011969901, 360581962238527674]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 53670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 53600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360588573279199481, 360588591468157558⟩, ⟨(-356799087782360985), (-356139259166926199)⟩, true⟩

def words08 : List Nat := [360581961464940234, 360581961038072300, 360581960831797617, 360581960616968922, 360581960402096453, 360581959890536748, 360581959265138866, 360581958836944838, 360581958408548471, 360581958340460795]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 53680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 53600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360586346117273837, 360586364313320708⟩, ⟨(-237208382672418382), (-236548173424375848)⟩, true⟩

def words09 : List Nat := [360581958341128905, 360581958205877366, 360581958280801929, 360581958717701410, 360581959067173151, 360581959416753539, 360581959499385954, 360581959500131166, 360581959318551502, 360581959401430346]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 53690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 53600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 53600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk536
