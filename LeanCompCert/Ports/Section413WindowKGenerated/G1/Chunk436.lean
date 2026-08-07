import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk436

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362470210471265176, 362470237635282704⟩, ⟨665270407416299622, 666070637683623628⟩, true⟩

def state01 : KState := ⟨⟨362492056285368257, 362492083462288856⟩, ⟨(-287308261403571297), (-286507468498296347)⟩, true⟩

def words00 : List Nat := [371285514210112339, 371285514211706258, 371285514222978243, 371285514338679362, 371285514349753606, 371285514351193369, 371285513661192913, 371285513498063415, 371285513695385962, 371285513847547202]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 43600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 43600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489354870337974, 362489382060349774⟩, ⟨(-169438233493614282), (-168636869614043606)⟩, true⟩

def words01 : List Nat := [371285513997553384, 371285514148025265, 371285514823883470, 371285515238727597, 371285515621360374, 371285516004536272, 371285516277167430, 371285516278607599, 371285516013888239, 371285516104282421]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 43610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 43600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490918614156276, 362490945816996762⟩, ⟨(-237613408141170804), (-236811484607890634)⟩, true⟩

def words02 : List Nat := [371285516670158615, 371285516701123962, 371285516702211482, 371285516681043009, 371285516778926266, 371285516780523451, 371285517174447545, 371285517635254401, 371285518094107462, 371285518219999034]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 43620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 43600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502118442629530, 362502145658519809⟩, ⟨(-726331846674794421), (-725529353713339833)⟩, true⟩

def words03 : List Nat := [371285518474048585, 371285518728850244, 371285519508345341, 371285519588229879, 371285519589608978, 371285519591423135, 371285519863184836, 371285519946022314, 371285520327977060, 371285520710564599]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 43630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 43600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475050887242529, 362475078116138222⟩, ⟨454936554414582045, 455739614997297833⟩, true⟩

def words04 : List Nat := [371285521080255657, 371285521081696589, 371285520804127587, 371285520858478523, 371285520870724934, 371285520872166165, 371285520245131688, 371285519617312179, 371285518988903843, 371285518886241253]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 43640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 43600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362473964398282254, 362473991640157224⟩, ⟨502514168282903972, 503317795476254418⟩, true⟩

def words05 : List Nat := [371285518933866254, 371285519221264788, 371285519506854756, 371285519508305218, 371285519494426575, 371285519567528176, 371285520107818340, 371285520109260005, 371285520024347078, 371285519761904276]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 43650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 43600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362511803876105889, 362511831130884740⟩, ⟨(-1149703085432598929), (-1148898894788622137)⟩, true⟩

def words06 : List Nat := [371285519759554808, 371285519821051701, 371285520316291760, 371285520812113207, 371285521182702282, 371285521184169191, 371285521395979488, 371285521674096664, 371285522475963618, 371285523079894641]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 43660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 43600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362499766980553136, 362499794248501701⟩, ⟨(-623973847155306726), (-623169081327282624)⟩, true⟩

def words07 : List Nat := [371285523682283016, 371285524285143308, 371285524971284647, 371285525449892025, 371285526090269008, 371285526731154317, 371285527328512850, 371285527329955269, 371285527555232960, 371285527883690290]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 43670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 43600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470428720758140, 362470456001536468⟩, ⟨657656256011919981, 658461582311125489⟩, true⟩

def words08 : List Nat := [371285528392698286, 371285528394140757, 371285528204790504, 371285528015028849, 371285527824737118, 371285527792696218, 371285527497149653, 371285527405588183, 371285527313531153, 371285527221090397]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 43680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 43600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362511914978932057, 362511942272736480⟩, ⟨(-1155065489661712718), (-1154259594186300040)⟩, true⟩

def words09 : List Nat := [371285527056043535, 371285527236680585, 371285527758548299, 371285527846450131, 371285527847577093, 371285527848994540, 371285528255952846, 371285528402681506, 371285529008097260, 371285529614120286]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 43690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 43600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 43600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk436
