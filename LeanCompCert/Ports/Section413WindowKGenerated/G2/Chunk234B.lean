import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk234A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk234B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk234A

def state06 : KState := ⟨⟨360635170953016340, 360635174193038875⟩, ⟨(-1265427323728499596), (-1265375898675984780)⟩, true⟩

def words05 : List Nat := [360581219760234730, 360581220961368280, 360581223354261904, 360581226664347162, 360581229509595684, 360581232354651212, 360581233814738832, 360581234301626147, 360581236601101168, 360581238900482037]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 23450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 23400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588153480748247, 360588156723642763⟩, ⟨(-162308745494793091), (-162257253051014897)⟩, true⟩

def words06 : List Nat := [360581242133975657, 360581243564973035, 360581243566714554, 360581243568489759, 360581243568746968, 360581242342647235, 360581242765375795, 360581243505075243, 360581243505347205, 360581243628629726]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 23460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 23400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360670693732779167, 360670696978559010⟩, ⟨(-2100109685774690009), (-2100058125598253599)⟩, true⟩

def words07 : List Nat := [360581243847959452, 360581244067358214, 360581246096911914, 360581248157547915, 360581248666880298, 360581249176192779, 360581250268765834, 360581252873664669, 360581256683285902, 360581260492651330]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 23470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 23400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360606156687380650, 360606159936068082⟩, ⟨(-584812815618943804), (-584761187158243294)⟩, true⟩

def words08 : List Nat := [360581263380848322, 360581265131847836, 360581267705235289, 360581270278492994, 360581271114472044, 360581271114777418, 360581270152764652, 360581268281757632, 360581266410851770, 360581266947810527]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 23480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 23400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360536907737551243, 360536910989119877⟩, ⟨1042276425772331849, 1042328121926797855⟩, true⟩

def words09 : List Nat := [360581268366892760, 360581269785916447, 360581270043691829, 360581270043998096, 360581269719285578, 360581268455261223, 360581267733252503, 360581267733558259, 360581267264471525, 360581265377286975]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 23490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 23400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 23400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk234B
