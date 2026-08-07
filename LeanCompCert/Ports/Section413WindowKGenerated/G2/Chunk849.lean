import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk849

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360591737224146678, 360591784390321423⟩, ⟨(-794518398854350181), (-791814106675078663)⟩, true⟩

def state01 : KState := ⟨⟨360591301984057681, 360591349161731957⟩, ⟨(-757620272705130944), (-754915004158329358)⟩, true⟩

def words00 : List Nat := [360582458271118014, 360582458335985452, 360582458337096190, 360582458288124618, 360582458238955156, 360582458155180412, 360582458268171271, 360582458383496717, 360582458393704052, 360582458499695727]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 84900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 84900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360596836293480733, 360596883482669188⟩, ⟨(-1227617810735246056), (-1224911564463683162)⟩, true⟩

def words01 : List Nat := [360582458610502838, 360582458721664500, 360582458971014114, 360582459081960397, 360582459083100711, 360582459049725744, 360582459016127503, 360582459010452433, 360582459181298059, 360582459352425036]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 84910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 84900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575298532283316, 360575345733081046⟩, ⟨601407984571721412, 604115216759273432⟩, true⟩

def words02 : List Nat := [360582459453877391, 360582459455097376, 360582459489266768, 360582459562072642, 360582459567608593, 360582459568828602, 360582459435828381, 360582459233500588, 360582459030948806, 360582458828768781]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 84920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 84900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360550797899262382, 360550845111557582⟩, ⟨2682330948469853867, 2685039157196756523⟩, true⟩

def words03 : List Nat := [360582458746027591, 360582458592399380, 360582458438648484, 360582458215742058, 360582457854064874, 360582457457829675, 360582457061245468, 360582456774832426, 360582456492075531, 360582456121178453]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 84930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 84900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360564784512436467, 360564831736253079⟩, ⟨1494282612962989469, 1496991800373575975⟩, true⟩

def words04 : List Nat := [360582455750013193, 360582455429892647, 360582455223794096, 360582455133249221, 360582455042631188, 360582454819591455, 360582454457784522, 360582454234779276, 360582454011425725, 360582453770395205]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 84940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 84900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360542415899632854, 360542463135092807⟩, ⟨3394643682955422848, 3397353859526009158⟩, true⟩

def words05 : List Nat := [360582453564055035, 360582453288643409, 360582453012988622, 360582452759330155, 360582452574951390, 360582452315321929, 360582452055565207, 360582451726524363, 360582451291028010, 360582450821763311]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 84950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 84900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360560395152337126, 360560442399296817⟩, ⟨1867015581873534794, 1869726735516944068⟩, true⟩

def words06 : List Nat := [360582450352090645, 360582450021059914, 360582449626371595, 360582449148868702, 360582448671169610, 360582448158975096, 360582447770345305, 360582447520346136, 360582447270222049, 360582446950732818]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 84960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 84900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360571066501999138, 360571113760490409⟩, ⟨960140825298662899, 962852958837163807⟩, true⟩

def words07 : List Nat := [360582446692754900, 360582446519727179, 360582446346362236, 360582446146687020, 360582445808489124, 360582445329919405, 360582444851126532, 360582444511064956, 360582444240368617, 360582444108323278]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 84970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 84900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360554727487171755, 360554774757285027⟩, ⟨2348598372814898131, 2351311494049188381⟩, true⟩

def words08 : List Nat := [360582443976088047, 360582443756396245, 360582443398056451, 360582443086958899, 360582442775546446, 360582442390629586, 360582441984616982, 360582441463024584, 360582440941211010, 360582440500243601]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 84980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 84900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360541990704148749, 360542037985761038⟩, ⟨3431258383544657006, 3433972482138100346⟩, true⟩

def words09 : List Nat := [360582440175716775, 360582439989740198, 360582439803635137, 360582439532118611, 360582439316190722, 360582439045118683, 360582438773687263, 360582438524120789, 360582438136048236, 360582437662021487]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 84990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 84900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 84900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk849
