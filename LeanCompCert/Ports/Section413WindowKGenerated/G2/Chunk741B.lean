import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk741A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk741B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk741A

def state06 : KState := ⟨⟨360568263914008660, 360568299523089437⟩, ⟨1039130995506399841, 1040914655472248915⟩, true⟩

def words05 : List Nat := [360582338505128754, 360582338060656993, 360582337615988767, 360582337270406496, 360582337051454379, 360582336786885613, 360582336522211161, 360582336147101233, 360582335777157331, 360582335589101739]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 74150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 74100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360575021347958821, 360575056966964330⟩, ⟨537982346596971879, 539766742630968887⟩, true⟩

def words06 : List Nat := [360582335400689706, 360582335394003714, 360582335360770583, 360582335214702439, 360582335068486041, 360582334765288120, 360582334568230991, 360582334552869064, 360582334537402695, 360582334393722197]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 74160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 74100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360576738260980912, 360576773889962921⟩, ⟨410586248853533915, 412371384893346927⟩, true⟩

def words07 : List Nat := [360582334296460551, 360582334261583439, 360582334226383352, 360582334212976848, 360582334017894446, 360582333650808550, 360582333283528139, 360582333098022691, 360582333028046327, 360582332954197127]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 74170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 74100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582569959893444, 360582605598916340⟩, ⟨(-22171985937422870), (-20386105014091590)⟩, true⟩

def words08 : List Nat := [360582332880198068, 360582332704152800, 360582332432253524, 360582332271398368, 360582332110260688, 360582331863773017, 360582331625196754, 360582331295191764, 360582330964990848, 360582330820236796]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 74180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 74100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360551369659859575, 360551405308835857⟩, ⟨2292731977463465641, 2294518596877535279⟩, true⟩

def words09 : List Nat := [360582330871745393, 360582330923450542, 360582330924407092, 360582330835513751, 360582330564953048, 360582330143250910, 360582329721238495, 360582329480790341, 360582329155711125, 360582328740060622]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 74190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 74100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 74100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk741B
