import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk325A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk325B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk325A

def state06 : KState := ⟨⟨360458674103405640, 360458680524115969⟩, ⟨3993718811694356407, 3993860172757113463⟩, true⟩

def words05 : List Nat := [360581362991099237, 360581361894668448, 360581360798259219, 360581359227687688, 360581357141151613, 360581354482242730, 360581351823376320, 360581349138949177, 360581345844243235, 360581342077333326]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 32550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 32500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360554037031162132, 360554043455969157⟩, ⟨888280098941728027, 888421593413067957⟩, true⟩

def words06 : List Nat := [360581338310553567, 360581335484572993, 360581333216683708, 360581331889402476, 360581330562163326, 360581328418346545, 360581325886786093, 360581323862416724, 360581321838043947, 360581320753894029]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 32560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 32500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360595735207938296, 360595741636891617⟩, ⟨(-470205237658612966), (-470063608122400880)⟩, true⟩

def words07 : List Nat := [360581319916822172, 360581318198457823, 360581316480114860, 360581315701832058, 360581315505398310, 360581315063956215, 360581314622493886, 360581313709238707, 360581313655786609, 360581314099120450]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 32570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 32500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360602464539605284, 360602470972646734⟩, ⟨(-689475731369867575), (-689333968621431109)⟩, true⟩

def words08 : List Nat := [360581315104540891, 360581315984039242, 360581316391902297, 360581316799787747, 360581316800158589, 360581316656350060, 360581317761632464, 360581318866930131, 360581319270183528, 360581319919637578]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 32580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 32500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360587752332805967, 360587758769956058⟩, ⟨(-210036214399271721), (-209894317729836443)⟩, true⟩

def words09 : List Nat := [360581320425541202, 360581320931546998, 360581321582365378, 360581321677112195, 360581321677513191, 360581320899573371, 360581320121598021, 360581320095638603, 360581320293501668, 360581320491445282]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 32590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 32500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 32500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk325B
