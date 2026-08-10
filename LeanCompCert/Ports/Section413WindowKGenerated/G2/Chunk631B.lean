import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk631A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk631B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk631A

def state06 : KState := ⟨⟨360576121758889307, 360576147259653690⟩, ⟨413287056192452141, 414375080724380335⟩, true⟩

def words05 : List Nat := [360582707606755180, 360582707748033876, 360582707761219696, 360582707887226370, 360582707887970947, 360582707866031635, 360582708019397929, 360582708081907899, 360582708082698855, 360582707979741157]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 63150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 63100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588348299720035, 360588373808872617⟩, ⟨(-358996460133136084), (-357907905761059600)⟩, true⟩

def words06 : List Nat := [360582707876598380, 360582707859373077, 360582708148380708, 360582708437549116, 360582708514378089, 360582708515265601, 360582708342258828, 360582708167239444, 360582708018722315, 360582708109330722]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 63160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 63100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360577233129340914, 360577258646952343⟩, ⟨343165989484435124, 344255078242159048⟩, true⟩

def words07 : List Nat := [360582708110128784, 360582708076305752, 360582708046114476, 360582708175760880, 360582708176519122, 360582708115142857, 360582708053671433, 360582707866280417, 360582707530494744, 360582707445278430]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 63170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 63100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360578321198408505, 360578346724387036⟩, ⟨274388136868113827, 275477754301315361⟩, true⟩

def words08 : List Nat := [360582707359756456, 360582707265987119, 360582707178638519, 360582706965412745, 360582706752042951, 360582706475708729, 360582706372672867, 360582706422355576, 360582706423170061, 360582706239410004]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 63180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 63100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360608441591962688, 360608467126320784⟩, ⟨(-1629153259449892766), (-1628063112469843578)⟩, true⟩

def words09 : List Nat := [360582706236922416, 360582706303682046, 360582706443137084, 360582706473062919, 360582706473887169, 360582706255007193, 360582706066259553, 360582706224787489, 360582706633114597, 360582707041631146]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 63190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 63100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 63100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk631B
