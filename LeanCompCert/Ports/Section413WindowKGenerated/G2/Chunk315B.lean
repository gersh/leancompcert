import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk315A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk315B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk315A

def state06 : KState := ⟨⟨360526900952413527, 360526906969100894⟩, ⟨1761194679032923844, 1761323085999059616⟩, true⟩

def words05 : List Nat := [360582723191437726, 360582721964714561, 360582720737987533, 360582720268286869, 360582720268638307, 360582720031540795, 360582719794404758, 360582718911962627, 360582717453301844, 360582715685387303]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 31550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 31500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360544255057471881, 360544261078120356⟩, ⟨1213221772400949491, 1213350304399051333⟩, true⟩

def words06 : List Nat := [360582713917446228, 360582712709663251, 360582710910873251, 360582708317402672, 360582705724026176, 360582702657954690, 360582700100705829, 360582698543541580, 360582696986431233, 360582694727293592]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 31560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 31500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560133752844075, 360560139777453752⟩, ⟨711891183126349364, 712019840199654676⟩, true⟩

def words07 : List Nat := [360582693510261538, 360582693043873904, 360582693110101361, 360582693110521526, 360582692642074166, 360582691312869723, 360582689983676678, 360582688203840280, 360582687034379789, 360582686320841962]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 31570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 31500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360545907396305329, 360545913424921246⟩, ⟨1160924398046733366, 1161053181656040480⟩, true⟩

def words08 : List Nat := [360582685607295185, 360582684058988309, 360582681509475364, 360582679959184166, 360582678408872079, 360582676607066431, 360582674492714547, 360582671879068917, 360582669265508610, 360582667245169934]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 31580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 31500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360493006095528375, 360493012128105678⟩, ⟨2832274615808604946, 2832403524578316022⟩, true⟩

def words09 : List Nat := [360582666082088873, 360582664893038887, 360582663704015577, 360582662016107390, 360582659327767067, 360582656176979845, 360582653026269927, 360582650314613042, 360582647987177583, 360582645151035372]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 31590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 31500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 31500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk315B
