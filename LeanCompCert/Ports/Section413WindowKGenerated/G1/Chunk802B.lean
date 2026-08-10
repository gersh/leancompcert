import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk802A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk802B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk802A

def state06 : KState := ⟨⟨362469690681105716, 362469787298879830⟩, ⟨1229650136215439927, 1234886445248159143⟩, true⟩

def words05 : List Nat := [371285173743207933, 371285173876271217, 371285173992897063, 371285173995671342, 371285173905295147, 371285173823358768, 371285173752624103, 371285173755398487, 371285173563313198, 371285173374699020]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 80250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 80200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478264495098087, 362478361137727178⟩, ⟨541543852190737677, 546782156209452791⟩, true⟩

def words06 : List Nat := [371285173184880327, 371285173135583315, 371285173103982150, 371285173167846944, 371285173205643578, 371285173208418615, 371285173061261131, 371285172995004795, 371285172927374227, 371285172924898095]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 80260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 80200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490664702291780, 362490761370269203⟩, ⟨(-453888082651114485), (-448647743797185885)⟩, true⟩

def words07 : List Nat := [371285172842134157, 371285172758207902, 371285172741243351, 371285172748922211, 371285172779220517, 371285172810593874, 371285172841026206, 371285172843821699, 371285172829854492, 371285172902963151]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 80270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 80200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486665308785136, 362486762001510607⟩, ⟨(-132795860322869419), (-127553534567450057)⟩, true⟩

def words08 : List Nat := [371285173102613351, 371285173113411858, 371285173115522694, 371285173096521453, 371285173102073899, 371285173105132539, 371285173158123902, 371285173264266765, 371285173338294615, 371285173361008341]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 80280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 80200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497017433184205, 362497114150950819⟩, ⟨(-964017312756746701), (-958772976319993219)⟩, true⟩

def words09 : List Nat := [371285173480722399, 371285173601837811, 371285173831684439, 371285173901532631, 371285173940537627, 371285173980430435, 371285174083345118, 371285174109631480, 371285174260207458, 371285174412014567]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 80290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 80200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 80200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk802B
