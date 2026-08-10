import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk991A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk991B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk991A

def state06 : KState := ⟨⟨362485779667340870, 362485929570213037⟩, ⟨(-66975370990991398), (-56939813990655296)⟩, true⟩

def words05 : List Nat := [371285354845566285, 371285354974518551, 371285355095650417, 371285355126463376, 371285355162340036, 371285355199860434, 371285355326873402, 371285355336266387, 371285355344661228, 371285355354402480]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 99150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 99100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486876059852298, 362487025993974854⟩, ⟨(-175673861578283550), (-165635205631136964)⟩, true⟩

def words06 : List Nat := [371285355404261220, 371285355418822152, 371285355518892117, 371285355620365654, 371285355687885990, 371285355691371062, 371285355666745968, 371285355703753234, 371285355775525937, 371285355795977142]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 99160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 99100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490725195970855, 362490875161852090⟩, ⟨(-557393296153419644), (-547351490546076092)⟩, true⟩

def words07 : List Nat := [371285355815305009, 371285355835752171, 371285355956531619, 371285356028005399, 371285356129558475, 371285356232573877, 371285356333309182, 371285356336804109, 371285356388709270, 371285356448685798]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 99170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 99100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485250330603732, 362485400327553008⟩, ⟨(-14360956908250923), (-4316069811907739)⟩, true⟩

def words08 : List Nat := [371285356608401233, 371285356643282248, 371285356657488025, 371285356672872210, 371285356713253178, 371285356717095575, 371285356744056207, 371285356780144565, 371285356810708400, 371285356814837017]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 99180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 99100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492249408125888, 362492399436613125⟩, ⟨(-708604925482008921), (-698556909980835455)⟩, true⟩

def words09 : List Nat := [371285356919336985, 371285357025675488, 371285357223965371, 371285357287897464, 371285357324153149, 371285357361455663, 371285357424500790, 371285357454941525, 371285357528301434, 371285357603264865]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 99190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 99100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 99100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk991B
