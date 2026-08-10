import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk776A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk776B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk776A

def state06 : KState := ⟨⟨362499828832986396, 362499919063731276⟩, ⟨(-1147063932200846619), (-1142331992033593729)⟩, true⟩

def words05 : List Nat := [371285209320960227, 371285209384674749, 371285209532928859, 371285209535609063, 371285209491270692, 371285209427240114, 371285209442940774, 371285209469653123, 371285209660880357, 371285209853290597]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 77650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 77600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491583923436329, 362491674178345006⟩, ⟨(-506743492583527299), (-502009675731495205)⟩, true⟩

def words06 : List Nat := [371285210043858917, 371285210114581774, 371285210313333283, 371285210513507241, 371285210720485910, 371285210723165393, 371285210709358517, 371285210696463127, 371285210808763843, 371285210895063840]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 77660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 77600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472582998695805, 362472673277789626⟩, ⟨969185599034964282, 973921294470151548⟩, true⟩

def words07 : List Nat := [371285211028932156, 371285211163954446, 371285211276810657, 371285211279490722, 371285211192251799, 371285211134117504, 371285211166803623, 371285211169483434, 371285211042922792, 371285210884567049]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 77670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 77600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362501262947388016, 362501353250471772⟩, ⟨(-1258794634563771509), (-1254057075470048237)⟩, true⟩

def words08 : List Nat := [371285210729190717, 371285210732164131, 371285210777364090, 371285210875282583, 371285210945749132, 371285210948478015, 371285211026800530, 371285211151114618, 371285211439535796, 371285211650087300]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 77680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 77600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494121836609044, 362494212164114329⟩, ⟨(-703978614175446289), (-699239157653001605)⟩, true⟩

def words09 : List Nat := [371285211844757359, 371285212040296640, 371285212251830850, 371285212394088711, 371285212559188279, 371285212725348288, 371285212873195463, 371285212875876762, 371285212943802774, 371285213062974666]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 77690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 77600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 77600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk776B
