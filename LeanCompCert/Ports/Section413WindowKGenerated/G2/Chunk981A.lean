import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk981A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360604700932841693, 360604764615290713⟩, ⟨(-2193781293044900054), (-2189562936666506820)⟩, true⟩

def state01 : KState := ⟨⟨360593555467910038, 360593619163761044⟩, ⟨(-1100337906578848525), (-1096118235396391143)⟩, true⟩

def words00 : List Nat := [360582445471584071, 360582445720845154, 360582445910860122, 360582446101026526, 360582446220452434, 360582446395120178, 360582446564130461, 360582446733406370, 360582446822713850, 360582446938063657]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 98100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 98100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360595779608904204, 360595843318231645⟩, ⟨(-1318573097202119662), (-1314352103782110926)⟩, true⟩

def words01 : List Nat := [360582447083914349, 360582447230202829, 360582447438509761, 360582447543516220, 360582447560978174, 360582447578552751, 360582447666982786, 360582447825365077, 360582447963058914, 360582448101063230]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 98110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 98100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360607396857915672, 360607460580804388⟩, ⟨(-2458616454962222953), (-2454394130843322579)⟩, true⟩

def words02 : List Nat := [360582448186786071, 360582448198411796, 360582448313566047, 360582448429149320, 360582448511177013, 360582448626507336, 360582448689684327, 360582448753003730, 360582448919840195, 360582449176346640]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 98120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 98100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360575917534376600, 360575981270706104⟩, ⟨630632100016995410, 634855743148142032⟩, true⟩

def words03 : List Nat := [360582449445776842, 360582449715466955, 360582449905083274, 360582450013607164, 360582450073631868, 360582450134047599, 360582450224862581, 360582450226288125, 360582450213692968, 360582450149279043]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 98130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 98100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590548236670868, 360590611986453522⟩, ⟨(-805313230071439321), (-801088266582350471)⟩, true⟩

def words04 : List Nat := [360582450084522021, 360582450006296428, 360582450110455251, 360582450215264816, 360582450231259031, 360582450232685786, 360582450185990368, 360582450135762666, 360582450107571094, 360582450192212177]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 98140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 98100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk981A
