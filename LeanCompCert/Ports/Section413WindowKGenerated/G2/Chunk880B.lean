import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk880A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk880B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk880A

def state06 : KState := ⟨⟨360567085002285930, 360567135888352619⟩, ⟨1322003945988938346, 1325029972683864106⟩, true⟩

def words05 : List Nat := [360582182798534046, 360582183036207437, 360582183171716257, 360582183178488761, 360582183179557389, 360582183102867641, 360582183054828905, 360582183056097380, 360582182957415933, 360582182787883438]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 88050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 88000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360591059884096552, 360591110782131014⟩, ⟨(-789320617562123939), (-786293536925721355)⟩, true⟩

def words06 : List Nat := [360582182618039793, 360582182562205663, 360582182675033117, 360582182788101631, 360582182792528771, 360582182793805978, 360582182778702489, 360582182719745001, 360582182728848481, 360582182831535180]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 88060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 88000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360586605806493132, 360586656716611569⟩, ⟨(-397034502271677402), (-394006357341703806)⟩, true⟩

def words07 : List Nat := [360582182861214566, 360582182891031067, 360582182990900093, 360582183193626953, 360582183322996137, 360582183452563220, 360582183461701164, 360582183462970392, 360582183436810901, 360582183489044424]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 88070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 88000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579158315671472, 360579209237754022⟩, ⟨258900349032451457, 261929547820836023⟩, true⟩

def words08 : List Nat := [360582183537827083, 360582183539095943, 360582183459205426, 360582183315119939, 360582183170827849, 360582182972348727, 360582182847047527, 360582182809220428, 360582182771218604, 360582182668879245]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 88080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 88000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360599131328078688, 360599182262130230⟩, ⟨(-1500605301406041195), (-1497575048208147307)⟩, true⟩

def words09 : List Nat := [360582182705600098, 360582182776459356, 360582182975642543, 360582183132667950, 360582183166940412, 360582183201290438, 360582183310643916, 360582183485128328, 360582183679109815, 360582183873369511]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 88090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 88000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 88000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk880B
