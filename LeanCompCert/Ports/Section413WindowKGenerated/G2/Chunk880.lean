import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk880

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360574176136579600, 360574226950635168⟩, ⟨696463275668889983, 699482963228790827⟩, true⟩

def state01 : KState := ⟨⟨360601888642319857, 360601939468333485⟩, ⟨(-1742334975731622753), (-1739314235802294589)⟩, true⟩

def words00 : List Nat := [360582175570027804, 360582175675432889, 360582175909426035, 360582176143679410, 360582176268197835, 360582176300173669, 360582176460874584, 360582176621947332, 360582176778277119, 360582177004143756]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 88000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 88000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360607260840727550, 360607311678834077⟩, ⟨(-2215222575857472599), (-2212200771572767183)⟩, true⟩

def words01 : List Nat := [360582177108988469, 360582177213930826, 360582177427981566, 360582177707263548, 360582177926233415, 360582178145404355, 360582178299809976, 360582178457706755, 360582178744271427, 360582179031266193]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 88010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 88000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594830235048037, 360594881085093210⟩, ⟨(-1121040989014336688), (-1118018133830813806)⟩, true⟩

def words02 : List Nat := [360582179324420855, 360582179598442846, 360582179769577008, 360582179940839540, 360582180023317134, 360582180195747878, 360582180372521004, 360582180549530835, 360582180661948852, 360582180807533819]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 88020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 88000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360598314416450260, 360598365278480703⟩, ⟨(-1427797765780683624), (-1424773855474687568)⟩, true⟩

def words03 : List Nat := [360582181041026043, 360582181274909622, 360582181492443865, 360582181581315446, 360582181582485042, 360582181561876175, 360582181648028292, 360582181836335754, 360582182021197964, 360582182206327108]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 88030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 88000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593570763640063, 360593621637750750⟩, ⟨(-1010247112221105764), (-1007222138311985744)⟩, true⟩

def words04 : List Nat := [360582182326677391, 360582182327945697, 360582182353288310, 360582182388671082, 360582182391290153, 360582182441400461, 360582182442542160, 360582182427666984, 360582182429734049, 360582182561098447]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 88040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 88000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk880
