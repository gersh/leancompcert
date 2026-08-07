import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk259

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362454283745748076, 362454292926733691⟩, ⟨810044138770424644, 810204897812469316⟩, true⟩

def state01 : KState := ⟨⟨362457489026836717, 362457498215156723⟩, ⟨727196720892430581, 727357669933293623⟩, true⟩

def words00 : List Nat := [371285573764065368, 371285573764976789, 371285573761638846, 371285574504989076, 371285574762963783, 371285574763783855, 371285573037417620, 371285571929639175, 371285570821532251, 371285570684085064]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 25900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 25900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476752349349902, 362476761545161074⟩, ⟨228056111966528446, 228217255139079942⟩, true⟩

def words01 : List Nat := [371285569601285686, 371285568532948856, 371285567882819503, 371285567883738543, 371285567996483342, 371285568231105797, 371285568387349279, 371285568388169915, 371285566561876362, 371285566223214280]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 25910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 25900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362427363713415518, 362427372916544678⟩, ⟨1508502957481009863, 1508664290374112483⟩, true⟩

def words02 : List Nat := [371285565940405803, 371285565941230331, 371285564592425974, 371285563236432035, 371285561880239486, 371285560578187255, 371285558680989609, 371285557545593306, 371285556409992254, 371285555110542909]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 25920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 25900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362505400077214834, 362505409287755083⟩, ⟨(-515365730309158300), (-515204205208491076)⟩, true⟩

def words03 : List Nat := [371285552867369495, 371285552110421367, 371285552080836619, 371285552081657714, 371285550829847449, 371285549457116626, 371285548084148832, 371285547859456494, 371285547906532388, 371285548673083001]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 25930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 25900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475811228250657, 362475820446210403⟩, ⟨252404602370276424, 252566319970448030⟩, true⟩

def words04 : List Nat := [371285549432072566, 371285549432910425, 371285550639470409, 371285551985526897, 371285553781077085, 371285553781898680, 371285553599066191, 371285553439866614, 371285553280363314, 371285553252374968]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 25940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 25900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362454258250008138, 362454267475378673⟩, ⟨812027016781835685, 812188926729113971⟩, true⟩

def words05 : List Nat := [371285553986316851, 371285555095563025, 371285556065134999, 371285556065958544, 371285555518693548, 371285555231882471, 371285555883895936, 371285555884717846, 371285554847867109, 371285553643588578]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 25950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 25900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362468881050513080, 362468890283244903⟩, ⟨432338060680679785, 432500161765414261⟩, true⟩

def words06 : List Nat := [371285552439027881, 371285552200607310, 371285551226028968, 371285550867409875, 371285550508576977, 371285549873786140, 371285547263444320, 371285545722201290, 371285544180642054, 371285544120817696]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 25960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 25900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362471005183933178, 362471014424145090⟩, ⟨377181255565139245, 377343550945763583⟩, true⟩

def words07 : List Nat := [371285543480189791, 371285542556212701, 371285541775228669, 371285541776148316, 371285541428363611, 371285541481122825, 371285541481748955, 371285541247554208, 371285539368321471, 371285538810247699]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 25970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 25900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476829762902889, 362476839010443432⟩, ⟨225939698823291641, 226102184639361267⟩, true⟩

def words08 : List Nat := [371285539172833053, 371285539173661107, 371285538776257123, 371285538393257800, 371285538073901109, 371285538074807546, 371285537854953914, 371285538228286551, 371285538593455177, 371285538594307971]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 25980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 25900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362510890991332179, 362510900246336736⟩, ⟨(-659648136195365271), (-659485456352882191)⟩, true⟩

def words09 : List Nat := [371285538395799942, 371285538532429774, 371285539006413519, 371285539007236994, 371285537789289031, 371285536348929049, 371285534945691020, 371285534946613409, 371285535420151982, 371285536396625076]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 25990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 25900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 25900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk259
