import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk390

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362479848804043960, 362479870342990692⟩, ⟨206456646487285125, 207024300635958893⟩, true⟩

def state01 : KState := ⟨⟨362468310295195993, 362468331845510273⟩, ⟨656531627491774715, 657099725033110797⟩, true⟩

def words00 : List Nat := [371285178924211919, 371285178925488028, 371285178452057300, 371285177979368372, 371285177506203928, 371285177146805775, 371285176561262935, 371285176453347868, 371285176344987829, 371285176237333732]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 39000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 39000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484537969057019, 362484559530899234⟩, ⟨23349754254851617, 23918301561359739⟩, true⟩

def words01 : List Nat := [371285175806429302, 371285175647790702, 371285175763485363, 371285175764761849, 371285175165906080, 371285174396321933, 371285173626253355, 371285173191552035, 371285172520624601, 371285172506336481]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 39010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 39000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477194800155986, 362477216373514507⟩, ⟨309840761770145201, 310409758501924859⟩, true⟩

def words02 : List Nat := [371285172491582127, 371285172477717413, 371285171684101140, 371285171547163048, 371285171409587416, 371285171269173785, 371285170684907708, 371285170101740103, 371285169518086668, 371285169480317016]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 39020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 39000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362456106603024021, 362456128187910033⟩, ⟨1133141496585834482, 1133710943293090484⟩, true⟩

def words03 : List Nat := [371285169545145365, 371285169814281212, 371285170082358183, 371285170083636556, 371285169644381044, 371285169310368240, 371285169211919602, 371285169213197108, 371285168657352230, 371285167914941107]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 39030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 39000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362502802271829416, 362502823868144884⟩, ⟨(-690025280041785115), (-689455387069968379)⟩, true⟩

def words04 : List Nat := [371285167171981645, 371285167084903779, 371285166912112229, 371285167154283935, 371285167315028641, 371285167316328339, 371285167203049187, 371285167475088338, 371285168159076422, 371285168612528640]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 39040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 39000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362500742549291416, 362500764157256666⟩, ⟨(-609572144197810324), (-609001796244759274)⟩, true⟩

def words05 : List Nat := [371285169065248660, 371285169518362621, 371285170235006232, 371285170687208206, 371285171303943674, 371285171921152781, 371285172509156464, 371285172510434746, 371285172711810202, 371285173112576685]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 39050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 39000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362462003439678495, 362462025059013841⟩, ⟨903773147937762444, 904343940067251236⟩, true⟩

def words06 : List Nat := [371285173743961552, 371285173745239690, 371285173504005583, 371285173220866835, 371285172937243905, 371285172765853046, 371285172327723011, 371285172160924830, 371285171993725414, 371285171819701511]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 39060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 39000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362513059717749466, 362513081348658584⟩, ⟨(-1091255804993249641), (-1090684560619097379)⟩, true⟩

def words07 : List Nat := [371285171228141150, 371285171212422724, 371285171669054552, 371285171670355195, 371285171600735619, 371285171427018109, 371285171549124585, 371285171610663904, 371285172325701040, 371285173041281110]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 39070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 39000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362467771717937328, 362467793360387961⟩, ⟨678676978058597455, 679248673535532985⟩, true⟩

def words08 : List Nat := [371285173625971537, 371285173627250272, 371285173340054065, 371285173133560164, 371285172926459963, 371285172918881886, 371285172039425663, 371285171106293437, 371285170172648693, 371285169893351265]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 39080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 39000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362452716164655376, 362452737818607656⟩, ⟨1267333845434439541, 1267905990568660417⟩, true⟩

def words09 : List Nat := [371285169449709264, 371285169301610380, 371285169153098220, 371285168984340012, 371285168230721397, 371285167515783921, 371285166800194618, 371285166738613951, 371285165909724510, 371285165081793556]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 39090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 39000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 39000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk390
