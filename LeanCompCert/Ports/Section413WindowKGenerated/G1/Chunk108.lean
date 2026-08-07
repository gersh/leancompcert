import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk108

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362525686780329822, 362525688259134461⟩, ⟨(-426719736591142221), (-426708924749237361)⟩, true⟩

def state01 : KState := ⟨⟨362496230917584408, 362496232399223686⟩, ⟨(-108445076566876019), (-108434234096003023)⟩, true⟩

def words00 : List Nat := [371286188962346956, 371286188962666811, 371286188558127362, 371286188078931545, 371286189689338254, 371286189689688211, 371286192177254417, 371286196827821321, 371286201479921348, 371286202408094651]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 10800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 10800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362554159314080603, 362554160798594484⟩, ⟨(-735003314998994089), (-734992441439043653)⟩, true⟩

def words01 : List Nat := [371286209320373917, 371286216231535155, 371286227392100201, 371286227392418527, 371286227179822932, 371286224734468811, 371286225983424630, 371286225983778316, 371286231737109276, 371286238014984925]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 10810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 10800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362450115519475969, 362450117006867979⟩, ⟨391371574228884590, 391382478945000774⟩, true⟩

def words02 : List Nat := [371286244262138319, 371286244262462322, 371286249874126192, 371286256254033035, 371286265128327578, 371286265128646243, 371286262659796381, 371286260075725382, 371286257492011352, 371286255739919226]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 10820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 10800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362384918332323177, 362384919822587927⟩, ⟨1098195400666049424, 1098206336508763530⟩, true⟩

def words03 : List Nat := [371286257579199192, 371286262754257934, 371286267062714107, 371286267063032881, 371286260044102730, 371286253538428703, 371286249035194688, 371286249035513555, 371286239716729708, 371286230370236337]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 10830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 10800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362516514821431961, 362516516314559837⟩, ⟨(-328930528309272497), (-328919561415835645)⟩, true⟩

def words04 : List Nat := [371286221025324153, 371286218271824950, 371286212353939527, 371286209912834017, 371286207472085304, 371286203621590690, 371286195156360168, 371286195166928428, 371286201147272638, 371286203941376183]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 10840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 10800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362537193225855773, 362537194721887547⟩, ⟨(-553246076775041167), (-553235078359370423)⟩, true⟩

def words05 : List Nat := [371286206718650879, 371286209495517762, 371286220745531414, 371286228125167124, 371286236847315581, 371286245567980909, 371286251349832270, 371286251350151863, 371286252264925656, 371286256955718744]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 10850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 10800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492489343830760, 362492490842712874⟩, ⟨(-67411255877917301), (-67400226492796031)⟩, true⟩

def words06 : List Nat := [371286270111197800, 371286271994377716, 371286272665848917, 371286273337310705, 371286275027181046, 371286275027533025, 371286278427384250, 371286284356151400, 371286290269567505, 371286290840275859]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 10860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 10800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362533648606641694, 362533650108425038⟩, ⟨(-514968342202866071), (-514957281267170257)⟩, true⟩

def words07 : List Nat := [371286294880434460, 371286298920016712, 371286310176451587, 371286310186631638, 371286310186880198, 371286308701039267, 371286312673429181, 371286315124729583, 371286319475591151, 371286323825797783]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 10870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 10800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362463255510063162, 362463257014735915⟩, ⟨250907909506324071, 250919001893748485⟩, true⟩

def words08 : List Nat := [371286328313523910, 371286328313844113, 371286323263523057, 371286324954031244, 371286326995323685, 371286326995644019, 371286317815399745, 371286308482510526, 371286299151203557, 371286298245396498]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 10880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 10800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362412508169298281, 362412509676856931⟩, ⟨804406773865056670, 804417897694807174⟩, true⟩

def words09 : List Nat := [371286302436849128, 371286308742897228, 371286315033493634, 371286315033815626, 371286314347546548, 371286315259535740, 371286321355923948, 371286321356244558, 371286316254873725, 371286309483984895]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 10890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 10800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 10800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk108
