import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk191

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588036772501706, 360588038881281500⟩, ⟨(-63939424534138624), (-63912163806532158)⟩, true⟩

def state01 : KState := ⟨⟨360511784372750740, 360511786483856807⟩, ⟨1392324422684277007, 1392351727854923535⟩, true⟩

def words00 : List Nat := [360584692870095948, 360584691682883329, 360584687763793771, 360584683776616857, 360584679789793118, 360584675113877259, 360584669018221688, 360584660833768247, 360584652650124254, 360584646333561408]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 19100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 19100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360443503178328141, 360443505291731477⟩, ⟨2697648650016595315, 2697675999099643741⟩, true⟩

def words01 : List Nat := [360584642521302961, 360584640153853115, 360584637786624660, 360584633649758755, 360584628401651344, 360584622467057687, 360584616533014407, 360584610533901193, 360584604512102263, 360584597132688572]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 19110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 19100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360481648513976519, 360481650629684389⟩, ⟨1968403820618147455, 1968431213775379907⟩, true⟩

def words02 : List Nat := [360584589753991785, 360584585093275042, 360584581824301130, 360584579323878102, 360584576823696152, 360584571690108785, 360584564845371857, 360584559585711488, 360584554326531388, 360584548236259161]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 19120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 19100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360481136597472649, 360481138715511291⟩, ⟨1977923284674824964, 1977950722431290822⟩, true⟩

def words03 : List Nat := [360584542857900895, 360584535343002746, 360584527828844000, 360584520937885498, 360584515417397923, 360584508541215013, 360584501665722596, 360584493435193509, 360584485322808737, 360584479923579802]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 19130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 19100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360492681084046017, 360492683204384476⟩, ⟨1756983147610020753, 1757010629396849381⟩, true⟩

def words04 : List Nat := [360584474524832599, 360584471838640863, 360584468353252622, 360584463481135669, 360584458609491371, 360584451796942733, 360584446370894997, 360584442523221123, 360584438675923431, 360584433106702850]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 19140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 19100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360512417491366285, 360512419614017245⟩, ⟨1378942820646174621, 1378970346728843855⟩, true⟩

def words05 : List Nat := [360584428316034734, 360584423936666601, 360584419557677060, 360584417162866919, 360584413139280828, 360584406767954086, 360584400397245883, 360584396734739347, 360584394682751381, 360584390926476997]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 19150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 19100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360608098067833295, 360608100192816428⟩, ⟨(-455011774634403646), (-454984203855926590)⟩, true⟩

def words06 : List Nat := [360584387170561513, 360584382030897314, 360584378062385924, 360584376800414258, 360584375538509883, 360584373590981263, 360584372350328998, 360584369756783477, 360584367163462048, 360584367252236598]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 19160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 19100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360478110485120826, 360478112612414219⟩, ⟨2037557520430546529, 2037585135508251121⟩, true⟩

def words07 : List Nat := [360584369635836530, 360584372019234139, 360584372019457487, 360584371924759530, 360584369121663156, 360584364512362628, 360584359903470778, 360584357197604168, 360584353038430407, 360584347499562721]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 19170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 19100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596097819800737, 360596099949406799⟩, ⟨(-225849829606450068), (-225822170160301262)⟩, true⟩

def words08 : List Nat := [360584341961213172, 360584339123334724, 360584339634326328, 360584341239630512, 360584341239856374, 360584340506508884, 360584338093713377, 360584335617778854, 360584333142027412, 360584332862222166]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 19180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 19100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360574793570112034, 360574795702051713⟩, ⟨183043721785884235, 183071426025961653⟩, true⟩

def words09 : List Nat := [360584332862440588, 360584332126903715, 360584331565750931, 360584333819574308, 360584334217283675, 360584334614990244, 360584334615210964, 360584333533023645, 360584331168516555, 360584330672157232]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 19190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 19100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 19100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk191
