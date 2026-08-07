import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk048

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360373352108956342, 360373352225080739⟩, ⟨992059876628534155, 992060255096573507⟩, true⟩

def state01 : KState := ⟨⟨360385194212188785, 360385194328822589⟩, ⟨935822601734001531, 935822982649733401⟩, true⟩

def words00 : List Nat := [360579988395734096, 360579989016258204, 360579989016306349, 360579967997776706, 360579946987987004, 360579908810061819, 360579894182338409, 360579858381616804, 360579822595779261, 360579752121473262]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 4800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 4800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360870408277487843, 360870408394632395⟩, ⟨(-1401234163537068342), (-1401233780162072364)⟩, true⟩

def words01 : List Nat := [360579711681319261, 360579684119307165, 360579671720145620, 360579671720199794, 360579670117152694, 360579631935362448, 360579598256884334, 360579635665716916, 360579695992053165, 360579756293374965]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 4810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 4800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360453472019951207, 360453472137613294⟩, ⟨608389792689057627, 608390178561135639⟩, true⟩

def words02 : List Nat := [360579794979428877, 360579794979483085, 360579791147221764, 360579765050830718, 360579738965242215, 360579700301165032, 360579648249312418, 360579574725065462, 360579501231259561, 360579432837108354]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 4820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 4800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360109180954264803, 360109181072438715⟩, ⟨2274076542934241076, 2274076931281037954⟩, true⟩

def words03 : List Nat := [360579423063810684, 360579439357199524, 360579439357248443, 360579433483790076, 360579385337728672, 360579325626784327, 360579265940514000, 360579204589428317, 360579128774651381, 360579031678075294]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 4830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 4800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360250236626188355, 360250236744876893⟩, ⟨1591021861653792380, 1591022252493945128⟩, true⟩

def words04 : List Nat := [360578934621601056, 360578860212183581, 360578808241493690, 360578775231604411, 360578742235336590, 360578669986706362, 360578555700517446, 360578461060998892, 360578366460499485, 360578282570133377]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 4840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 4800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360218747871399652, 360218747990609715⟩, ⟨1743108386822054037, 1743108780194210433⟩, true⟩

def words05 : List Nat := [360578214945812332, 360578107780456792, 360578000659255611, 360577910359602563, 360577842139349416, 360577762697103109, 360577683287563383, 360577582920320533, 360577486163050400, 360577412348674368]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 4850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 4800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360450661386309143, 360450661506035339⟩, ⟨615669554362470229, 615669950245690043⟩, true⟩

def words06 : List Nat := [360577338564650067, 360577306489417175, 360577299729513775, 360577272085465817, 360577244452774124, 360577186406742662, 360577150212454229, 360577135054086408, 360577119901939548, 360577082440377370]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 4860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 4800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360481974377656270, 360481974497901689⟩, ⟨463462791115795825, 463463189530192683⟩, true⟩

def words07 : List Nat := [360577072051196316, 360577087609438785, 360577108461978095, 360577108462033022, 360577087768858254, 360577031093313941, 360576974441001159, 360576965928324163, 360576965928369606, 360576946462969352]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 4870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 4800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360493347384850383, 360493347505619654⟩, ⟨405537177792254888, 405537578765671008⟩, true⟩

def words08 : List Nat := [360576927005537316, 360576886814463726, 360576805204284758, 360576739280646480, 360576673383983714, 360576596445036091, 360576522862813483, 360576427981075893, 360576333138142051, 360576279525817133]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 4880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 4800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨359970420367374555, 359970420488664216⟩, ⟨2965798204837101613, 2965798608357862005⟩, true⟩

def words09 : List Nat := [360576268157453832, 360576273742862852, 360576273742912797, 360576246138890223, 360576177287938388, 360576078586239240, 360575979924834673, 360575903361082210, 360575809059407854, 360575685510778066]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 4890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 4800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 4800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk048
