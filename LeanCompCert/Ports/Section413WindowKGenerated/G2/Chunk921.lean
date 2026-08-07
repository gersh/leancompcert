import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk921

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360570127386982691, 360570183243540002⟩, ⟨1082453426420276780, 1085927276266008162⟩, true⟩

def state01 : KState := ⟨⟨360572106329108200, 360572162198208804⟩, ⟨900126118386698742, 903601123531315878⟩, true⟩

def words00 : List Nat := [360581973857925221, 360581973803548911, 360581973631444892, 360581973370860759, 360581973110069207, 360581972785170230, 360581972570243906, 360581972473294544, 360581972376201966, 360581972220177443]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 92100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 92100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360600969729272771, 360601025610964346⟩, ⟨(-1758664424206616848), (-1755188259246986364)⟩, true⟩

def words01 : List Nat := [360581972125959411, 360581972138637821, 360581972148326061, 360581972177488445, 360581972178730319, 360581972097316663, 360581972029877993, 360581972120503574, 360581972328413620, 360581972536646363]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 92110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 92100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360582377485524563, 360582433379892099⟩, ⟨(-45962191373178944), (-42484858642238150)⟩, true⟩

def words02 : List Nat := [360581972685549012, 360581972717035880, 360581972788104289, 360581972859574731, 360581972860698583, 360581972847346054, 360581972747475588, 360581972544999458, 360581972342272379, 360581972244566940]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 92120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 92100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360570554875700007, 360570610782614655⟩, ⟨1043311342609032397, 1046789831368853671⟩, true⟩

def words03 : List Nat := [360581972245651318, 360581972236184891, 360581972226584464, 360581972142271333, 360581972060518702, 360581971949711957, 360581971838506274, 360581971829661109, 360581971766605445, 360581971644687250]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 92130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 92100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581414818768377, 360581470738278401⟩, ⟨42606342703806073, 46085992064643211⟩, true⟩

def words04 : List Nat := [360581971522484370, 360581971398098635, 360581971383495018, 360581971435798599, 360581971437027463, 360581971389163070, 360581971223567235, 360581971076370070, 360581970928759507, 360581970857562879]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 92140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 92100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360587546761263138, 360587602693468313⟩, ⟨(-522504506122127952), (-519023686838267666)⟩, true⟩

def words05 : List Nat := [360581970853335096, 360581970789295187, 360581970777216285, 360581970889778423, 360581970920423309, 360581970951265595, 360581970952461776, 360581970894579949, 360581970924498307, 360581970987140927]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 92150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 92100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590260472054427, 360590316416830349⟩, ⟨(-772591742147848013), (-769109764282748241)⟩, true⟩

def words06 : List Nat := [360581971104839678, 360581971266011083, 360581971360519700, 360581971455170870, 360581971520203689, 360581971644444308, 360581971781610472, 360581971919028628, 360581971945830293, 360581972037749264]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 92160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 92100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360623254216167386, 360623310173519430⟩, ⟨(-3813824596463342405), (-3810341459394178483)⟩, true⟩

def words07 : List Nat := [360581972212889345, 360581972388417050, 360581972681080425, 360581972934341627, 360581973086991247, 360581973239763056, 360581973509776167, 360581973842177384, 360581974291685375, 360581974741495541]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 92170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 92100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360603015376518590, 360603071346572405⟩, ⟨(-1948244635194181301), (-1944760327212458757)⟩, true⟩

def words08 : List Nat := [360581975132088142, 360581975405419769, 360581975629108563, 360581975853162247, 360581976030411051, 360581976090480562, 360581976091765696, 360581976093188054, 360581976211852116, 360581976442219351]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 92180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 92100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360564944046976310, 360565000029580360⟩, ⟨1561755547426755646, 1565241012476603172⟩, true⟩

def words09 : List Nat := [360581976608782132, 360581976775586384, 360581976877038756, 360581976908661764, 360581976910683857, 360581976913080484, 360581976914176939, 360581976913829852, 360581976795977629, 360581976613229781]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 92190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 92100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 92100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk921
