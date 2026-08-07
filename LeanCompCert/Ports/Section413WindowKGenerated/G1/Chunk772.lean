import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk772

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362481460629707736, 362481549753742223⟩, ⟨277427026004751702, 282073273239693352⟩, true⟩

def state01 : KState := ⟨⟨362481175267394789, 362481264415272615⟩, ⟨299494990367839013, 304143078435128805⟩, true⟩

def words00 : List Nat := [371285203627412835, 371285203667439097, 371285203741201747, 371285203815989891, 371285203863048482, 371285203865711477, 371285203689043668, 371285203624980690, 371285203579394719, 371285203582199634]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 77200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 77200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362481900354638822, 362481989526785701⟩, ⟨243538171893014735, 248188133888615241⟩, true⟩

def words01 : List Nat := [371285203533193618, 371285203470178585, 371285203507817025, 371285203544123219, 371285203630630645, 371285203718200260, 371285203771889150, 371285203774552630, 371285203604615004, 371285203566333599]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 77210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 77200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362471770095095655, 362471859290923164⟩, ⟨1025853688527477969, 1030505479265010551⟩, true⟩

def words02 : List Nat := [371285203586464924, 371285203589128505, 371285203427677888, 371285203267310612, 371285203105854005, 371285202996322597, 371285202809598423, 371285202747827166, 371285202685199589, 371285202622261569]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 77220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 77200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485812073910581, 362485901293880203⟩, ⟨(-58746248798122782), (-54092593443004508)⟩, true⟩

def words03 : List Nat := [371285202451346073, 371285202261081194, 371285202069412880, 371285201987666566, 371285201740441118, 371285201478097661, 371285201214700955, 371285201119987277, 371285200972459946, 371285200984543931]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 77230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 77200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485122730776804, 362485211974768318⟩, ⟨(-5532544616325722), (-877033688900826)⟩, true⟩

def words04 : List Nat := [371285200995719295, 371285200998401574, 371285200884414084, 371285200913403742, 371285200947964621, 371285200950641751, 371285200824688212, 371285200701513206, 371285200618538249, 371285200621728372]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 77240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 77200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362475137271223410, 362475226539214642⟩, ⟨765959262904747662, 770616627931371172⟩, true⟩

def words05 : List Nat := [371285200766962929, 371285200913306293, 371285201025476133, 371285201028146674, 371285200977052362, 371285200978541081, 371285201095509698, 371285201098174383, 371285200993952373, 371285200867818466]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 77250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 77200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362498073707243885, 362498162999067415⟩, ⟨(-1006191467242774525), (-1001532260810030961)⟩, true⟩

def words06 : List Nat := [371285200778802948, 371285200781739859, 371285200878641603, 371285201012815582, 371285201094164053, 371285201096875540, 371285201146065844, 371285201256594196, 371285201533116830, 371285201703616211]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 77260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 77200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491195605337342, 362491284921520446⟩, ⟨(-474690030473968911), (-470028941663055695)⟩, true⟩

def words07 : List Nat := [371285201864027792, 371285202025372434, 371285202229827009, 371285202358566820, 371285202494821232, 371285202632054152, 371285202768506412, 371285202771171780, 371285202763073385, 371285202845180039]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 77270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 77200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482440109849350, 362482529449743425⟩, ⟨202017093805729497, 206680015125348993⟩, true⟩

def words08 : List Nat := [371285203079913698, 371285203144081435, 371285203210415621, 371285203277604074, 371285203342114181, 371285203349553095, 371285203409849181, 371285203471220500, 371285203531795137, 371285203534555501]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 77280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 77200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362502708681257630, 362502798045229181⟩, ⟨(-1364614783448658592), (-1359950001057379396)⟩, true⟩

def words09 : List Nat := [371285203634424331, 371285203770277064, 371285204034753850, 371285204160986641, 371285204259684647, 371285204359245407, 371285204544671639, 371285204669233709, 371285204898645517, 371285205129211829]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 77290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 77200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 77200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk772
