import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk088

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360342366809818335, 360342367225649189⟩, ⟨2049268921078103008, 2049271402005211754⟩, true⟩

def state01 : KState := ⟨⟨360710089691053534, 360710090107876356⟩, ⟨(-1188624813913410492), (-1188622324252020152)⟩, true⟩

def words00 : List Nat := [360575212516270557, 360575189732830138, 360575174130343657, 360575171320162260, 360575168510610848, 360575154429263393, 360575154461604210, 360575160868057597, 360575172704333749, 360575188016825168]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 8800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 8800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360564364827917833, 360564365245745449⟩, ⟨95648096229086931, 95650594747526793⟩, true⟩

def words01 : List Nat := [360575193293209231, 360575198568405939, 360575203365715378, 360575216140345104, 360575221292395581, 360575226443294708, 360575226443388559, 360575225191577817, 360575211213957817, 360575209984378956]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 8810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 8800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360520813511084613, 360520813929904441⟩, ⟨480376846616123500, 480379353890967346⟩, true⟩

def words02 : List Nat := [360575220267866976, 360575230288532210, 360575231145815714, 360575232002916235, 360575232003004709, 360575232774840581, 360575232774927907, 360575229699390849, 360575226624539912, 360575217027740338]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 8820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 8800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360832720873692364, 360832721293508696⟩, ⟨(-2275711061511448844), (-2275708545432501812)⟩, true⟩

def words03 : List Nat := [360575217428702771, 360575223988678674, 360575230707894257, 360575238028273712, 360575238028371204, 360575235332973290, 360575242648266268, 360575259075253077, 360575288200024028, 360575317318230730]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 8830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 8800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360673309860062532, 360673310280886069⟩, ⟨(-867033976964088164), (-867031451976446684)⟩, true⟩

def words04 : List Nat := [360575336388945381, 360575342811996231, 360575355665366118, 360575368515860835, 360575374446626446, 360575374446732196, 360575367738455898, 360575354472037214, 360575341208595193, 360575351694062383]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 8840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 8800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360431807095952557, 360431807517773231⟩, ⟨1271870468462819961, 1271873002280145709⟩, true⟩

def words05 : List Nat := [360575370363700944, 360575389029141807, 360575399067893632, 360575404437655399, 360575404437746369, 360575396951717798, 360575389467348249, 360575385820949773, 360575375979372673, 360575359775366927]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 8850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 8800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360834983294221900, 360834983717044552⟩, ⟨(-2301742559470679387), (-2301740016770823209)⟩, true⟩

def words06 : List Nat := [360575343574994990, 360575346349168033, 360575365315851076, 360575384278275176, 360575392682670580, 360575406919974970, 360575433780846010, 360575460635690377, 360575486533533457, 360575515785946500]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 8860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 8800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360773617861139353, 360773618284972591⟩, ⟨(-1756986523951229419), (-1756983972282501235)⟩, true⟩

def words07 : List Nat := [360575538691780332, 360575561592462710, 360575589789159905, 360575627980893209, 360575661525761525, 360575695063090969, 360575718724014795, 360575737445449874, 360575759729414674, 360575782008395348]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 8870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 8800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360813488224955176, 360813488649789591⟩, ⟨(-2111916683813565553), (-2111914123249318403)⟩, true⟩

def words08 : List Nat := [360575812584772765, 360575830625784912, 360575838663010943, 360575846698436859, 360575851509942605, 360575862795192905, 360575886640062488, 360575910479587851, 360575928005892809, 360575954725231126]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 8880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 8800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360772090858934244, 360772091284772509⟩, ⟨(-1743568182822626073), (-1743565613329145757)⟩, true⟩

def words09 : List Nat := [360575985297172557, 360576015862270722, 360576058963739667, 360576089555279230, 360576109081801154, 360576128603942059, 360576142590430125, 360576163021475203, 360576185035973664, 360576207045548923]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 8890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 8800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 8800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk088
