import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk248

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362560050776139741, 362560059163337941⟩, ⟨(-1841992562821812651), (-1841851929749780881)⟩, true⟩

def state01 : KState := ⟨⟨362502714107503831, 362502722501770928⟩, ⟨(-419959680789600859), (-419818872372512349)⟩, true⟩

def words00 : List Nat := [371285796621300364, 371285797142676371, 371285798672396520, 371285800202400258, 371285801598134664, 371285801598917546, 371285801085011665, 371285800563252438, 371285801143669007, 371285801826571520]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 24800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 24800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362457080250408239, 362457088651717647⟩, ⟨712660703433115788, 712801686605430268⟩, true⟩

def words01 : List Nat := [371285803806182042, 371285805785942977, 371285807745085307, 371285808035927748, 371285808410765656, 371285808785966119, 371285809799246286, 371285809800029496, 371285808651109705, 371285807494852435]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 24810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 24800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362466722540114886, 362466730948442039⟩, ⟨473531865895165995, 473673023284137195⟩, true⟩

def words02 : List Nat := [371285806804904871, 371285806805790493, 371285807984178960, 371285809267356572, 371285810266514042, 371285810267297433, 371285809105591500, 371285808379327046, 371285807652734728, 371285807590539669]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 24820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 24800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362479213312328985, 362479221727811847⟩, ⟨163348566197944172, 163489901298224346⟩, true⟩

def words03 : List Nat := [371285806822872804, 371285806033667509, 371285805636288881, 371285805637151998, 371285805295919405, 371285805369180730, 371285805369768772, 371285805260439439, 371285803710853180, 371285803446865721]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 24830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 24800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362469395283681446, 362469403706154601⟩, ⟨407316613613013403, 407458122388492369⟩, true⟩

def words04 : List Nat := [371285804538126840, 371285804538910835, 371285803737245940, 371285802686420625, 371285801635387994, 371285801071510218, 371285800100994569, 371285800426209040, 371285800426805149, 371285800411280899]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 24840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 24800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362526945914623054, 362526954344174086⟩, ⟨(-1023042331713452933), (-1022900647016720697)⟩, true⟩

def words05 : List Nat := [371285800711578665, 371285801671997865, 371285803820108352, 371285804493915651, 371285804925163961, 371285805356631744, 371285806203990304, 371285806241591144, 371285807897317097, 371285809553255913]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 24850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 24800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480391455727579, 362480399892353137⟩, ⟨134447728669528285, 134589589274821097⟩, true⟩

def words06 : List Nat := [371285811201430746, 371285811202215920, 371285811874298581, 371285812692590042, 371285813995978820, 371285813996763476, 371285813146319729, 371285812281368851, 371285811615997341, 371285811616891731]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 24860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 24800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362441162488259392, 362441170931965098⟩, ⟨1110213093016777301, 1110355129742311827⟩, true⟩

def words07 : List Nat := [371285811399848518, 371285810971005200, 371285810541925618, 371285810106596712, 371285807518893910, 371285805451980625, 371285803384828550, 371285802933703109, 371285801146505974, 371285799353578535]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 24870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 24800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362503422284281513, 362503430735015562⟩, ⟨(-439020163595464015), (-438877951969514235)⟩, true⟩

def words08 : List Nat := [371285797560437077, 371285797201805034, 371285797218808368, 371285797899482809, 371285798262168300, 371285798262954894, 371285796903956190, 371285796742523520, 371285798032233367, 371285798741444813]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 24880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 24800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476016652875068, 362476025110768650⟩, ⟨243331848161262912, 243474238023948294⟩, true⟩

def words09 : List Nat := [371285799444344304, 371285800147459198, 371285801507703593, 371285802079665674, 371285802938678066, 371285803797929699, 371285804636682285, 371285804637468342, 371285803584362503, 371285803192617002]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 24890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 24800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 24800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk248
