import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk033

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362195665789421692, 362195665912462219⟩, ⟨937629493622758876, 937629769134579672⟩, true⟩

def state01 : KState := ⟨⟨362329844377250781, 362329844501069209⟩, ⟨494964896385485038, 494965174468487398⟩, true⟩

def words00 : List Nat := [371279714337213883, 371279714337301645, 371279635665524935, 371279555161245574, 371279474705647510, 371279423469468442, 371279356527701478, 371279368062698483, 371279380807464542, 371279380807555157]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 3300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 3300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362629095845103550, 362629095969717529⟩, ⟨(-498179967841306286), (-498179687121020414)⟩, true⟩

def words01 : List Nat := [371279335644128987, 371279293057339698, 371279297700676992, 371279297700764776, 371279224797624479, 371279139720968887, 371279054695576259, 371279040780229466, 371279041846991447, 371279087030506141]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 3310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 3300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480727721654115, 362480727847063377⟩, ⟨(-5558875622171753), (-5558592257468603)⟩, true⟩

def words02 : List Nat := [371279124386674329, 371279124386762985, 371279132190366818, 371279180675658267, 371279232969412184, 371279232969500405, 371279165999407593, 371279100541346770, 371279058600038090, 371279059101264077]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 3320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 3300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362084733339792155, 362084733465996423⟩, ⟨1316675147086170656, 1316675433102352922⟩, true⟩

def words03 : List Nat := [371279148406594761, 371279237658373393, 371279304195240305, 371279304195328654, 371279251961691059, 371279201030488754, 371279167155104063, 371279167155192521, 371279065730978246, 371278947667524074]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 3330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 3300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362423328532601511, 362423328659599505⟩, ⟨184726076388181842, 184726365059452376⟩, true⟩

def words04 : List Nat := [371278829674707831, 371278768604315505, 371278662609453529, 371278644831774592, 371278627064695950, 371278589893430404, 371278480021024308, 371278458275024861, 371278470858032858, 371278470858124715]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 3340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 3300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362439334392505181, 362439334520314767⟩, ⟨130907105501525343, 130907396895712335⟩, true⟩

def words05 : List Nat := [371278454402745532, 371278439173993425, 371278445869321838, 371278445869419947, 371278437594938569, 371278427583808113, 371278417578613743, 371278405710771044, 371278306653841849, 371278295055105158]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 3350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 3300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362211313649084152, 362211313777687651⟩, ⟨899193585849517206, 899193879915409788⟩, true⟩

def words06 : List Nat := [371278359226037658, 371278359226126797, 371278330994896017, 371278293145089292, 371278255317745864, 371278245407993529, 371278209462190434, 371278184913736840, 371278160379826073, 371278136887454835]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 3360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 3300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362741595329249538, 362741595458660006⟩, ⟨(-889777596565940860), (-889777299776424074)⟩, true⟩

def words07 : List Nat := [371278065536512583, 371278073333498491, 371278167981972554, 371278191123142317, 371278200319551811, 371278209510542665, 371278261611108303, 371278269829680936, 371278347736732860, 371278425597738260]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 3370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 3300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362513148808496627, 362513148938716984⟩, ⟨(-117688343151516422), (-117688043620406032)⟩, true⟩

def words08 : List Nat := [371278484347539453, 371278484347629231, 371278488044775284, 371278517691822510, 371278574933551316, 371278574933641014, 371278517029116265, 371278460247417942, 371278432701558810, 371278442939418723]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 3380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 3300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362155912363203316, 362155912494233921⟩, ⟨1096853473009155042, 1096853775291134012⟩, true⟩

def words09 : List Nat := [371278539017172189, 371278635038329871, 371278726152591394, 371278726152681311, 371278702599969192, 371278675222317463, 371278686838074613, 371278686838164672, 371278611457147969, 371278516545790137]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 3390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 3300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 3300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk033
