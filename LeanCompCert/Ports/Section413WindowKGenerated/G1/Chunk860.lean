import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk860

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486103435342265, 362486214958597911⟩, ⟨(-89360137335722623), (-82884202399275891)⟩, true⟩

def state01 : KState := ⟨⟨362469953033234087, 362470064583483507⟩, ⟨1299658757799782763, 1306137014339692853⟩, true⟩

def words00 : List Nat := [371285251212137403, 371285251215179747, 371285251114890450, 371285251101938216, 371285251099312536, 371285251102302815, 371285250936212395, 371285250771278406, 371285250605138218, 371285250457385841]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 86000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 86000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362469791357492500, 362469902934655750⟩, ⟨1313615164058273010, 1320095735588857336⟩, true⟩

def words01 : List Nat := [371285250282856583, 371285250244505464, 371285250205198231, 371285250162577377, 371285249972029038, 371285249824565778, 371285249675446873, 371285249662262802, 371285249491181685, 371285249316143647]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 86010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 86000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477195173774715, 362477306777711067⟩, ⟨676693708958371995, 683176583647870059⟩, true⟩

def words02 : List Nat := [371285249139778976, 371285249052875644, 371285248900357607, 371285248804963617, 371285248708619465, 371285248587479656, 371285248285330060, 371285248119645998, 371285247952446046, 371285247921308044]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 86020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 86000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475215737220672, 362475327368454533⟩, ⟨847014446858952266, 853499670088188314⟩, true⟩

def words03 : List Nat := [371285247831275001, 371285247717293955, 371285247604250401, 371285247607562955, 371285247561284307, 371285247557612017, 371285247553001515, 371285247507424593, 371285247280887185, 371285247169362114]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 86030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 86000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362471761407014097, 362471873064895029⟩, ⟨1144275369499776964, 1150762885582425040⟩, true⟩

def words04 : List Nat := [371285247066066455, 371285247069078652, 371285246960144009, 371285246830257319, 371285246699197303, 371285246610837725, 371285246453734618, 371285246387749299, 371285246320735743, 371285246253571176]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 86040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 86000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481686859607282, 362481798544538231⟩, ⟨290108316797002905, 296598160671057283⟩, true⟩

def words05 : List Nat := [371285246100230133, 371285245985345793, 371285245868957873, 371285245823041623, 371285245638092752, 371285245432163182, 371285245224991603, 371285245133454514, 371285244992584190, 371285244955886954]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 86050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 86000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475910691584126, 362476022403487253⟩, ⟨787188704165414455, 793680869402097037⟩, true⟩

def words06 : List Nat := [371285244918077429, 371285244881141006, 371285244687132885, 371285244612430876, 371285244536221570, 371285244467792862, 371285244252676393, 371285244038867317, 371285243823871920, 371285243745062740]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 86060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 86000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362461306174418709, 362461417913345863⟩, ⟨2044305585346777631, 2050800076676072219⟩, true⟩

def words07 : List Nat := [371285243639962028, 371285243601043424, 371285243561037829, 371285243519312136, 371285243296873265, 371285243082305339, 371285242866185780, 371285242785805757, 371285242537044672, 371285242263678996]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 86070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 86000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478978356633566, 362479090122349656⟩, ⟨523035585751626547, 529532383209929029⟩, true⟩

def words08 : List Nat := [371285241988942539, 371285241825289080, 371285241592943564, 371285241496552862, 371285241399281160, 371285241281351964, 371285241117975593, 371285241070220876, 371285241035538014, 371285241038637378]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 86080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 86000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362467697212753818, 362467809005751080⟩, ⟨1494316280439112803, 1500815426670857757⟩, true⟩

def words09 : List Nat := [371285240969428396, 371285240901302281, 371285240832022215, 371285240815327144, 371285240729934456, 371285240675822117, 371285240620675664, 371285240539655121, 371285240277939741, 371285240079231578]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 86090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 86000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 86000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk860
