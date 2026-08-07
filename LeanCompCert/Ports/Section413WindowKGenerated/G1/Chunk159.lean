import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk159

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362452302898409876, 362452306215169429⟩, ⟨508535807516001327, 508571481082238661⟩, true⟩

def state01 : KState := ⟨⟨362459571397991435, 362459574719061203⟩, ⟨392987793684905524, 393023535805666180⟩, true⟩

def words00 : List Nat := [371284291777057375, 371284291777541398, 371284288454891962, 371284285181362339, 371284281908044300, 371284279810027668, 371284276755357327, 371284277205143432, 371284277643500251, 371284277644001849]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 15900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 15900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362539183164207033, 362539186489667282⟩, ⟨(-874121923749873399), (-874086111754918789)⟩, true⟩

def words01 : List Nat := [371284276143756323, 371284276196330492, 371284280198284749, 371284280198769328, 371284279771444587, 371284278735687439, 371284278630887084, 371284278631429603, 371284281582599992, 371284285031734055]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 15910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 15900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362469982297103670, 362469985626936942⟩, ⟨227815615216312321, 227851496852458525⟩, true⟩

def words02 : List Nat := [371284287987177554, 371284287987663388, 371284289844350669, 371284292745782865, 371284295705986186, 371284295706471113, 371284293413630642, 371284291111750311, 371284288921850075, 371284288922407907]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 15920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 15900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362453431587093611, 362453434921294729⟩, ⟨491828225825213430, 491864177063591410⟩, true⟩

def words03 : List Nat := [371284290437946697, 371284292851211241, 371284295201439452, 371284295201924955, 371284293206358892, 371284292383802566, 371284294676291914, 371284294676779406, 371284294082375079, 371284292146957439]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 15930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 15900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362548922542421967, 362548925880965368⟩, ⟨(-1030738291665172051), (-1030702271188345969)⟩, true⟩

def words04 : List Nat := [371284291120180337, 371284291120714546, 371284292290472593, 371284294501862599, 371284296111746651, 371284296112241839, 371284297638694168, 371284299887844155, 371284305048409116, 371284309100124773]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 15940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 15900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362542967823335860, 362542971166310433⟩, ⟨(-935769275689033723), (-935733184512786687)⟩, true⟩

def words05 : List Nat := [371284313089538662, 371284317078620137, 371284322065298607, 371284325105498625, 371284329314216629, 371284333522587923, 371284337845936309, 371284337846422293, 371284341266915428, 371284344940853834]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 15950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 15900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362468649948362582, 362468653295664215⟩, ⟨250805221140601917, 250841381399727623⟩, true⟩

def words06 : List Nat := [371284350575413730, 371284352039467742, 371284353048080785, 371284354056728099, 371284355927407552, 371284355927947486, 371284357339277923, 371284358842982130, 371284360332193014, 371284360332696133]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 15960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 15900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362578177341521363, 362578180693210941⟩, ⟨(-1498694998189766868), (-1498658767832746324)⟩, true⟩

def words07 : List Nat := [371284362288244903, 371284365227146917, 371284372086980783, 371284375834413771, 371284378940402587, 371284382046153767, 371284387703897475, 371284391420928458, 371284397290425852, 371284403159399994]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 15970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 15900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489431695307486, 362489435051393715⟩, ⟨(-80358153835206055), (-80321853197677831)⟩, true⟩

def words08 : List Nat := [371284408278330045, 371284408928174170, 371284411537364710, 371284414146489542, 371284417188431449, 371284417188918151, 371284415018073123, 371284412916562859, 371284411795477050, 371284412110164419]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 15980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 15900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475253073286251, 362475256433757922⟩, ⟨146739214050439644, 146775584833277320⟩, true⟩

def words09 : List Nat := [371284416337549992, 371284420564608254, 371284424802362396, 371284425591545066, 371284426606935573, 371284427622428028, 371284431035587412, 371284431036075762, 371284430480633659, 371284429907810002]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 15990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 15900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 15900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk159
