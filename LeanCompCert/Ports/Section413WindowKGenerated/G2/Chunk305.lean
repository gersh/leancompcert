import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk305

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360622412991104789, 360622418594099652⟩, ⟨(-1189472422208262581), (-1189356853422384117)⟩, true⟩

def state01 : KState := ⟨⟨360612391707416527, 360612397314269273⟩, ⟨(-884154144917619768), (-884038458447386432)⟩, true⟩

def words00 : List Nat := [360583425296286183, 360583425329353357, 360583425329683428, 360583425095835128, 360583424861894716, 360583424357551324, 360583423888408305, 360583422884521601, 360583421946433400, 360583422896569185]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 30500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 30500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360570089668269922, 360570095278944119⟩, ⟨406789221967424969, 406905025049514111⟩, true⟩

def words01 : List Nat := [360583424158839758, 360583425421103459, 360583425843967612, 360583426611575764, 360583426721222035, 360583426830967267, 360583428010103433, 360583428120810105, 360583428121174591, 360583427684745218]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 30510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 30500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360603542827058745, 360603548441557130⟩, ⟨(-614381093255994381), (-614265173440591255)⟩, true⟩

def words02 : List Nat := [360583427311266553, 360583427913289507, 360583429314559165, 360583430715816305, 360583430981665598, 360583430982070982, 360583430179954899, 360583429227095404, 360583428389599941, 360583429049023621]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 30520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 30500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590114120780238, 360590119739139686⟩, ⟨(-204333962854173796), (-204217925141261496)⟩, true⟩

def words03 : List Nat := [360583429174187467, 360583429299388409, 360583429891190729, 360583431314036952, 360583432281634401, 360583433249236988, 360583433468019500, 360583433468425027, 360583432838705810, 360583433058116103]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 30530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 30500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360541285257950710, 360541290880135090⟩, ⟨1286976190984514616, 1287092345530129796⟩, true⟩

def words04 : List Nat := [360583433251565133, 360583433251970691, 360583432378162732, 360583430970929923, 360583429563722789, 360583427589167760, 360583426150916160, 360583424878402005, 360583423605921007, 360583421562476502]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 30540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 30500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360621227802226495, 360621233428236730⟩, ⟨(-1155811324499762418), (-1155695053055078354)⟩, true⟩

def words05 : List Nat := [360583420183776828, 360583419572583048, 360583419416615764, 360583419417021491, 360583418806107513, 360583417105930091, 360583415405786506, 360583414943472267, 360583416181316391, 360583417419171089]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 30550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 30500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360612742006279930, 360612747636160558⟩, ⟨(-896498375997300556), (-896381986254590538)⟩, true⟩

def words06 : List Nat := [360583417993802377, 360583419013302744, 360583420344620354, 360583421675972437, 360583422736882376, 360583424056175533, 360583424684129471, 360583425312086101, 360583425359405744, 360583426319021617]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 30560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 30500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360549209916263289, 360549215549967018⟩, ⟨1046076955337280976, 1046193461971357774⟩, true⟩

def words07 : List Nat := [360583427745080783, 360583429171123549, 360583429935649582, 360583429936055622, 360583429634762923, 360583429049252643, 360583428943132684, 360583428943538737, 360583428357744855, 360583427239370922]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 30570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 30500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585886705609088, 360585892343149919⟩, ⟨(-75780687045725477), (-75664063054101327)⟩, true⟩

def words08 : List Nat := [360583426120975821, 360583425834278803, 360583425834613871, 360583425466659509, 360583425098697545, 360583423815602739, 360583421949018337, 360583420835946451, 360583419722830212, 360583418933877450]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 30580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 30500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360553519282698303, 360553524924109304⟩, ⟨914551970731088587, 914668713130080263⟩, true⟩

def words09 : List Nat := [360583418934245486, 360583418158695833, 360583417671503305, 360583418498376172, 360583418809454296, 360583419120578042, 360583419120946686, 360583418609965974, 360583417034922650, 360583416058525320]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 30590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 30500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 30500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk305
