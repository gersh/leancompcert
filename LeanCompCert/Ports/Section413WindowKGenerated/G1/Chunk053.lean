import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk053

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362612539926967138, 362612540259816444⟩, ⟨(-684468933571577139), (-684467738079240397)⟩, true⟩

def state01 : KState := ⟨⟨362656232574548784, 362656232908717899⟩, ⟨(-916677214255473327), (-916676011761436235)⟩, true⟩

def words00 : List Nat := [371283444555909616, 371283444556056682, 371283467246367882, 371283496277948922, 371283536006854252, 371283546727682761, 371283553007328047, 371283559284655329, 371283600891269232, 371283633396053347]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 5300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 5300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362428847685176777, 362428848020667802⟩, ⟨292592946450668832, 292594155970822688⟩, true⟩

def words01 : List Nat := [371283694665040110, 371283755911023984, 371283805064152992, 371283807286739406, 371283820242154063, 371283833192765459, 371283868646993130, 371283868647139737, 371283857262080473, 371283846922166077]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 5310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 5300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362531903899103361, 362531904235907714⟩, ⟨(-255849747574441469), (-255848531060620137)⟩, true⟩

def words02 : List Nat := [371283847915171191, 371283847915332432, 371283870339469546, 371283899088014105, 371283922058694811, 371283922058841549, 371283898334933600, 371283889058018344, 371283902635180944, 371283911639572952]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 5320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 5300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362591465052495095, 362591465390636786⟩, ⟨(-573268990066715598), (-573267766418018402)⟩, true⟩

def words03 : List Nat := [371283920743033530, 371283929843128206, 371283973876593977, 371284005976648927, 371284036576229752, 371284067164400426, 371284096767442895, 371284096767590482, 371284111876146356, 371284131976216637]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 5330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 5300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476144704363997, 362476145043821114⟩, ⟨42901007368154147, 42902238048036739⟩, true⟩

def words04 : List Nat := [371284165551601690, 371284165551749075, 371284152714920014, 371284138837920762, 371284124966056110, 371284121832691352, 371284125578091132, 371284144824956720, 371284164153583911, 371284164153736635]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 5340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 5300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362649063094030108, 362649063434822337⟩, ⟨(-882813433857746230), (-882812196028245942)⟩, true⟩

def words05 : List Nat := [371284195865199651, 371284229062950303, 371284288431505939, 371284301584783473, 371284302404570080, 371284303224092608, 371284321664511788, 371284328932589346, 371284359666739009, 371284390389489704]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 5350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 5300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362400311764654337, 362400312106782264⟩, ⟨451925167926475426, 451926412922210558⟩, true⟩

def words06 : List Nat := [371284421256699916, 371284423647057248, 371284453703964577, 371284483749742732, 371284516473725613, 371284516473873631, 371284503222992044, 371284490174063257, 371284477129935553, 371284469725575972]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 5360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 5300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362183786095894065, 362183786439356404⟩, ⟨1616687229195295236, 1616688481363629156⟩, true⟩

def words07 : List Nat := [371284462994262902, 371284471928573813, 371284482079047924, 371284482079196259, 371284446407815044, 371284419139578478, 371284391881403817, 371284389822394505, 371284342022266955, 371284286157081986]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 5370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 5300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362353303163797767, 362353303508591414⟩, ⟨704205694513186603, 704206953850751645⟩, true⟩

def words08 : List Nat := [371284230312597005, 371284208722072103, 371284175670810464, 371284156772217814, 371284137880596953, 371284112846955092, 371284042204227355, 371284005745797964, 371283969300825080, 371283954149380051]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 5380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 5300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362399897461142160, 362399897807293005⟩, ⟨453193465932262598, 453194732591850224⟩, true⟩

def words09 : List Nat := [371283929914537714, 371283904867784733, 371283888884709272, 371283888884873114, 371283888967033633, 371283892039134236, 371283892039247656, 371283887888334094, 371283838302122070, 371283822757772978]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 5390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 5300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 5300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk053
