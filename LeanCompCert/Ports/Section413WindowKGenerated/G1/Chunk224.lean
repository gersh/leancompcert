import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk224

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362500533583003737, 362500540366720084⟩, ⟨(-368739894359872391), (-368637139021101465)⟩, true⟩

def state01 : KState := ⟨⟨362470445820591618, 362470452610630929⟩, ⟨305256226563568327, 305359123569478709⟩, true⟩

def words00 : List Nat := [371284084732148516, 371284084732850591, 371284083405983369, 371284083550087751, 371284084296531589, 371284084297234708, 371284083022023207, 371284080894498800, 371284078766874405, 371284078631316761]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 22400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 22400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477061322872223, 362477068119221460⟩, ⟨157152141934140788, 157255180377868998⟩, true⟩

def words01 : List Nat := [371284079147136833, 371284080271143604, 371284081412192690, 371284081412906308, 371284081018235378, 371284081122932929, 371284082688984813, 371284082689691124, 371284082489302046, 371284082177222258]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 22410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 22400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362461799620399661, 362461806423038826⟩, ⟨499506406181147724, 499609585677065462⟩, true⟩

def words02 : List Nat := [371284082360716798, 371284082361490067, 371284082728799860, 371284083535083397, 371284083989867546, 371284083990569533, 371284081797232381, 371284081059599763, 371284080590198117, 371284080590924563]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 22420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 22400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475991783189790, 362475998592230164⟩, ⟨181168749512617660, 181272072619550760⟩, true⟩

def words03 : List Nat := [371284079598441664, 371284078596071367, 371284078576950201, 371284078577723379, 371284078666238334, 371284078757635424, 371284078838665110, 371284078839370723, 371284077029451821, 371284076670332640]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 22430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 22400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487251434960719, 362487258250261711⟩, ⟨(-71385610103853064), (-71282146476375834)⟩, true⟩

def words04 : List Nat := [371284077936238426, 371284077950244325, 371284077953708123, 371284077957401998, 371284078449511740, 371284078450293349, 371284079964677939, 371284081714417561, 371284083098243266, 371284083240396834]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 22440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 22400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362529392208912351, 362529399030552527⟩, ⟨(-1017713354718887547), (-1017609748743955519)⟩, true⟩

def words05 : List Nat := [371284083903421784, 371284084566736788, 371284087213338717, 371284087545242248, 371284087565587278, 371284087586162689, 371284088849384128, 371284089365071485, 371284091382898534, 371284093400850201]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 22450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 22400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362506402631281560, 362506409459277122⟩, ⟨(-501418865387601393), (-501315116639337899)⟩, true⟩

def words06 : List Nat := [371284095408301367, 371284095655938048, 371284096709235816, 371284097762816720, 371284099416172554, 371284099416875894, 371284098834513555, 371284098242962176, 371284099039385899, 371284100033054910]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 22460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 22400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362432591424365357, 362432598258696648⟩, ⟨1157725843605829519, 1157829734750637575⟩, true⟩

def words07 : List Nat := [371284102411849952, 371284104790723801, 371284106691886291, 371284106692591732, 371284106797304141, 371284107015823364, 371284107540554719, 371284107541258390, 371284105430581229, 371284103140135734]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 22470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 22400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362492340596798897, 362492347437427852⟩, ⟨(-185609191632540888), (-185505158883810740)⟩, true⟩

def words08 : List Nat := [371284100849573305, 371284100538001941, 371284099920055546, 371284100600769154, 371284100971051175, 371284100971755079, 371284098708019732, 371284098301623284, 371284099097039069, 371284099464510516]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 22480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 22400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362501749084408090, 362501755931459752⟩, ⟨(-397281770767086321), (-397177593539976791)⟩, true⟩

def words09 : List Nat := [371284099465053399, 371284099253912723, 371284100571684824, 371284101294550020, 371284102084437605, 371284102874532045, 371284103655319463, 371284103656035996, 371284103593097239, 371284104378482553]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 22490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 22400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 22400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk224
