import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk973

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362473885375758168, 362474029498657067⟩, ⟨1090855514714783259, 1100323286434783099⟩, true⟩

def state01 : KState := ⟨⟨362484379284302342, 362484523437742150⟩, ⟨69791535050987192, 79262278557317608⟩, true⟩

def words00 : List Nat := [371285337948844695, 371285337942096213, 371285337923737932, 371285337969991104, 371285338005032312, 371285338008470692, 371285337948566086, 371285337934252559, 371285337967947742, 371285337971485418]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 97300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 97300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491094709747768, 362491238894331359⟩, ⟨(-583724287245240214), (-574250512978743704)⟩, true⟩

def words01 : List Nat := [371285337965667477, 371285337960638975, 371285338021166131, 371285338052766313, 371285338114759863, 371285338178030494, 371285338218476433, 371285338221915852, 371285338247722955, 371285338312617457]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 97310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 97300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480651507074322, 362480795722117750⟩, ⟨432650731885871705, 442127470661422649⟩, true⟩

def words02 : List Nat := [371285338419444558, 371285338422860204, 371285338389136004, 371285338356271485, 371285338322135380, 371285338293814191, 371285338232008238, 371285338256614321, 371285338279669085, 371285338283205405]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 97320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 97300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488316338930548, 362488460584774796⟩, ⟨(-313392556143187721), (-303912819365550753)⟩, true⟩

def words03 : List Nat := [371285338261595835, 371285338288381472, 371285338409854621, 371285338413272076, 371285338412353975, 371285338384893115, 371285338386663542, 371285338390428410, 371285338402833517, 371285338438717477]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 97330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 97300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482360846714147, 362482505123446154⟩, ⟨266346647162083610, 275829390703359040⟩, true⟩

def words04 : List Nat := [371285338471169230, 371285338474654794, 371285338501099370, 371285338566384624, 371285338661696842, 371285338665113331, 371285338619909101, 371285338566306049, 371285338511384103, 371285338501881731]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 97340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 97300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362470918558830973, 362471062866342163⟩, ⟨1380360895433148299, 1389846635482714367⟩, true⟩

def words05 : List Nat := [371285338535208253, 371285338599061549, 371285338651985256, 371285338655401886, 371285338567496934, 371285338513170520, 371285338467988716, 371285338471405615, 371285338344286368, 371285338201546382]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 97350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 97300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477583162033270, 362477727500151412⟩, ⟨731433058281034557, 740921778380960213⟩, true⟩

def words06 : List Nat := [371285338057256790, 371285337955645539, 371285337800499946, 371285337689252027, 371285337576972298, 371285337449281659, 371285337191548984, 371285337041173392, 371285336888996959, 371285336843669754]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 97360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 97300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362479399709711351, 362479544078941544⟩, ⟨554559632761813971, 564051382399870965⟩, true⟩

def words07 : List Nat := [371285336768101792, 371285336692721572, 371285336642416679, 371285336646183167, 371285336622435268, 371285336611760152, 371285336599916115, 371285336568221442, 371285336405520322, 371285336350274466]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 97370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 97300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480984862696452, 362481129262345219⟩, ⟨400216213488526121, 409710925445570199⟩, true⟩

def words08 : List Nat := [371285336339162741, 371285336342589067, 371285336308200226, 371285336251550869, 371285336193493326, 371285336168615434, 371285336113960469, 371285336141912011, 371285336168401296, 371285336171940102]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 97380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 97300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362498239399161651, 362498383829803871⟩, ⟨(-1280316542225195008), (-1270818811659300338)⟩, true⟩

def words09 : List Nat := [371285336131690443, 371285336136416643, 371285336201996455, 371285336205445589, 371285336199208837, 371285336174547058, 371285336225643236, 371285336268586276, 371285336404862489, 371285336542695327]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 97390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 97300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 97300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk973
