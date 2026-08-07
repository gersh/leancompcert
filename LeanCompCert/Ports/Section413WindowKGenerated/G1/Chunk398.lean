import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk398

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362506264262157285, 362506286730724580⟩, ⟨(-839215304792490113), (-838611022113873395)⟩, true⟩

def state01 : KState := ⟨⟨362483722692705507, 362483745173050126⟩, ⟨58079803278848209, 58684554755697313⟩, true⟩

def words00 : List Nat := [371285217162515926, 371285217170480164, 371285217714137368, 371285218258429046, 371285218937426938, 371285219014490092, 371285219090252683, 371285219166461265, 371285219287482185, 371285219288969637]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 39800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 39800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471334583972361, 362471357076059585⟩, ⟨551408236518426091, 552013455527472693⟩, true⟩

def words01 : List Nat := [371285219689084455, 371285220126724087, 371285220502535242, 371285220503843794, 371285220237296526, 371285220164086012, 371285220478090616, 371285220479396275, 371285220141361681, 371285219794681571]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 39810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 39800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362494545409132795, 362494567912901599⟩, ⟨(-372943480444357269), (-372337796213872541)⟩, true⟩

def words02 : List Nat := [371285219729421180, 371285219730859004, 371285219924745278, 371285220152592573, 371285220237044854, 371285220238350312, 371285219483116486, 371285219358478785, 371285219736879404, 371285219972949957]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 39820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 39800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488480652950996, 362488503168624021⟩, ⟨(-131344960488987373), (-130738802054037665)⟩, true⟩

def words03 : List Nat := [371285220015000249, 371285220057498030, 371285220636752831, 371285220903028443, 371285221321411822, 371285221740263313, 371285222033162009, 371285222034467905, 371285221570551034, 371285221654554243]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 39830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 39800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490941626616222, 362490964153918002⟩, ⟨(-229322611161954519), (-228715989376573241)⟩, true⟩

def words04 : List Nat := [371285222367290433, 371285222516638287, 371285222634902199, 371285222753602177, 371285222984814074, 371285222986254038, 371285223577340454, 371285224188521658, 371285224729995391, 371285224875371001]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 39840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 39800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362513533320752055, 362513555859865451⟩, ⟨(-1129785228179489815), (-1129178135642447633)⟩, true⟩

def words05 : List Nat := [371285225280145034, 371285225685561661, 371285226413125467, 371285226414431818, 371285226303628823, 371285226087478164, 371285226282264082, 371285226543298766, 371285227254907112, 371285227967046846]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 39850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 39800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362495047706366398, 362495070257266149⟩, ⟨(-392924255365522920), (-392316692964136398)⟩, true⟩

def words06 : List Nat := [371285228644483599, 371285228673649550, 371285229331274275, 371285229989564211, 371285230541747892, 371285230543055864, 371285230391133428, 371285230171394913, 371285230358772992, 371285230607070164]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 39860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 39800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362467223058825499, 362467245621516215⟩, ⟨716675993820228331, 717284026387861871⟩, true⟩

def words07 : List Nat := [371285231270145750, 371285231933758569, 371285232597319100, 371285232598626240, 371285232424472752, 371285232225538358, 371285232453941359, 371285232455248681, 371285232129888420, 371285231680352421]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 39870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 39800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362516852115241988, 362516874689642927⟩, ⟨(-1262731109934692526), (-1262122610304708398)⟩, true⟩

def words08 : List Nat := [371285231239093521, 371285231240539416, 371285231445563840, 371285231863173509, 371285232175405138, 371285232176745097, 371285232794284368, 371285233418280667, 371285234612824629, 371285235407341037]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 39880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 39800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496012703857713, 362496035290169023⟩, ⟨(-431300025342099417), (-430691050548435011)⟩, true⟩

def words09 : List Nat := [371285236201884716, 371285236996817920, 371285237928349333, 371285238589164552, 371285239377160214, 371285240165628040, 371285240878608051, 371285240879915797, 371285241026613646, 371285241298776616]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 39890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 39800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 39800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk398
