import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk093

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362436946442826458, 362436947524173690⟩, ⟨418009039890322623, 418015849217253539⟩, true⟩

def state01 : KState := ⟨⟨362391876827574974, 362391877911336330⟩, ⟨837367073576098764, 837373905366844914⟩, true⟩

def words00 : List Nat := [371281895264504070, 371281895264774559, 371281884543060132, 371281871681909470, 371281858823418248, 371281849427093444, 371281836670957907, 371281831902321832, 371281827134621170, 371281821402782823]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 9300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 9300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484303096617368, 362484304182826151⟩, ⟨(-23417622805821003), (-23410768217119293)⟩, true⟩

def words01 : List Nat := [371281813582586985, 371281815422056064, 371281826610197756, 371281826610468495, 371281822483554437, 371281815609717276, 371281808737252660, 371281803237941105, 371281792297518379, 371281792567310958]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 9310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 9300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362406336776420949, 362406337865076223⟩, ⟨703428797179568456, 703435674581944296⟩, true⟩

def words02 : List Nat := [371281792567514909, 371281792556445253, 371281779599643313, 371281778118987421, 371281778475332224, 371281778475603250, 371281765034498631, 371281751540437921, 371281738049156008, 371281732899865285]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 9320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 9300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362377379356352213, 362377380447450817⟩, ⟨973759913124116002, 973766813335524712⟩, true⟩

def words03 : List Nat := [371281724819993869, 371281719810528877, 371281714802051613, 371281707772633871, 371281689993510234, 371281675659486036, 371281661328390864, 371281658436432470, 371281649299631619, 371281638136244771]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 9330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 9300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362515278466819202, 362515279560351206⟩, ⟨(-314688474890546685), (-314681551938952115)⟩, true⟩

def words04 : List Nat := [371281627245215175, 371281627245517127, 371281628420254409, 371281634720305088, 371281637955804158, 371281637956075916, 371281625976073519, 371281621439897288, 371281623779111129, 371281627378558997]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 9340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 9300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362484899017767723, 362484900113784308⟩, ⟨(-30101228771946157), (-30094282577071469)⟩, true⟩

def words05 : List Nat := [371281631033732911, 371281634688221657, 371281647981098579, 371281655608068386, 371281666669800126, 371281677729268360, 371281688735941089, 371281688736213170, 371281684912310229, 371281685256121978]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 9350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 9300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362343144651040089, 362343145749481141⟩, ⟨1297493670800475778, 1297500639701241740⟩, true⟩

def words06 : List Nat := [371281687876579399, 371281687876851774, 371281678113523473, 371281668307880142, 371281658504230088, 371281652145479757, 371281641709030716, 371281634480425506, 371281627253272098, 371281619670473803]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 9360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 9300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362484279139612571, 362484280240519811⟩, ⟨(-25718401498853541), (-25711409477381103)⟩, true⟩

def words07 : List Nat := [371281604893803011, 371281601474032263, 371281598054856422, 371281596941509354, 371281583355907714, 371281567967487881, 371281552582236701, 371281548545412568, 371281539151780966, 371281539444285148]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 9370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 9300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362362563966878284, 362362565070246620⟩, ⟨1116188796191649170, 1116195811310856624⟩, true⟩

def words08 : List Nat := [371281539444489659, 371281538778774015, 371281523014530724, 371281512913692110, 371281502814868862, 371281496146225232, 371281481078117217, 371281463323450699, 371281445572458676, 371281435763676957]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 9380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 9300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362430120846598960, 362430121952431843⟩, ⟨482000181579492333, 482007219853240657⟩, true⟩

def words09 : List Nat := [371281423105925157, 371281421754825993, 371281420403919900, 371281418682990971, 371281411119342239, 371281406995708434, 371281410040889688, 371281410041163281, 371281404771555721, 371281399316246018]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 9390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 9300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 9300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk093
