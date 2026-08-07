import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk916

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362480243703994358, 362480370841181211⟩, ⟨425874679234334510, 433737627805880286⟩, true⟩

def state01 : KState := ⟨⟨362486643392941676, 362486770558802636⟩, ⟨(-160304479906546680), (-152438904639827372)⟩, true⟩

def words00 : List Nat := [371285105978586841, 371285105999806319, 371285106119780297, 371285106241025205, 371285106353873808, 371285106357075182, 371285106390216733, 371285106460488350, 371285106556965893, 371285106578443948]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 91600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 91600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484430650543691, 362484557845573064⟩, ⟨42430465139449000, 50298712671955620⟩, true⟩

def words01 : List Nat := [371285106592383799, 371285106607338768, 371285106694669158, 371285106723933292, 371285106782807740, 371285106843013923, 371285106901851004, 371285106905059615, 371285106840313937, 371285106838289414]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 91610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 91600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484776789688291, 362484904013264864⟩, ⟨10711375802033245, 18582238976331317⟩, true⟩

def words02 : List Nat := [371285106947545907, 371285106950748284, 371285106923790294, 371285106874830212, 371285106824601942, 371285106811056755, 371285106757868017, 371285106782426178, 371285106806311850, 371285106809717733]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 91620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 91600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362493984654017776, 362494111906542671⟩, ⟨(-833036698157455864), (-825163182305514456)⟩, true⟩

def words03 : List Nat := [371285106926510696, 371285107047224629, 371285107264588734, 371285107324278971, 371285107351581608, 371285107379853366, 371285107420045900, 371285107423611506, 371285107503279571, 371285107605167681]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 91630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 91600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481762602813502, 362481889884231741⟩, ⟨287010602907205862, 294886766691244900⟩, true⟩

def words04 : List Nat := [371285107684022291, 371285107687224622, 371285107635579211, 371285107667854426, 371285107735006336, 371285107738208834, 371285107646878940, 371285107539152033, 371285107430078615, 371285107415783201]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 91640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 91600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362472809603715845, 362472936913962050⟩, ⟨1107604939179757045, 1115483745195753045⟩, true⟩

def words05 : List Nat := [371285107397382651, 371285107415348333, 371285107423134948, 371285107426337617, 371285107275356823, 371285107139706504, 371285107002324155, 371285106972025487, 371285106841826495, 371285106712622270]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 91650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 91600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472695807638519, 362472823146526669⟩, ⟨1118057036221260981, 1125938467705502275⟩, true⟩

def words06 : List Nat := [371285106582024855, 371285106556434346, 371285106470152371, 371285106419493408, 371285106367856107, 371285106277252974, 371285106027040750, 371285105878997059, 371285105729332053, 371285105664991876]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 91660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 91600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475198120299990, 362475325488462718⟩, ⟨888690307405087757, 896574422634216051⟩, true⟩

def words07 : List Nat := [371285105533401340, 371285105402810160, 371285105270828097, 371285105259182125, 371285105205600831, 371285105182160411, 371285105157648168, 371285105133777277, 371285104980541530, 371285104877889357]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 91670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 91600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362467282620305187, 362467410016977281⟩, ⟨1614415779644361536, 1622302508760388264⟩, true⟩

def words08 : List Nat := [371285104773400038, 371285104744786118, 371285104556864515, 371285104359148395, 371285104160253579, 371285103968665800, 371285103734046729, 371285103609864122, 371285103484584442, 371285103358767666]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 91680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 91600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486255871766419, 362486383297426243⟩, ⟨(-125345534096705984), (-117456146954342774)⟩, true⟩

def words09 : List Nat := [371285103167973347, 371285103097720149, 371285103025839734, 371285103004506434, 371285102866321017, 371285102710235920, 371285102552784511, 371285102496846482, 371285102419776888, 371285102437381595]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 91690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 91600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 91600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk916
