import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk905

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497835582843992, 362497959569036913⟩, ⟨(-1169585484555843300), (-1162009438036694822)⟩, true⟩

def state01 : KState := ⟨⟨362485984263599408, 362486108278340545⟩, ⟨(-97029239058180559), (-89450608782837045)⟩, true⟩

def words00 : List Nat := [371285119961086269, 371285119964246470, 371285119994920489, 371285120038033986, 371285120093580573, 371285120096754949, 371285120045144862, 371285119994515362, 371285119979360739, 371285119993946573]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 90500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 90500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362472677506545939, 362472801549726019⟩, ⟨1107505087699005143, 1115086292128235515⟩, true⟩

def words01 : List Nat := [371285120129005978, 371285120265389936, 371285120400011156, 371285120403170202, 371285120398688865, 371285120412830455, 371285120463737441, 371285120466896630, 371285120355367924, 371285120222860445]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 90510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 90500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489587819758489, 362489711891228671⟩, ⟨(-423284066995886275), (-415700301608342741)⟩, true⟩

def words02 : List Nat := [371285120088916653, 371285120068865498, 371285120047158632, 371285120099679012, 371285120119293047, 371285120122452505, 371285119979140173, 371285119959482650, 371285120036597601, 371285120090612216]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 90520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 90500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362497566784617558, 362497690884879598⟩, ⟨(-1145665688058866079), (-1138079315997421343)⟩, true⟩

def words03 : List Nat := [371285120122194370, 371285120154764554, 371285120308006858, 371285120408049868, 371285120534403388, 371285120661988285, 371285120787448609, 371285120833689401, 371285120974667694, 371285121117415163]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 90530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 90500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491048450216945, 362491172578595156⟩, ⟨(-555458549351798988), (-547869631502209750)⟩, true⟩

def words04 : List Nat := [371285121320685651, 371285121400254289, 371285121478928568, 371285121558710088, 371285121644021624, 371285121669673299, 371285121815891789, 371285121963365038, 371285122110035002, 371285122180129074]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 90540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 90500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362502028676156250, 362502152833211975⟩, ⟨(-1549760524608728571), (-1542169009875197047)⟩, true⟩

def words05 : List Nat := [371285122312423276, 371285122446471228, 371285122690439397, 371285122809247146, 371285122907818639, 371285123007343460, 371285123217653385, 371285123387946975, 371285123578179842, 371285123769819619]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 90550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 90500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488755861722121, 362488880047241437⟩, ⟨(-347746365900474875), (-340152273351798431)⟩, true⟩

def words06 : List Nat := [371285123960122254, 371285123988731114, 371285124078620263, 371285124170098074, 371285124280576280, 371285124290648491, 371285124293035697, 371285124290882247, 371285124359927779, 371285124405001076]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 90560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 90500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483965388621846, 362484089602644444⟩, ⟨86189495874018400, 93786170106121848⟩, true⟩

def words07 : List Nat := [371285124529806808, 371285124655857694, 371285124750384725, 371285124762140321, 371285124809879029, 371285124859269537, 371285125012407276, 371285125015568652, 371285125006496372, 371285124998649149]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 90570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 90500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489098091406054, 362489222333680990⟩, ⟨(-378709528278273207), (-371110294803426833)⟩, true⟩

def words08 : List Nat := [371285125088911119, 371285125139484070, 371285125310512875, 371285125482870354, 371285125611457815, 371285125614619532, 371285125594885922, 371285125613023218, 371285125738125845, 371285125786619986]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 90580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 90500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362491068060007889, 362491192331146309⟩, ⟨(-557173755313407576), (-549571906955919586)⟩, true⟩

def words09 : List Nat := [371285125834138691, 371285125882776585, 371285125999539876, 371285126074667576, 371285126185665461, 371285126297870399, 371285126394644144, 371285126397806533, 371285126412106574, 371285126483010462]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 90590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 90500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 90500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk905
