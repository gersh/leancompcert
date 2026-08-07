import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk857

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493413676238941, 362493524392891791⟩, ⟨(-714202834430488170), (-707796146482902530)⟩, true⟩

def state01 : KState := ⟨⟨362476566905216710, 362476677648757390⟩, ⟨729626213160712206, 736035205534995654⟩, true⟩

def words00 : List Nat := [371285265548712966, 371285265551692327, 371285265477033731, 371285265510293303, 371285265575134704, 371285265578113788, 371285265461670053, 371285265340245050, 371285265217595267, 371285265155530637]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 85700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 85700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362473192973416677, 362473303743786055⟩, ⟨1018878492148568179, 1025289784150306783⟩, true⟩

def words01 : List Nat := [371285265093163248, 371285265132260804, 371285265170266633, 371285265173254207, 371285265071785815, 371285264981241227, 371285264931020179, 371285264933999739, 371285264796701342, 371285264660540025]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 85710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 85700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362472013050003458, 362472123847093544⟩, ⟨1120083438720770110, 1126497021353681136⟩, true⟩

def words02 : List Nat := [371285264523030450, 371285264484532170, 371285264409046846, 371285264404768255, 371285264399612647, 371285264372388120, 371285264162853022, 371285264065583698, 371285263966754969, 371285263903332360]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 85720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 85700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475661204997561, 362475772029196161⟩, ⟨807316861097139195, 813732767883638709⟩, true⟩

def words03 : List Nat := [371285263752296147, 371285263574619997, 371285263395761797, 371285263354141227, 371285263263996814, 371285263200053230, 371285263135021032, 371285263070729932, 371285262837978338, 371285262730944280]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 85730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 85700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362469038748958162, 362469149599750982⟩, ⟨1375169780015341234, 1381587967125310012⟩, true⟩

def words04 : List Nat := [371285262637860523, 371285262640842153, 371285262500761905, 371285262333207071, 371285262164484505, 371285262002585824, 371285261780771143, 371285261660424581, 371285261539076703, 371285261412778683]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 85740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 85700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362483684759385031, 362483795637130060⟩, ⟨119213121309458900, 125633619706378868⟩, true⟩

def words05 : List Nat := [371285261226909373, 371285261178515396, 371285261179057690, 371285261182039376, 371285261073040171, 371285260943005622, 371285260811801117, 371285260737988463, 371285260595077508, 371285260581389696]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 85750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 85700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476887611892219, 362476998516551967⟩, ⟨702130669068595427, 708553475809104673⟩, true⟩

def words06 : List Nat := [371285260566567998, 371285260551134000, 371285260366773173, 371285260309346033, 371285260250421953, 371285260202889397, 371285260041374272, 371285259852647771, 371285259662684698, 371285259604062858]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 85760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 85700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476390639980106, 362476501571490792⟩, ⟨744765182649130772, 751190292534560736⟩, true⟩

def words07 : List Nat := [371285259509804540, 371285259472872016, 371285259434958756, 371285259397819451, 371285259229734959, 371285259095761782, 371285258960206239, 371285258940406150, 371285258843172163, 371285258744404462]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 85770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 85700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486612042904018, 362486723001087487⟩, ⟨(-132019070827404301), (-125591672813671029)⟩, true⟩

def words08 : List Nat := [371285258678006091, 371285258681304313, 371285258784634571, 371285258901002126, 371285258994092213, 371285258997075103, 371285258944817282, 371285258966443552, 371285259054962305, 371285259075118404]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 85780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 85700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482501451024243, 362482612436455207⟩, ⟨220705728466476924, 227135464172187624⟩, true⟩

def words09 : List Nat := [371285259094423897, 371285259114835813, 371285259269644779, 371285259364615169, 371285259500036760, 371285259636571369, 371285259772416049, 371285259775398794, 371285259730021310, 371285259702937401]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 85790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 85700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 85700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk857
