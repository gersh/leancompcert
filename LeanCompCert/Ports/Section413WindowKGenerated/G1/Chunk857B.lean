import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk857A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk857B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk857A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk857B
