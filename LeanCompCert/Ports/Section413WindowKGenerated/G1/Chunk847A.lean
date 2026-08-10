import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk847A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476491654433562, 362476599704390321⟩, ⟨731939357912069460, 738118840358895440⟩, true⟩

def state01 : KState := ⟨⟨362481891580487263, 362481999656750468⟩, ⟨274607216136544638, 280788926873982708⟩, true⟩

def words00 : List Nat := [371285314148084239, 371285314151332831, 371285314242182134, 371285314350850610, 371285314435757693, 371285314438700656, 371285314361729693, 371285314343826530, 371285314361847607, 371285314364894418]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 84700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 84700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362485198092709429, 362485306195781978⟩, ⟨(-5502342956518628), 681638938689338⟩, true⟩

def words01 : List Nat := [371285314327984959, 371285314246649245, 371285314218817477, 371285314225847607, 371285314274288370, 371285314323828586, 371285314372390397, 371285314375332643, 371285314237975913, 371285314241567374]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 84710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 84700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478341639124104, 362478449768445424⟩, ⟨575401960962888838, 581588166787860582⟩, true⟩

def words02 : List Nat := [371285314265002211, 371285314267964519, 371285314166620180, 371285314067066775, 371285313966416947, 371285313908135575, 371285313780579006, 371285313785149994, 371285313787349831, 371285313785520697]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 84720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 84700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362499249783176813, 362499357939053595⟩, ⟨(-1196253912141156822), (-1190065456138421074)⟩, true⟩

def words03 : List Nat := [371285313764718695, 371285313826424041, 371285313958380335, 371285313961337247, 371285313960398123, 371285313925694270, 371285313991014466, 371285314040686588, 371285314208411758, 371285314377422998]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 84730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 84700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485838529518034, 362485946711980860⟩, ⟨(-59718851221543387), (-53528142184259665)⟩, true⟩

def words04 : List Nat := [371285314537148237, 371285314582173023, 371285314752368239, 371285314924169774, 371285315105647052, 371285315108590354, 371285315104628599, 371285315088053995, 371285315108120935, 371285315118935536]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 84740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 84700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk847A
