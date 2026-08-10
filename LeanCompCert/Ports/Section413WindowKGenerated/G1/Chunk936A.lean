import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk936A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489301474269960, 362489434446407019⟩, ⟨(-408996737053729349), (-400593448843328903)⟩, true⟩

def state01 : KState := ⟨⟨362492901750823250, 362493034752117775⟩, ⟨(-745996910369434069), (-737590892866827671)⟩, true⟩

def words00 : List Nat := [371285154809730475, 371285154856095047, 371285154892154798, 371285154929351893, 371285154989349870, 371285154993783830, 371285155111015907, 371285155229609225, 371285155345930268, 371285155433524161]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 93600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 93600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362498102169559172, 362498235200467598⟩, ⟨(-1232863783989357088), (-1224454994179881588)⟩, true⟩

def words01 : List Nat := [371285155553524377, 371285155675150667, 371285155848097146, 371285155869957349, 371285155876014656, 371285155883135748, 371285155993877125, 371285156065411208, 371285156207343529, 371285156350699065]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 93610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 93600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489331820728088, 362489464881152871⟩, ⟨(-411790909342376407), (-403379356059686735)⟩, true⟩

def words02 : List Nat := [371285156472655133, 371285156475932378, 371285156517127514, 371285156592659322, 371285156670492052, 371285156673785160, 371285156646710514, 371285156611289710, 371285156649750820, 371285156699502994]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 93620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 93600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480705502917594, 362480838592952076⟩, ⟨395981771050119320, 404396096829956132⟩, true⟩

def words03 : List Nat := [371285156852643952, 371285157007259364, 371285157145744639, 371285157149022146, 371285157144671570, 371285157157983098, 371285157283690960, 371285157286968553, 371285157260912816, 371285157218505579]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 93630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 93600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488838747981761, 362488971867325369⟩, ⟨(-365643266546996344), (-357226196106459924)⟩, true⟩

def words04 : List Nat := [371285157212822422, 371285157216434786, 371285157239317044, 371285157282107683, 371285157304658590, 371285157307993610, 371285157249157574, 371285157266895076, 371285157382389091, 371285157426517407]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 93640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 93600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk936A
