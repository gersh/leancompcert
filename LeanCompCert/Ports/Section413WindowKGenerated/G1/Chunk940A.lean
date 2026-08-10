import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk940A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362481151553688965, 362481285708853522⟩, ⟨355285074046226103, 363799330564311507⟩, true⟩

def state01 : KState := ⟨⟨362490603935065142, 362490738119711360⟩, ⟨(-533315577194885136), (-524798549246798202)⟩, true⟩

def words00 : List Nat := [371285155892148593, 371285155895776153, 371285155858174501, 371285155849777628, 371285155840408652, 371285155813092876, 371285155683447837, 371285155668740129, 371285155746813371, 371285155809670548]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 94000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 94000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490469118837023, 362490603333431499⟩, ⟨(-520627824065504459), (-512107980528671903)⟩, true⟩

def words01 : List Nat := [371285155871258393, 371285155933935497, 371285156081177912, 371285156173900493, 371285156299694734, 371285156426813210, 371285156509624568, 371285156512919596, 371285156531042950, 371285156593016819]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 94010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 94000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484985698713356, 362485119942618096⟩, ⟨(-5026627364848720), 3495972075364326⟩, true⟩

def words02 : List Nat := [371285156753024522, 371285156779561811, 371285156804689974, 371285156831003362, 371285156890332620, 371285156894521869, 371285156968763551, 371285157044332967, 371285157118535972, 371285157121944645]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 94020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 94000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491812278605805, 362491946552328980⟩, ⟨(-646975557776099231), (-638450154355973973)⟩, true⟩

def words03 : List Nat := [371285157146011306, 371285157172218917, 371285157309769458, 371285157313062048, 371285157300195305, 371285157270627488, 371285157308682475, 371285157340230535, 371285157414673426, 371285157490596800]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 94030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 94000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486098558815737, 362486232862281742⟩, ⟨(-109665301028298736), (-101137100445480898)⟩, true⟩

def words04 : List Nat := [371285157561684530, 371285157564993258, 371285157588517988, 371285157653340315, 371285157721783102, 371285157725076922, 371285157657458726, 371285157570223335, 371285157503847197, 371285157519112127]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 94040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 94000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk940A
