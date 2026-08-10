import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk977A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk977B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk977A

def state06 : KState := ⟨⟨360581705200043872, 360581768424747567⟩, ⟨59458275091766094, 63631804445636834⟩, true⟩

def words05 : List Nat := [360582419889084977, 360582419836605074, 360582419804092440, 360582419805512849, 360582419766541577, 360582419635756872, 360582419504710556, 360582419390161239, 360582419328091847, 360582419322910882]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 97750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 97700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360571913708306126, 360571976946538118⟩, ⟨1016698801478727384, 1020873653427523308⟩, true⟩

def words06 : List Nat := [360582419317517555, 360582419259852123, 360582419218717814, 360582419234919665, 360582419236107753, 360582419225721790, 360582419110887125, 360582418918208527, 360582418725272004, 360582418530392343]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 97760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 97700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564143743317077, 360564206994921825⟩, ⟨1776472615699565003, 1780648775170688141⟩, true⟩

def words07 : List Nat := [360582418424743665, 360582418423916755, 360582418422942885, 360582418347189331, 360582418267227924, 360582418161087090, 360582418054489051, 360582418052700720, 360582417946470016, 360582417761695917]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 97770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 97700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593923971030740, 360593987236059058⟩, ⟨(-1135645917936223074), (-1131468445844054358)⟩, true⟩

def words08 : List Nat := [360582417576603402, 360582417479607907, 360582417445954499, 360582417387579716, 360582417329105001, 360582417173769031, 360582416987106707, 360582416905384021, 360582416844473815, 360582416964297403]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 97780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 97700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360581537672390402, 360581600950930996⟩, ⟨75686269426022697, 79865062951049427⟩, true⟩

def words09 : List Nat := [360582417016563221, 360582417068982439, 360582417167120089, 360582417318142096, 360582417442338507, 360582417566766274, 360582417610515496, 360582417611935917, 360582417573844235, 360582417567116590]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 97790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 97700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 97700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk977B
