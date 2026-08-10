import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk644A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk644B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk644A

def state06 : KState := ⟨⟨362519601874070907, 362519663142040761⟩, ⟨(-2203172305247176701), (-2200504820432343935)⟩, true⟩

def words05 : List Nat := [371285522904170875, 371285523121392250, 371285523578285403, 371285523853738757, 371285524091738602, 371285524330474922, 371285524767013050, 371285525084130568, 371285525615218986, 371285526147262022]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 64450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 64400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362498428433627795, 362498489721400941⟩, ⟨(-838278756768691917), (-835609995333980669)⟩, true⟩

def words06 : List Nat := [371285526677746618, 371285526915252115, 371285527251656960, 371285527589198689, 371285527998641504, 371285528088090243, 371285528166020020, 371285528244639851, 371285528496654453, 371285528700238962]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 64460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 64400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475797763195757, 362475859070727541⟩, ⟨620891596456897469, 623561631830237643⟩, true⟩

def words07 : List Nat := [371285529026203134, 371285529353058852, 371285529678439715, 371285529683822420, 371285529760548461, 371285529838357611, 371285529984504658, 371285529986698403, 371285529839039897, 371285529691568581]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 64470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 64400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495441457004875, 362495502784158522⟩, ⟨(-645801436495132249), (-643130135801518541)⟩, true⟩

def words08 : List Nat := [371285529545309348, 371285529547742858, 371285529626375065, 371285529787604472, 371285529906386283, 371285529908584876, 371285529846567913, 371285529916573889, 371285530225897515, 371285530382803271]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 64480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 64400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496860760250367, 362496922107402526⟩, ⟨(-737390942438856678), (-734718351941622102)⟩, true⟩

def words09 : List Nat := [371285530482438570, 371285530582765249, 371285530719503286, 371285530736989593, 371285530826527886, 371285530916934472, 371285531005957679, 371285531008196242, 371285531122504905, 371285531301803518]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 64490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 64400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 64400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk644B
