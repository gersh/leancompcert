import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk912A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk912B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk912A

def state06 : KState := ⟨⟨362489312185020929, 362489438343986718⟩, ⟨(-403201037675184394), (-395427528073547104)⟩, true⟩

def words05 : List Nat := [371285104532511775, 371285104580758896, 371285104747679119, 371285104862540423, 371285105012962849, 371285105164665691, 371285105312223410, 371285105315411380, 371285105362498022, 371285105413950081]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 91250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 91200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482335878206052, 362482462065549455⟩, ⟨233510138101992253, 241286237589975937⟩, true⟩

def words06 : List Nat := [371285105571182958, 371285105574370806, 371285105571838702, 371285105562342341, 371285105575407242, 371285105578984503, 371285105614574833, 371285105665445165, 371285105715558559, 371285105718859305]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 91260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 91200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362492157434525033, 362492283650776822⟩, ⟨(-662968874358152874), (-655190136258779882)⟩, true⟩

def words07 : List Nat := [371285105770855049, 371285105853496051, 371285105938476902, 371285105941666419, 371285105889156219, 371285105818476026, 371285105772167725, 371285105775738985, 371285105841037825, 371285105923360835]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 91270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 91200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480920092995543, 362481046337976708⟩, ⟨362816917936691100, 370598278602430040⟩, true⟩

def words08 : List Nat := [371285106004264656, 371285106007453309, 371285105966752621, 371285106009056835, 371285106086667634, 371285106089871724, 371285106052481594, 371285105989966551, 371285105926142078, 371285105909436917]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 91280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 91200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482478856480607, 362482605130163664⟩, ⟨220561150497671118, 228345131503408744⟩, true⟩

def words09 : List Nat := [371285105942555980, 371285106021414296, 371285106099107461, 371285106102352385, 371285106083361906, 371285106090610559, 371285106216000667, 371285106219190090, 371285106195941760, 371285106172129748]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 91290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 91200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 91200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk912B
