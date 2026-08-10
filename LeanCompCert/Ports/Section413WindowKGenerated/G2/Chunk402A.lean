import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk402A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360624937484923094, 360624947443166163⟩, ⟨(-1699747595102070212), (-1699477029543333772)⟩, true⟩

def state01 : KState := ⟨⟨360580837049384626, 360580847012764206⟩, ⟨73197547983877669, 73468320056454549⟩, true⟩

def words00 : List Nat := [360582673983055301, 360582674403578363, 360582674509234451, 360582674614941768, 360582674615402117, 360582674127244835, 360582674138210400, 360582674328547019, 360582674329034630, 360582674128408485]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 40200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 40200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360621025580911447, 360621035549428831⟩, ⟨(-1543018146514055491), (-1542747167824186853)⟩, true⟩

def words01 : List Nat := [360582674492588995, 360582674902352438, 360582675929108214, 360582676340515146, 360582676341026210, 360582676165394318, 360582676281447346, 360582676882921758, 360582677837083906, 360582678791321768]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 40210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 40200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360589798835838934, 360589808809561074⟩, ⟨(-286975043797641628), (-286703855748067368)⟩, true⟩

def words02 : List Nat := [360582679361374435, 360582680340881579, 360582681296793065, 360582682252815329, 360582683050525096, 360582683233233194, 360582683233722906, 360582682897009856, 360582682560216931, 360582682368365279]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 40220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 40200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360577538936247231, 360577548915102608⟩, ⟨206352400391736381, 206623794977300079⟩, true⟩

def words03 : List Nat := [360582683162527146, 360582683956754064, 360582684441732262, 360582684442277497, 360582684312337186, 360582683841515533, 360582683515596444, 360582683827811279, 360582683828302903, 360582683701260096]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 40230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 40200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360614958772033981, 360614968756044910⟩, ⟨(-1299596589153294267), (-1299324987083371639)⟩, true⟩

def words04 : List Nat := [360582684062848701, 360582684938590933, 360582685798603876, 360582686658670844, 360582686991901123, 360582686992446544, 360582686905484679, 360582687100629773, 360582687389330466, 360582688191907787]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 40240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 40200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk402A
