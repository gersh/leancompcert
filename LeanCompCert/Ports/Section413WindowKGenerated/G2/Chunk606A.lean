import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk606A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360569578272667014, 360569601671182998⟩, ⟨772421383902646679, 773379301206915753⟩, true⟩

def state01 : KState := ⟨⟨360586492073564712, 360586515480075245⟩, ⟨(-252706798384207840), (-251748396573283432)⟩, true⟩

def words00 : List Nat := [360582363557562105, 360582363558410606, 360582363416695461, 360582363138278129, 360582362859734900, 360582362342183837, 360582362068150451, 360582362066425819, 360582362064608587, 360582361970042854]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 60600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 60600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360601548867491378, 360601572282013126⟩, ⟨(-1165403454502096863), (-1164444567090235887)⟩, true⟩

def words01 : List Nat := [360582362311371815, 360582362652938576, 360582362985492348, 360582363046910934, 360582363047701335, 360582362877583388, 360582362808424876, 360582363046244605, 360582363363813395, 360582363681576145]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 60610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 60600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585983602485504, 360586007025084393⟩, ⟨(-221854748688152630), (-220895371600258194)⟩, true⟩

def words02 : List Nat := [360582363786187721, 360582363799690783, 360582364085047093, 360582364370651776, 360582364552113209, 360582364552961974, 360582364463320546, 360582364166463288, 360582363869453403, 360582363750660415]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 60620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 60600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578483215715556, 360578506646305973⟩, ⟨233059450667216706, 234019312320960784⟩, true⟩

def words03 : List Nat := [360582364083388065, 360582364416277475, 360582364613133525, 360582364894666590, 360582365069194081, 360582365243941529, 360582365690349055, 360582365865834598, 360582365866593746, 360582365803831055]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 60630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 60600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360588962851425810, 360588986290042548⟩, ⟨(-402568237305129041), (-401607888895519167)⟩, true⟩

def words04 : List Nat := [360582365740889892, 360582365733737107, 360582365734428446, 360582365734607682, 360582365734724330, 360582365499278328, 360582364992660844, 360582364758151451, 360582364559749583, 360582364669807177]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 60640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 60600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk606A
