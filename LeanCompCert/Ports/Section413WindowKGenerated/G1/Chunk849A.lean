import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk849A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489844147095883, 362489952727835082⟩, ⟨(-399677967447057997), (-393453474562554983)⟩, true⟩

def state01 : KState := ⟨⟨362484918340030214, 362485026947055229⟩, ⟨18547008628392111, 24773733316718983⟩, true⟩

def words00 : List Nat := [371285318634533255, 371285318637482490, 371285318621513465, 371285318585372204, 371285318551159171, 371285318554441071, 371285318573024962, 371285318650073156, 371285318708561820, 371285318711668546]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 84900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 84900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362493860547142287, 362493969180857269⟩, ⟨(-740790360704485253), (-734561369641068195)⟩, true⟩

def words01 : List Nat := [371285318776973131, 371285318847280581, 371285319054581696, 371285319078006665, 371285319080320497, 371285319058166104, 371285319067390100, 371285319070640931, 371285319137813063, 371285319243036930]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 84910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 84900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479525347211325, 362479634007532345⟩, ⟨476600403678582331, 482831654261692203⟩, true⟩

def words02 : List Nat := [371285319347052827, 371285319350002775, 371285319309119528, 371285319352805312, 371285319426972505, 371285319429922502, 371285319319451603, 371285319209991228, 371285319099300506, 371285319061744776]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 84920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 84900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362468771109088331, 362468879795950541⟩, ⟨1390011420420012708, 1396244925285290460⟩, true⟩

def words03 : List Nat := [371285318996857211, 371285318950209488, 371285318902605188, 371285318855922423, 371285318623627851, 371285318435280831, 371285318245381749, 371285318180787783, 371285318000377679, 371285317810140385]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 84930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 84900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474472069327042, 362474580782602814⟩, ⟨905794065926587683, 912029814493479671⟩, true⟩

def words04 : List Nat := [371285317618620619, 371285317516069928, 371285317377070320, 371285317367496179, 371285317357004472, 371285317311441454, 371285317080253774, 371285316989017235, 371285316896294419, 371285316860466187]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 84940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 84900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk849A
