import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk821A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360608215667574959, 360608259659276702⟩, ⟨(-2132003119651673260), (-2129563922400639312)⟩, true⟩

def state01 : KState := ⟨⟨360590228751708901, 360590272754635370⟩, ⟨(-655334480201181442), (-652894361347102520)⟩, true⟩

def words00 : List Nat := [360582321558656222, 360582321653437630, 360582321705148607, 360582321757195431, 360582321771729176, 360582321772906019, 360582321683497887, 360582321519955810, 360582321356187074, 360582321391707783]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 82100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 82100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360560356773754230, 360560400787750097⟩, ⟨1797658311116354857, 1800099338935675611⟩, true⟩

def words01 : List Nat := [360582321608345329, 360582321825203062, 360582321954688077, 360582321955864894, 360582321937319519, 360582321822748255, 360582321707838723, 360582321589172102, 360582321405863874, 360582321140148243]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 82110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 82100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586839532479743, 360586883557583872⟩, ⟨(-377274244399529878), (-374832304315500988)⟩, true⟩

def words02 : List Nat := [360582320874176788, 360582320652823274, 360582320505473981, 360582320445764388, 360582320385955625, 360582320200737320, 360582319992571995, 360582319834918381, 360582319676921634, 360582319722925637]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 82120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 82100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590124443782737, 360590168480114762⟩, ⟨(-647128953085972228), (-644686090800815756)⟩, true⟩

def words03 : List Nat := [360582319723992667, 360582319666892185, 360582319620798271, 360582319726516061, 360582319794747583, 360582319863169482, 360582319864227772, 360582319809431431, 360582319853365686, 360582319950259991]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 82130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 82100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585112902314196, 360585156949727258⟩, ⟨(-235456756714434258), (-233012984177006602)⟩, true⟩

def words04 : List Nat := [360582320194878599, 360582320337462550, 360582320405377264, 360582320473412072, 360582320474414534, 360582320480529871, 360582320517674225, 360582320555046473, 360582320556095597, 360582320551093316]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 82140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 82100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk821A
