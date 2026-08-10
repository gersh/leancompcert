import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk984A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571409428534579, 360571473516171846⟩, ⟨1074262394523695857, 1078520560676287471⟩, true⟩

def state01 : KState := ⟨⟨360578675862120513, 360578739963219835⟩, ⟨359146704748986567, 363406195634844109⟩, true⟩

def words00 : List Nat := [360582433980746638, 360582433916173265, 360582433748489013, 360582433529227994, 360582433309738005, 360582433064484045, 360582432918800148, 360582432876584191, 360582432834213071, 360582432740332272]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 98400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 98400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360579591111332673, 360579655225941346⟩, ⟨269038716805362172, 273299537211299208⟩, true⟩

def words01 : List Nat := [360582432769623601, 360582432836857935, 360582432859300810, 360582432860730510, 360582432780387664, 360582432612415583, 360582432444182474, 360582432252796576, 360582432122562886, 360582432095858145]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 98410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 98400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360565261516943123, 360565325645166016⟩, ⟨1679308287226693475, 1683570447610193605⟩, true⟩

def words02 : List Nat := [360582432068917970, 360582431983735260, 360582431795356986, 360582431610490644, 360582431425236479, 360582431192090776, 360582430902748848, 360582430529544716, 360582430156064357, 360582429886226772]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 98420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 98400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360560621092355890, 360560685234040841⟩, ⟨2136154039560233905, 2140417525081743335⟩, true⟩

def words03 : List Nat := [360582429713613838, 360582429626986977, 360582429540217730, 360582429401906726, 360582429289027132, 360582429150361610, 360582429011271327, 360582428956750185, 360582428825291364, 360582428605892546]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 98430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 98400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360567568104884334, 360567632260091729⟩, ⟨1452235728460126142, 1456500545198605640⟩, true⟩

def words04 : List Nat := [360582428386192472, 360582428138323332, 360582427941981965, 360582427849039473, 360582427755987667, 360582427575424744, 360582427291718512, 360582427043566257, 360582426794977016, 360582426577462970]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 98440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 98400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk984A
