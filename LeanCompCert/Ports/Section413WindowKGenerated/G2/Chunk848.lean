import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk848

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360596713919390203, 360596760970152425⟩, ⟨(-1215913196808236111), (-1213218697376486827)⟩, true⟩

def state01 : KState := ⟨⟨360586750086262709, 360586797148612694⟩, ⟨(-371052155515653025), (-368356673384541333)⟩, true⟩

def words00 : List Nat := [360582454395706279, 360582454396924541, 360582454448617375, 360582454530906779, 360582454531944064, 360582454519627747, 360582454368251861, 360582454143239539, 360582453917999091, 360582453883312385]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 84800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 84800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360563510357562154, 360563557431397615⟩, ⟨1600098207010641513, 1602794663282819211⟩, true⟩

def words01 : List Nat := [360582454074426745, 360582454265797270, 360582454361195226, 360582454362413614, 360582454318825626, 360582454240551013, 360582454187585449, 360582454188803883, 360582454076681069, 360582453855157139]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 84810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 84800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360600447803695823, 360600494889031218⟩, ⟨(-1533163539353342270), (-1530466107601744532)⟩, true⟩

def words02 : List Nat := [360582453633368778, 360582453429782271, 360582453311173342, 360582453307780627, 360582453304309781, 360582453181918368, 360582453140176190, 360582453189586899, 360582453321013991, 360582453534955447]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 84820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 84800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360592502121831002, 360592549218788731⟩, ⟨(-859120879525656782), (-856422461794962934)⟩, true⟩

def words03 : List Nat := [360582453679035695, 360582453823253850, 360582453963642083, 360582454174545744, 360582454307944264, 360582454441536068, 360582454505336636, 360582454537505386, 360582454657475725, 360582454777872253]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 84830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 84800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360572646937735072, 360572694046157832⟩, ⟨825496712916417765, 828196103398197653⟩, true⟩

def words04 : List Nat := [360582454978423523, 360582455087614882, 360582455090283584, 360582455093067627, 360582455094087603, 360582455061202382, 360582455062209716, 360582454982874381, 360582454903407930, 360582454754506662]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 84840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 84800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360610530479147296, 360610577599073347⟩, ⟨(-2389173462627436741), (-2386473096034158905)⟩, true⟩

def words05 : List Nat := [360582454640463367, 360582454528584983, 360582454416338961, 360582454503556905, 360582454504681067, 360582454490014920, 360582454597981316, 360582454791984636, 360582455124372379, 360582455457028896]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 84850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 84800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360599934387406296, 360599981518971619⟩, ⟨(-1490063396916826699), (-1487362042559091583)⟩, true⟩

def words06 : List Nat := [360582455682526201, 360582455799831434, 360582456030726861, 360582456261984929, 360582456401994261, 360582456403436800, 360582456404522866, 360582456336399903, 360582456337377198, 360582456545275550]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 84860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 84800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360577958267718426, 360578005410757918⟩, ⟨375205780423196664, 377908108651765004⟩, true⟩

def words07 : List Nat := [360582456891459245, 360582457237868575, 360582457499536480, 360582457622593038, 360582457636551142, 360582457650822254, 360582457705999690, 360582457724150634, 360582457725247012, 360582457674054947]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 84870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 84800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581908354299561, 360581955508866726⟩, ⟨39947511693044485, 42650818446645923⟩, true⟩

def words08 : List Nat := [360582457622590195, 360582457729140062, 360582457917013376, 360582458105115169, 360582458174990126, 360582458176209521, 360582458107251551, 360582458060285601, 360582458012966005, 360582457933397845]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 84880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 84800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360591737224146678, 360591784390321423⟩, ⟨(-794518398854350181), (-791814106675078663)⟩, true⟩

def words09 : List Nat := [360582457928565742, 360582457854308934, 360582457779818933, 360582457830539211, 360582457856135402, 360582457881951319, 360582457883047938, 360582457845737463, 360582457956576647, 360582458067820215]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 84890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 84800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 84800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk848
