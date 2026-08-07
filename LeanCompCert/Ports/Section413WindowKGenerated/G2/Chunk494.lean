import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk494

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360567510632730633, 360567525926940670⟩, ⟨707976170691806700, 708486696800993770⟩, true⟩

def state01 : KState := ⟨⟨360577954243415708, 360577969544113564⟩, ⟨191813255602587229, 192324102241135609⟩, true⟩

def words00 : List Nat := [360581867473209963, 360581866872452794, 360581866140493143, 360581865727531156, 360581865314404788, 360581864698703158, 360581864096374304, 360581863246975390, 360581862397480426, 360581861956626034]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 49400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 49400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360549800205681971, 360549815512804784⟩, ⟨1583163342213834976, 1583674506341330682⟩, true⟩

def words01 : List Nat := [360581862207983172, 360581862538238207, 360581862541484881, 360581862542166680, 360581862308230379, 360581861973130102, 360581861710267844, 360581861710949163, 360581861375142967, 360581860727421161]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 49410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 49400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360573761710314235, 360573777023863241⟩, ⟨398876451211142088, 399387932953992800⟩, true⟩

def words02 : List Nat := [360581860079559185, 360581859738242882, 360581859603383689, 360581859531256428, 360581859459079656, 360581859045786034, 360581858514865515, 360581857838296212, 360581857161547653, 360581856893030832]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 49420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 49400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585025591942361, 360585040911980890⟩, ⟨(-157912674949713618), (-157400872397827400)⟩, true⟩

def words03 : List Nat := [360581856730180325, 360581856363354074, 360581856036921524, 360581856462319437, 360581856786347190, 360581857110474887, 360581857228369518, 360581857229052531, 360581857236600241, 360581857301770785]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 49430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 49400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576607682137290, 360576623008600704⟩, ⟨258184121497448104, 258696241726677320⟩, true⟩

def words04 : List Nat := [360581857347423274, 360581857348105015, 360581857137295301, 360581856722669820, 360581856307954494, 360581855561174221, 360581855103016796, 360581854974423798, 360581854845749910, 360581854479616411]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 49440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 49400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360606620690474054, 360606636023370312⟩, ⟨(-1226153687493349879), (-1225641249128035447)⟩, true⟩

def words05 : List Nat := [360581854676239937, 360581854978845622, 360581855421532877, 360581855575663070, 360581855576308463, 360581855330913802, 360581855085395123, 360581855067198566, 360581855568780056, 360581856070495764]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 49450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 49400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360584704290981079, 360584719630378514⟩, ⟨(-142084186573661041), (-141571426628019249)⟩, true⟩

def words06 : List Nat := [360581856368324340, 360581856679063778, 360581857397105633, 360581858115326025, 360581858605626325, 360581858688184597, 360581858688796134, 360581858460128481, 360581858231349260, 360581857925003082]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 49460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 49400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360586861013408179, 360586876359229293⟩, ⟨(-248790839858561894), (-248277762101913480)⟩, true⟩

def words07 : List Nat := [360581858266358882, 360581858607831468, 360581858681443082, 360581858682125800, 360581858545152101, 360581858298344139, 360581858211041677, 360581858516768817, 360581858618787926, 360581858720901412]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 49470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 49400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360599159690165672, 360599175042430435⟩, ⟨(-857346324013193180), (-856832927392635824)⟩, true⟩

def words08 : List Nat := [360581859230059659, 360581859943268110, 360581860647773537, 360581861352371750, 360581861704746447, 360581861757560319, 360581861758113684, 360581861753020333, 360581861787975828, 360581862138520783]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 49480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 49400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583862279747083, 360583877638514555⟩, ⟨(-100207600813891543), (-99693882343494037)⟩, true⟩

def words09 : List Nat := [360581862216550923, 360581862294643155, 360581862631091301, 360581863186657910, 360581863544575130, 360581863902589052, 360581863944244934, 360581863944927393, 360581863619897979, 360581863661375841]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 49490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 49400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 49400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk494
