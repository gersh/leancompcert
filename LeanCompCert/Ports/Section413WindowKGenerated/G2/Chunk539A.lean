import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk539A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360615057917363068, 360615076254689026⟩, ⟨(-1788086288046856059), (-1787418477979975129)⟩, true⟩

def state01 : KState := ⟨⟨360571097831381235, 360571116175829330⟩, ⟨581469093314377166, 582137287300076492⟩, true⟩

def words00 : List Nat := [360581915538972168, 360581915617274977, 360581915847626667, 360581916078187975, 360581916221903074, 360581916222651395, 360581916022796643, 360581915507516768, 360581914992113694, 360581914493160068]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 53900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 53900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360533960635997213, 360533978987489129⟩, ⟨2583720587255662181, 2584389161009808465⟩, true⟩

def words01 : List Nat := [360581914293473755, 360581913915251666, 360581913536960840, 360581912986520795, 360581912445607774, 360581911733875055, 360581911021949304, 360581910653581611, 360581909941684047, 360581909053531596]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 53910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 53900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360578834517846787, 360578852876418353⟩, ⟨163869193737135331, 164538149259581383⟩, true⟩

def words02 : List Nat := [360581908165253081, 360581907269147458, 360581906669409146, 360581906413155658, 360581906156848338, 360581905607047324, 360581904835404806, 360581904407307806, 360581903978985155, 360581903834127598]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 53920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 53900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360560201454892385, 360560219820587312⟩, ⟨1168813058877015204, 1169482398596886568⟩, true⟩

def words03 : List Nat := [360581903778222981, 360581903550279000, 360581903322204095, 360581903176472597, 360581903177111054, 360581902903039072, 360581902628904826, 360581902137807639, 360581901393335534, 360581900992233528]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 53930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 53900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360565841180074903, 360565859552835379⟩, ⟨864513338291967217, 865183059161819001⟩, true⟩

def words04 : List Nat := [360581900590899578, 360581900136917744, 360581899692272955, 360581899075746816, 360581898459116308, 360581897756297290, 360581897272300801, 360581897041075147, 360581896809787996, 360581896310187777]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 53940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 53900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk539A
