import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk539

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

def state06 : KState := ⟨⟨360615587125025496, 360615605504852666⟩, ⟨(-1819585969311262118), (-1818915867159001848)⟩, true⟩

def words05 : List Nat := [360581896059242368, 360581896105761588, 360581896412646659, 360581896489713585, 360581896490415264, 360581896241092429, 360581895999532771, 360581896282262102, 360581896907575290, 360581897533036744]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 53950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 53900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588734664394075, 360588753051362973⟩, ⟨(-370710752465048618), (-370040264909676340)⟩, true⟩

def words06 : List Nat := [360581897986528901, 360581898097268032, 360581898097887109, 360581898058387972, 360581898018684531, 360581897824997534, 360581897612778152, 360581897228873006, 360581896844839178, 360581896771788578]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 53960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 53900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360525161793875327, 360525180187896663⟩, ⟨3060748703608292737, 3061419571819296739⟩, true⟩

def words07 : List Nat := [360581897107255924, 360581897442853991, 360581897602692610, 360581897603441907, 360581897420552605, 360581897018889538, 360581896617032446, 360581896036755829, 360581895197992276, 360581894148100800]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 53970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 53900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360546397098529305, 360546415499622208⟩, ⟨1914379364156912419, 1915050614126677895⟩, true⟩

def words08 : List Nat := [360581893098079356, 360581892207917573, 360581891489318519, 360581890966574016, 360581890443777727, 360581889596819923, 360581888407224770, 360581887560337514, 360581886713259247, 360581885968489159]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 53980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 53900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360555942603672119, 360555961011919055⟩, ⟨1398941435275861479, 1399613071526456799⟩, true⟩

def words09 : List Nat := [360581885312204726, 360581884389688621, 360581883467061147, 360581882887050979, 360581882479473340, 360581881985902861, 360581881492269129, 360581880782008013, 360581880251624293, 360581879772502879]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 53990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 53900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 53900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk539
